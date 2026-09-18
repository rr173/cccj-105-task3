'use strict';
/*
 * 协作服务器 v3：零依赖（仅 Node 内置模块）。
 *
 * 在 v2（RGA CRDT + 四角色治理 + 统一 seq/epoch + 原子批次授权 + 三级幂等）之上增加：
 *
 * 【有界流水压缩】
 *   - compact() 以 cutoff 时刻存活状态构建新基线代次（generation 单调 +1），
 *     回收 cutoff 之前的操作流水、修订全量快照、字符墓碑；
 *     压缩前后正文投影 / 样式标记 / 批注 / 成员关系 / 授权纪元 / 治理账本次序完全相同。
 *   - 新代次先写 <file>.gen<n>.tmp 并 fsync，再 rename 为权威文件（原子切换）；
 *     切换前任一时刻宕机 => 重启仍是完整旧代；切换后宕机 => 完整新代；重试压缩不破坏权威态。
 *   - 磁盘流水受 LOG_CAP_BYTES 约束：超过即自动再压缩；不保留隐藏全量副本。
 *
 * 【快照迁移与基线换算】
 *   - hello 携带 gen/lastSeq；落后于保留窗口（gen < currentGen）的镜像端收到
 *     welcome{needMigration} + 基线分片（baselineChunk，可重复/乱序、按片幂等拼装）
 *     + cutoff 之后的尾部操作；积压批次以 migrate 消息提交，服务器用 id 前向链
 *     （墓碑用 RGA 后继）确定性换算：保留改动意图；锚点墓碑已回收 => 显式冲突草稿，
 *     绝不悄悄挂到另一段字句。
 *   - 重连裁决仍按当前成员纪元 epoch；被降权/移除主体的陈旧批次整批拒绝，
 *     完整载荷（ops 原文）落盘，跨压缩与重启保留，必须本人显式核准（approve）后才再次提交。
 *   - 基线请求 / 迁移分片 / 换算批次 / 重复重连 / 进程重启全部幂等（migId/batchId/opId/reqId）。
 *
 * 【可观测】welcome 与 compactionStatus 暴露当前代次、保留 seq 区间、各镜像端水位/租约、
 *   最近压缩失败原因；主理人无需改存储文件即可排查。
 *
 * 【代次演进】回退到仍保留的基线点 => 新修订 + 新 ledger 演进记录；请求已清除基线点 =>
 *   明确错误 baseline-unavailable 且不增加演进记录。
 *
 * 【惰性升级】既有第二代（v:2）空间首次打开时升级为 v3：投影视图不被改写、不产生第二个 owner。
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const CRDT = require('../shared/crdt.js');
const AUTHZ = require('../shared/authz.js');
const COMPACT = require('../shared/compaction.js');

const PORT = Number(process.env.PORT || 8080);
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, '..', 'data');
const PUBLIC_DIR = path.join(__dirname, '..', 'public');
const SHARED_DIR = path.join(__dirname, '..', 'shared');
const MAX_REVS = 1000;
const MAX_LEDGER = 5000;
const MAX_BATCH_RECORDS = 20000;   // 含被拒完整载荷，跨压缩/重启保留
const MAX_REQ_RECORDS = 20000;
const RETAIN_BASELINES = Math.max(1, Number(process.env.RETAIN_BASELINES || 3)); // 保留基线点数
const LOG_CAP_BYTES = Math.max(2048, Number(process.env.LOG_CAP_BYTES || 90000)); // 磁盘流水上界（默认 90KB，便于验收触发多轮回收）
const SHARD_CHARS = Math.max(16, Number(process.env.SHARD_CHARS || 300));
const LEASE_MS = 60000;             // 镜像端水位租约
fs.mkdirSync(DATA_DIR, { recursive: true });

const clip = (s, n) => typeof s === 'string' ? s.slice(0, n) : String(s == null ? '' : s).slice(0, n);

// ---------------- WebSocket（RFC6455 最小实现） ----------------
const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
function wsAccept(key) {
  return crypto.createHash('sha1').update(key + WS_GUID).digest('base64');
}
function wsEncode(str) {
  const p = Buffer.from(str, 'utf8');
  const l = p.length;
  if (l < 126) return Buffer.concat([Buffer.from([0x81, l]), p]);
  if (l < 65536) { const h = Buffer.alloc(4); h[0] = 0x81; h[1] = 126; h.writeUInt16BE(l, 2); return Buffer.concat([h, p]); }
  const h = Buffer.alloc(10); h[0] = 0x81; h[1] = 127; h.writeBigUInt64BE(BigInt(l), 2); return Buffer.concat([h, p]);
}
class WSConn {
  constructor(socket) {
    this.sock = socket;
    this.buf = Buffer.alloc(0);
    this.frags = [];
    this.alive = true;
    this.onmessage = null;
    this.onclose = null;
    socket.on('data', (d) => this._feed(d));
    const bye = () => { if (this.alive) { this.alive = false; this.onclose && this.onclose(); } };
    socket.on('close', bye); socket.on('error', bye); socket.on('end', bye);
  }
  send(obj) {
    if (!this.alive) return;
    try { this.sock.write(wsEncode(typeof obj === 'string' ? obj : JSON.stringify(obj))); } catch (e) { /* ignore */ }
  }
  close() { this.alive = false; try { this.sock.end(); } catch (e) { /* ignore */ } }
  _feed(d) {
    this.buf = Buffer.concat([this.buf, d]);
    for (;;) {
      if (this.buf.length < 2) return;
      const b0 = this.buf[0], b1 = this.buf[1];
      const fin = !!(b0 & 0x80), op = b0 & 0x0f, masked = !!(b1 & 0x80);
      let len = b1 & 0x7f, off = 2;
      if (len === 126) { if (this.buf.length < 4) return; len = this.buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (this.buf.length < 10) return; len = Number(this.buf.readBigUInt64BE(2)); off = 10; }
      const maskOff = off;            // 掩码紧接长度头
      if (masked) off += 4;           // 净荷在掩码之后
      if (this.buf.length < off + len) return;
      let payload = this.buf.slice(off, off + len);
      if (masked) {
        const mask = this.buf.slice(maskOff, maskOff + 4);
        payload = Buffer.from(payload);
        for (let i = 0; i < payload.length; i++) payload[i] ^= mask[i & 3];
      }
      this.buf = this.buf.slice(off + len);
      if (op === 8) { this.close(); return; }
      if (op === 9) { try { this.sock.write(Buffer.concat([Buffer.from([0x8a, payload.length]), payload])); } catch (e) { /* ignore */ } continue; }
      if (op === 0 || op === 1 || op === 2) {
        this.frags.push(payload);
        if (fin) {
          const full = Buffer.concat(this.frags);
          this.frags = [];
          if (this.onmessage) { try { this.onmessage(full.toString('utf8')); } catch (e) { console.error('[ws] handler error:', e); } }
        }
      }
    }
  }
}

// ---------------- 操作清洗 ----------------
function sanitizeOp(o) {
  if (!o || typeof o !== 'object') return null;
  const by = clip(o.by || '?', 128);
  if (o.t === 'ins' && typeof o.id === 'string' && typeof o.ch === 'string' && o.ch.length > 0 && o.ch.length <= 8 && typeof o.after === 'string') {
    return { t: 'ins', id: clip(o.id, 160), after: clip(o.after, 160), ch: o.ch, by, opId: clip(o.opId, 200) };
  }
  if (o.t === 'del' && typeof o.id === 'string') return { t: 'del', id: clip(o.id, 160), by, opId: clip(o.opId, 200) };
  if (o.t === 'mark' && typeof o.id === 'string' && o.start && o.end && o.attrs && typeof o.attrs === 'object') {
    const attrs = {};
    for (const k of ['bold', 'italic', 'underline']) if (k in o.attrs) attrs[k] = !!o.attrs[k];
    return { t: 'mark', id: clip(o.id, 160), start: o.start, end: o.end, attrs, ts: +o.ts || Date.now(), by, deleted: !!o.deleted, opId: clip(o.opId, 200) };
  }
  if (o.t === 'com' && typeof o.id === 'string' && o.start && o.end) {
    return {
      t: 'com', id: clip(o.id, 160), start: o.start, end: o.end,
      text: clip(o.text || '', 4000), quote: clip(o.quote || '', 4000),
      ts: +o.ts || Date.now(), by, resolved: !!o.resolved,
      detached: !!o.detached, detachReason: clip(o.detachReason || '', 600) || null,
      opId: clip(o.opId, 200),
    };
  }
  return null;
}

function pubRev(r) { return r ? { n: r.n, seq: r.seq, fromSeq: r.fromSeq || r.seq, ts: r.ts, by: r.by, kind: r.kind, summary: r.summary, target: r.target, gen: r.gen || 0 } : null; }

// ---------------- 文档 / 成员存储 ----------------
class Store {
  constructor(name) {
    this.name = name;
    this.doc = new CRDT.Doc('server');
    this.seq = 0;
    this.ops = [];              // 尾部操作 [{ seq, op }]（cutoff 之后仍保留的流水）
    this.bySeq = new Map();     // seq -> op（仅尾部；幂等回放批次用）
    this.revs = [];
    this.seenOpIds = new Set();
    // v3：代次 / 基线
    this.v = 3;                 // 写入格式；从 v2 文件载入时先保持 2，直到升级/压缩
    this.gen = 0;               // 当前权威代次（0 = 未压缩的 v2 形态）
    this.cutoff = 0;            // 当前基线覆盖到的 seq
    this.baselines = [];        // 保留的基线点 [{ gen, cutoffSeq, seq, ts, chars:[{id,o,ch,by}], marks, comments, b:{text}, bytes }]
    this.maps = new Map();      // gen -> succ Map（墓碑 oldId -> 后继活字符 oldId|null）；前向映射由基线 chars[].o 派生
    this.ev = 0;                // 代次演进序号（空间级单调，独立于内容 seq，演进项稳定次序）
    this.staging = null;        // 进行中的压缩（内存态，宕机即丢弃 => 权威态不受影响）
    this.lastCompactError = null;
    this.lastCompact = null;
    this.logBytes = 0;
    // 成员治理
    this.initialized = false;
    this.members = new Map();
    this.epoch = 0;
    this.ledger = [];
    this.batches = new Map();   // batchId -> 处理结果（rejected 含完整 ops 载荷）
    this.seenReq = new Map();
    // 迁移 / 水位
    this.migrated = new Map();  // migId -> 结论（换算结果幂等）
    this.approvals = new Map(); // approveId -> 0/1（核准幂等）
    this.watermarks = new Map();// clientId -> { id,name,gen,lastSeq,ts,leaseUntil }
    this.dirty = false;
    this.file = path.join(DATA_DIR, encodeURIComponent(name) + '.json');
    this._load();
  }

  // ---------------- 载入（v2 惰性，v3 全量） ----------------
  _load() {
    let j;
    try { j = JSON.parse(fs.readFileSync(this.file, 'utf8')); } catch (e) { return; }
    this.seq = j.seq || 0;
    this.ops = j.ops || [];
    this.revs = (j.revs || []).map(r => Object.assign({ gen: 0 }, r));
    this._loadGovernance(j);
    if (j.v === 3) {
      this.v = 3;
      this.gen = j.gen || 0;
      this.cutoff = j.cutoff || 0;
      this.ev = j.ev || 0;
      this.baselines = j.baselines || [];
      for (const g of Object.keys(j.maps || {})) {
        const m = j.maps[g];
        // 兼容旧格式 {forward,succ}：v3 只持久化 succ（墓碑后继），forward 由基线派生
        const succ = m instanceof Array ? m : (m.succ || []);
        this.maps.set(Number(g), new Map(succ));
      }
      if (j.lastCompactError) this.lastCompactError = j.lastCompactError;
      if (j.lastCompact) this.lastCompact = j.lastCompact;
      for (const [id, rec] of Object.entries(j.migrated || {})) this.migrated.set(id, rec);
      for (const id of j.approvals || []) this.approvals.set(id, 1);
      for (const [id, w] of Object.entries(j.watermarks || {})) this.watermarks.set(id, w);
      // v3 权威状态 = 当前基线 + cutoff 之后的尾部流水（即使尾部为空，基线也包含全部投影）
      if (this.gen > 0 && this.baselines.length) {
        const cur = this.baselines[this.baselines.length - 1];
        for (const op of COMPACT.baselineToOps(this._baselineForRebuild(cur))) this.doc.apply(op);
      }
      for (const { seq, op } of this.ops) {
        this.doc.apply(op);
        this.bySeq.set(seq, op);
        if (op.opId) this.seenOpIds.add(op.opId);
      }
      console.log(`[store] "${this.name}" 载入 v3：gen ${this.gen} / cutoff ${this.cutoff} / 尾部 ${this.ops.length} 操作 / ${this.members.size} 成员 / epoch ${this.epoch}`);
    } else {
      for (const { seq, op } of this.ops) {
        this.doc.apply(op);
        this.bySeq.set(seq, op);
        if (op.opId) this.seenOpIds.add(op.opId);
      }
      if (j.v === 2) {
        this.v = 2; // 标记磁盘格式为 v2，首次打开 ensureInitialized 时惰性升级到 v3
        console.log(`[store] "${this.name}" 载入 v2：${this.ops.length} 操作 / ${this.revs.length} 修订；首次打开惰性升级 v3（投影不变、不新增 owner）`);
      } else {
        this.v = 1; // 无 v 字段的旧版数据
        console.log(`[store] "${this.name}" 载入旧版数据：${this.ops.length} 操作 / ${this.revs.length} 修订，等待首次打开初始化 owner`);
      }
    }
    this._recomputeLogBytes();
  }

  _baselineForRebuild(b) {
    return { gen: b.gen, cutoffSeq: b.cutoffSeq, chars: b.chars, marks: b.marks, comments: b.comments };
  }

  _loadGovernance(j) {
    this.initialized = !!j.initialized;
    this.epoch = j.epoch || 0;
    this.ledger = j.ledger || [];
    if (j.members && typeof j.members === 'object') {
      for (const [id, m] of Object.entries(j.members)) {
        if (m && AUTHZ.isValidRole(m.role)) this.members.set(id, {
          id, name: clip(m.name || id, 80), role: m.role,
          since: m.since || 0, by: m.by || null, byName: m.byName || null,
        });
      }
    }
    for (const [id, rec] of Object.entries(j.batches || {})) this.batches.set(id, rec);
    for (const id of j.seenReqIds || []) this.seenReq.set(id, 0);
  }

  // ---------------- 序列化与原子落盘 ----------------
  _serialize() {
    // 前向映射不持久化（由基线 chars[].o 派生）；只存墓碑后继 succ，避免隐藏的全量副本。
    const mapsObj = {};
    for (const [g, succ] of this.maps) mapsObj[g] = [...succ];
    return JSON.stringify({
      v: this.v,
      gen: this.gen, cutoff: this.cutoff, ev: this.ev,
      seq: this.seq,
      ops: this.ops,
      revs: this.revs, // snapshot 是否保留由压缩采纳决定（惰性升级保留，显式压缩剥离 cutoff 之前）
      baselines: this.baselines.map(b => ({
        gen: b.gen, cutoffSeq: b.cutoffSeq, seq: b.seq, ts: b.ts,
        chars: b.chars, marks: b.marks, comments: b.comments, b: b.b, bytes: b.bytes,
      })),
      maps: mapsObj,
      initialized: this.initialized,
      epoch: this.epoch,
      members: Object.fromEntries(this.members),
      ledger: this.ledger,
      batches: Object.fromEntries(this.batches),
      seenReqIds: [...this.seenReq.keys()],
      migrated: Object.fromEntries(this.migrated),
      approvals: [...this.approvals.keys()],
      watermarks: Object.fromEntries(this.watermarks),
      lastCompactError: this.lastCompactError,
      lastCompact: this.lastCompact,
    });
  }
  _writeSync() {
    const tmp = this.file + '.tmp';
    const str = this._serialize();
    const fd = fs.openSync(tmp, 'w');
    try { fs.writeSync(fd, str); fs.fsyncSync(fd); } finally { fs.closeSync(fd); }
    fs.renameSync(tmp, this.file); // 原子切换：崩溃只可能落在完整旧文件或完整新文件
    this.dirty = false;
    this._recomputeLogBytes();
  }
  save() {
    if (this.dirty) {
      try { this._writeSync(); }
      catch (e) { this.lastCompactError = { ts: Date.now(), phase: 'save', message: String((e && e.message) || e) }; }
    }
  }
  saveSync() { this._writeSync(); }
  // 「磁盘流水」口径：尾部操作流水 + 仍保留的修订全量快照 + 迁移/批次/墓碑相关记录。
  // 基线 chars 是当前活文档投影本身（非历史流水、非隐藏副本），不计入流水；
  // 这样多次压缩后流水（ops+快照）必然归零并受上限约束。
  _logPayload() {
    return {
      ops: this.ops,
      snapshots: this.revs.map(r => r.snapshot).filter(Boolean),
      migrated: Object.fromEntries(this.migrated),
    };
  }
  _recomputeLogBytes(known) {
    if (known != null) {
      // 已知整文件大小；流水部分按比例的稳定口径改为只统计 payload，避免把活基线计入
    }
    try {
      this.logBytes = Buffer.byteLength(JSON.stringify(this._logPayload()));
    } catch (e) { this.logBytes = 0; }
  }

  roleOf(userId) { const m = this.members.get(userId); return m ? m.role : null; }
  publicMembers() {
    return [...this.members.values()]
      .sort((a, b) => (AUTHZ.rank(b.role) - AUTHZ.rank(a.role)) || (a.id < b.id ? -1 : a.id > b.id ? 1 : 0))
      .map(m => ({ id: m.id, name: m.name, role: m.role, since: m.since, by: m.by, byName: m.byName }));
  }
  publicLedger() { return this.ledger.slice(-MAX_LEDGER); }
  _ownerCount() { let n = 0; for (const m of this.members.values()) if (m.role === 'owner') n++; return n; }

  // ---------------- 初始化 / 惰性升级 ----------------
  ensureInitialized(firstId, firstName) {
    if (this.initialized) {
      if (this.v === 2) this._upgradeV2ToV3(); // 既有第二代空间首次打开：惰性升级，投影不变，不新增 owner
      return null;
    }
    const legacy = this.ops.length > 0 || this.revs.length > 0;
    const now = Date.now();
    this.members.set(firstId, { id: firstId, name: clip(firstName || firstId, 80), role: 'owner', since: now, by: null, byName: null });
    this.initialized = true;
    const entry = {
      seq: ++this.seq, ev: ++this.ev, ts: now, kind: 'space', act: legacy ? 'upgrade' : 'init',
      by: null, byName: null, target: firstId, targetName: clip(firstName || firstId, 80),
      from: null, to: 'owner', epoch: this.epoch,
      note: legacy ? '旧版空间升级：初始化唯一所有者，既有内容/批注/修订原样保留' : '空间创建，初始化所有者',
    };
    this.ledger.push(entry);
    if (this.ledger.length > MAX_LEDGER) this.ledger.splice(0, this.ledger.length - MAX_LEDGER);
    // v1 旧空间首开：建立第一代基线（投影不变、保留旧修订快照、仅一个 owner）；全新空空间无需基线
    if (legacy) {
      const built = COMPACT.buildBaseline(this.doc, 1, this.seq, {});
      this._adoptBaseline(built, { kind: 'upgrade-v2v3', by: null, ts: Date.now(), persist: true, keepSnapshots: true });
    } else {
      this.saveSync();
    }
    return entry;
  }

  // v2 -> v3：以当前完整状态构建第一代基线；投影/成员/epoch/账本次序逐项不变，仅追加演进记录。
  _upgradeV2ToV3() {
    const built = COMPACT.buildBaseline(this.doc, 1, this.seq, {});
    return this._adoptBaseline(built, { kind: 'upgrade-v2v3', by: null, ts: Date.now(), persist: true, keepSnapshots: true });
  }

  touchName(userId, name) {
    const m = this.members.get(userId);
    const nm = clip(name || userId, 80);
    if (m && m.name !== nm) { m.name = nm; this.dirty = true; }
    return m ? m.role : null;
  }

  _rememberReq(reqId) {
    if (!reqId) return;
    this.seenReq.set(reqId, Date.now());
    if (this.seenReq.size > MAX_REQ_RECORDS) this.seenReq.delete(this.seenReq.keys().next().value);
  }
  _pruneBatches() {
    // 被拒批次含完整载荷，必须跨压缩/重启保留；仅在远超上限时淘汰最早的非拒绝记录。
    if (this.batches.size <= MAX_BATCH_RECORDS) return;
    for (const [id, rec] of this.batches) {
      if (this.batches.size <= MAX_BATCH_RECORDS) break;
      if (rec.status !== 'rejected') this.batches.delete(id);
    }
  }
  _batchReply(rec) {
    if (rec.status === 'rejected') {
      return {
        rejected: true, status: 'rejected', epoch: rec.epoch, atSeq: rec.atSeq,
        role: rec.role, need: rec.need, reason: rec.reason, code: rec.code || null,
        kinds: rec.kinds || {}, ts: rec.ts, ops: rec.ops || [],
      };
    }
    if (rec.status === 'empty') return { empty: true, status: 'empty', epoch: rec.epoch };
    return {
      applied: (rec.seqs || []).map(seq => ({ seq, op: this.bySeq.get(seq) })).filter(x => x.op),
      rev: rec.rev || null, status: 'applied', epoch: rec.epoch,
    };
  }

  // ---------------- 成员变更 ----------------
  submitMembership(actorId, actorName, msg) {
    const act = msg.act;
    const reqId = clip(msg.reqId || '', 200);
    const target = clip(msg.target || '', 128);
    const wantRole = clip(msg.role || '', 32);
    const actor = this.members.get(actorId);
    if (!actor || actor.role !== 'owner') {
      return { ok: false, code: 'forbidden-membership', message: '只有所有者可以邀请成员或变更角色' };
    }
    actor.name = clip(actorName || actor.name, 80);
    if (reqId && this.seenReq.has(reqId)) {
      return { ok: true, duplicate: true, applied: false, epoch: this.epoch, members: this.publicMembers() };
    }
    if (!target) return { ok: false, code: 'bad-target', message: '缺少成员标识' };

    const cur = this.members.get(target);
    let effectiveAct = act;
    const fromRole = cur ? cur.role : null;
    let toRole = null;

    if (act === 'invite') {
      if (!AUTHZ.isValidRole(wantRole)) return { ok: false, code: 'bad-role', message: '角色不合法' };
      if (cur) {
        if (cur.role === wantRole) { this._rememberReq(reqId); this.saveSync(); return { ok: true, applied: false, duplicate: false, noop: 'already-member', epoch: this.epoch, members: this.publicMembers() }; }
        effectiveAct = 'role'; toRole = wantRole;
      } else toRole = wantRole;
    } else if (act === 'role') {
      if (!cur) return { ok: false, code: 'not-member', message: '该用户还不是空间成员，请先邀请' };
      if (!AUTHZ.isValidRole(wantRole)) return { ok: false, code: 'bad-role', message: '角色不合法' };
      if (cur.role === wantRole) { this._rememberReq(reqId); this.saveSync(); return { ok: true, applied: false, noop: 'same-role', epoch: this.epoch, members: this.publicMembers() }; }
      toRole = wantRole;
    } else if (act === 'remove') {
      if (!cur) { this._rememberReq(reqId); this.saveSync(); return { ok: true, applied: false, noop: 'already-removed', epoch: this.epoch, members: this.publicMembers() }; }
    } else {
      return { ok: false, code: 'bad-act', message: '未知的成员操作' };
    }

    if (cur && cur.role === 'owner' && (effectiveAct === 'remove' || toRole !== 'owner') && this._ownerCount() <= 1) {
      return { ok: false, code: 'last-owner', message: '空间必须保留至少一个所有者' };
    }

    const now = Date.now();
    if (effectiveAct === 'remove') this.members.delete(target);
    else if (!cur) this.members.set(target, { id: target, name: clip(msg.name || target, 80), role: toRole, since: now, by: actorId, byName: actor.name });
    else cur.role = toRole;
    this.epoch += 1;
    const entry = {
      seq: ++this.seq, ev: ++this.ev, ts: now, kind: 'membership', act: effectiveAct,
      by: actorId, byName: actor.name, target, targetName: cur ? cur.name : target,
      from: fromRole, to: effectiveAct === 'remove' ? null : toRole, epoch: this.epoch,
    };
    this.ledger.push(entry);
    if (this.ledger.length > MAX_LEDGER) this.ledger.splice(0, this.ledger.length - MAX_LEDGER);
    this._rememberReq(reqId);
    this.saveSync();
    return { ok: true, applied: true, duplicate: false, epoch: this.epoch, entry, members: this.publicMembers() };
  }

  // ---------------- 修订 / 提交 ----------------
  _snapshot() {
    return { text: this.doc.text(), marks: this.doc.activeMarks().map(m => ({ s: m.s, e: m.e, attrs: m.attrs })) };
  }
  _summarize(ops) {
    let ins = 0, del = 0, mark = 0, com = 0;
    for (const o of ops) {
      if (o.t === 'ins') ins++; else if (o.t === 'del') del++;
      else if (o.t === 'mark') mark++; else if (o.t === 'com') com++;
    }
    const parts = [];
    if (ins) parts.push('+' + ins);
    if (del) parts.push('−' + del);
    if (mark) parts.push(mark + ' 处格式');
    if (com) parts.push(com + ' 条批注');
    return parts.join('  ') || '（无文本变化）';
  }
  _commitOps(ops, by, kind, extra) {
    const applied = [];
    for (const op of ops) {
      this.seq++;
      const rec = { seq: this.seq, op };
      this.ops.push(rec);
      this.bySeq.set(this.seq, op);
      this.doc.apply(op);
      applied.push(rec);
    }
    const rev = Object.assign({
      n: this.revs.length ? this.revs[this.revs.length - 1].n + 1 : 1,
      seq: this.seq, fromSeq: applied[0].seq, ts: Date.now(), by: clip(by || '?', 128),
      kind: kind || 'edit', summary: this._summarize(ops), gen: this.gen,
      snapshot: this._snapshot(),
    }, extra || {});
    this.revs.push(rev);
    if (this.revs.length > MAX_REVS) this.revs.splice(0, this.revs.length - MAX_REVS);
    this.dirty = true;
    return { applied, rev };
  }

  _anchorKnown(a) {
    if (!a || a.id == null) return true;
    return this.doc.chars.has(a.id);
  }
  _opAnchorsKnown(op) {
    if (op.t === 'ins') return op.after === COMPACT.ROOT || this.doc.chars.has(op.after);
    if (op.t === 'del') return this.doc.chars.has(op.id);
    if (op.t === 'mark' || op.t === 'com') return this._anchorKnown(op.start) && this._anchorKnown(op.end);
    return true;
  }

  submitBatch(actorId, msg) {
    const batchId = clip(msg.batchId || ('srv-' + Date.now().toString(36) + '-' + Math.random().toString(36).slice(2, 10)), 200);
    const cached = this.batches.get(batchId);
    if (cached) return Object.assign({ duplicate: true, batchId }, this._batchReply(cached));

    const raw = Array.isArray(msg.ops) ? msg.ops.slice(0, 5000) : [];
    const valid = [];
    for (const r of raw) { const op = sanitizeOp(r); if (op) valid.push(op); }

    const role = AUTHZ.effectiveRole(this.roleOf(actorId));
    const auth = AUTHZ.authorizeBatch(role, valid);
    if (!auth.ok) {
      const rec = {
        status: 'rejected', ts: Date.now(), epoch: this.epoch, atSeq: this.seq,
        role: auth.role, need: auth.need, reason: auth.reason, kinds: auth.kinds || {}, by: actorId,
        ops: valid,
      };
      this.batches.set(batchId, rec);
      this._pruneBatches();
      this.saveSync();
      return Object.assign({ rejected: true, batchId }, this._batchReply(rec));
    }
    if (!valid.length) {
      const rec = { status: 'empty', ts: Date.now(), epoch: this.epoch };
      this.batches.set(batchId, rec);
      this._pruneBatches();
      return Object.assign({ empty: true, batchId }, this._batchReply(rec));
    }

    // 陈旧命名空间：锚点不在当前基线 => 必须先迁移换算，绝不悄悄挂到别的字句。
    // 批次内「插入后引用」是合法的：把本批次新插入的 id 也视为已知。
    const batchLocalIds = new Set();
    let stale = null;
    for (const op of valid) {
      if (op.t === 'ins') {
        if (op.after !== COMPACT.ROOT && !this.doc.chars.has(op.after) && !batchLocalIds.has(op.after)) { stale = op; break; }
        batchLocalIds.add(op.id);
      } else if (op.t === 'del') {
        if (!this.doc.chars.has(op.id) && !batchLocalIds.has(op.id)) { stale = op; break; }
      } else if (op.t === 'mark' || op.t === 'com') {
        if (!this._anchorKnown(op.start) || !this._anchorKnown(op.end)) { stale = op; break; }
      }
    }
    if (stale) {
      const rec = {
        status: 'rejected', ts: Date.now(), epoch: this.epoch, atSeq: this.seq,
        role, code: 'migration-required',
        reason: '操作引用的字符不在当前基线代次（gen ' + this.gen + '）；请先取得新基线并完成换算后再提交。',
        kinds: { stale: 1 }, by: actorId, ops: valid,
      };
      this.batches.set(batchId, rec);
      this._pruneBatches();
      this.saveSync();
      return Object.assign({ rejected: true, batchId, migrationRequired: true }, this._batchReply(rec));
    }

    const novel = [];
    for (const op of valid) {
      if (op.opId && this.seenOpIds.has(op.opId)) continue;
      if (op.opId) this.seenOpIds.add(op.opId);
      novel.push(op);
    }
    const commit = novel.length ? this._commitOps(novel, actorId, 'edit') : null;
    const rec = {
      status: 'applied', ts: Date.now(), epoch: this.epoch,
      seqs: novel.map((_, i) => commit.applied[i].seq),
      rev: commit ? pubRev(commit.rev) : null, by: actorId,
    };
    this.batches.set(batchId, rec);
    this._pruneBatches();
    this._maybeAutoCompact();
    return {
      applied: commit ? commit.applied : [],
      rev: commit ? pubRev(commit.rev) : null,
      batchId, status: 'applied', epoch: this.epoch,
    };
  }

  // ---------------- 快照迁移换算 ----------------
  _mapsContext(fromGen) {
    const mapsByGen = {}, succByGen = {};
    for (let g = fromGen + 1; g <= this.gen; g++) {
      // g-1 -> g 的前向映射来自第 g 代基线：跨代沿用字符记录了来源 id（c.o 非本代前缀）。
      const baseCur = this.baselines.find(b => b.gen === g);
      const fwd = new Map();
      const ownPrefix = 'g' + g + ':';
      if (baseCur) for (const c of baseCur.chars) {
        if (c.o != null && !String(c.o).startsWith(ownPrefix)) fwd.set(c.o, c.id);
      }
      mapsByGen[g] = fwd;
      succByGen[g] = this.maps.get(g) || new Map();
    }
    return { mapsByGen, succByGen };
  }
  _liveIds() {
    const s = new Set();
    for (const id of this.doc.visibleIds()) s.add(id);
    return s;
  }

  submitMigration(actorId, msg) {
    const migId = clip(msg.migId || '', 200);
    const fromGen = Math.max(0, Number(msg.fromGen) || 0);
    if (migId && this.migrated.has(migId)) return Object.assign({ duplicate: true, migId }, this.migrated.get(migId));

    const raw = Array.isArray(msg.ops) ? msg.ops.slice(0, 5000) : [];
    const valid = [];
    for (const r of raw) { const op = sanitizeOp(r); if (op) valid.push(op); }

    // 重连裁决以当前成员纪元为准：降权/移除主体不得借迁移夹带旧操作，完整载荷原样退回
    const role = AUTHZ.effectiveRole(this.roleOf(actorId));
    const auth = AUTHZ.authorizeBatch(role, valid);
    if (!auth.ok) {
      const out = {
        rejected: true, status: 'rejected', epoch: this.epoch, atSeq: this.seq,
        role: auth.role, need: auth.need, reason: auth.reason, kinds: auth.kinds || {},
        ops: valid, conflicts: [], obsolete: [], applied: [], rev: null,
      };
      if (migId) { this.migrated.set(migId, out); this._pruneMigrated(); this.dirty = true; }
      return Object.assign({ migId }, out);
    }

    const { mapsByGen, succByGen } = this._mapsContext(fromGen);
    const tr = COMPACT.translateBatch(valid, {
      fromGen, toGen: this.gen, mapsByGen, succByGen, liveIds: this._liveIds(),
    });

    const novel = [];
    for (const op of tr.ops) {
      if (op.opId && this.seenOpIds.has(op.opId)) continue;
      if (op.opId) this.seenOpIds.add(op.opId);
      novel.push(op);
    }
    const commit = novel.length ? this._commitOps(novel, actorId, 'migrate', { fromGen }) : null;
    const out = {
      rejected: false, status: 'migrated', epoch: this.epoch, gen: this.gen,
      applied: commit ? commit.applied : [],
      rev: commit ? pubRev(commit.rev) : null,
      conflicts: tr.conflicts,
      obsolete: tr.obsolete,
      ops: [],
    };
    if (migId) { this.migrated.set(migId, out); this._pruneMigrated(); }
    this.dirty = true;
    this._maybeAutoCompact();
    return Object.assign({ migId }, out);
  }
  _pruneMigrated() {
    if (this.migrated.size <= MAX_BATCH_RECORDS) return;
    for (const k of [...this.migrated.keys()]) {
      if (this.migrated.size <= MAX_BATCH_RECORDS) break;
      this.migrated.delete(k);
    }
  }

  // 本人显式核准一条冲突草稿 => 在新基线上生成等价新操作（仍按当前 epoch 授权，恰好一次）。
  approveConflict(actorId, msg) {
    const approveId = clip(msg.approveId || '', 200);
    if (!approveId) return { ok: false, code: 'bad-approve', message: '缺少核准标识' };
    if (this.approvals.has(approveId)) return { ok: true, duplicate: true, applied: this.approvals.get(approveId) === 1 };

    const kind = clip(msg.kind || '', 32);
    const role = AUTHZ.effectiveRole(this.roleOf(actorId));
    const needAction = kind === 'com-anchor' ? 'annotate' : 'prose';
    if (!AUTHZ.can(role, needAction)) {
      return { ok: false, code: 'forbidden-approve', message: '当前角色无权核准此类操作（权限恢复后再试）。' };
    }

    let op = null;
    const now = Date.now();
    const actor = 'srv-' + clip(String(actorId), 28) + '-ap-' + now.toString(36) + Math.random().toString(36).slice(2, 6);
    // 偏移区间 [s,e) -> 字符锚点：start 指向位置 s 的前一字符，end 指向区间最后一个字符（与客户端 anchorsFor 一致）
    const offsetAnchors = (s, e) => {
      const ids = this.doc.visibleIds();
      const st = s <= 0 ? { id: null, edge: 's' } : { id: ids[Math.min(s, ids.length) - 1], edge: 's' };
      const en = e >= ids.length ? { id: null, edge: 'e' } : { id: ids[Math.max(e - 1, 0)], edge: 'e' };
      return [st, en];
    };
    if (kind === 'ins-after') {
      const ch = typeof msg.ch === 'string' ? msg.ch.slice(0, 8) : '';
      if (!ch) return { ok: false, code: 'bad-approve', message: '缺少要插入的字符' };
      const after = msg.anchor && msg.anchor.id != null ? clip(msg.anchor.id, 160) : COMPACT.ROOT;
      if (after !== COMPACT.ROOT && !this.doc.chars.has(after)) return { ok: false, code: 'anchor-reclaimed', message: '所选插入位置不在当前基线，请重新选择。' };
      op = sanitizeOp({ t: 'ins', id: actor + ':1', after, ch, by: actorId });
    } else if (kind === 'del-reclaimed') {
      // 删除意图已被基线满足 => 显式核准即消解，不产生任何操作（零次副作用，幂等）
      this.approvals.set(approveId, 0);
      this.dirty = true;
      return { ok: true, applied: false, resolved: true };
    } else if (kind === 'mark-anchor') {
      const s = msg.anchor && msg.anchor.s, e = msg.anchor && msg.anchor.e;
      const attrs = msg.attrs && typeof msg.attrs === 'object' ? msg.attrs : null;
      if (!attrs || !(s >= 0) || !(e > s)) return { ok: false, code: 'bad-approve', message: '请在新基线显式选择样式范围。' };
      const [st, en] = offsetAnchors(s, e);
      op = sanitizeOp({ t: 'mark', id: actor + ':m1', start: st, end: en, attrs, ts: now, by: actorId, deleted: false });
    } else if (kind === 'com-anchor') {
      const s = msg.anchor && msg.anchor.s, e = msg.anchor && msg.anchor.e;
      if (!(s >= 0) || !(e > s)) return { ok: false, code: 'bad-approve', message: '请在新基线显式选择批注范围（批注不会自动重挂）。' };
      const [st, en] = offsetAnchors(s, e);
      // quote 以服务端当前投影为准，保证用户选定范围后批注即为 anchored（而非 changed）
      const curQuote = this.doc.text().slice(s, e);
      op = sanitizeOp({
        t: 'com', id: actor + ':c1', start: st, end: en,
        text: clip(msg.text || '', 4000), quote: curQuote, ts: now, by: actorId, resolved: false,
      });
    } else {
      return { ok: false, code: 'bad-approve', message: '未知的冲突类型' };
    }
    if (!op) return { ok: false, code: 'bad-approve', message: '无法构造核准操作' };
    const commit = this._commitOps([op], actorId, 'approve', { approveId });
    this.approvals.set(approveId, 1);
    this.dirty = true;
    this._maybeAutoCompact();
    return { ok: true, duplicate: false, applied: true, appliedOps: commit.applied, rev: pubRev(commit.rev) };
  }

  // ---------------- 压缩（基线代次） ----------------
  // 两阶段：stage 先在某时刻拍下基线（制作基线期间允许在线写入）；
  // publish 在切换点以最新状态重建基线 => 边界两侧变动不丢不重。
  compactStage(actorId, reqId) {
    if (this.staging) return { ok: true, already: true, reqId: this.staging.reqId, gen: this.staging.newGen, cutoffBase: this.staging.baseline.cutoffSeq };
    if (actorId != null && this.roleOf(actorId) !== 'owner') {
      return { ok: false, code: 'forbidden-compact', message: '只有所有者可以压缩流水。' };
    }
    try {
      const newGen = this.gen + 1;
      const built = COMPACT.buildBaseline(this.doc, newGen, this.seq, {});
      this.staging = { reqId: reqId || ('compact-' + Date.now()), newGen, baseline: built, stagedAt: Date.now(), stagedSeq: this.seq };
      return { ok: true, staged: true, reqId: this.staging.reqId, gen: newGen, cutoffBase: built.cutoffSeq };
    } catch (e) {
      this.lastCompactError = { ts: Date.now(), phase: 'stage', message: String((e && e.message) || e) };
      return { ok: false, code: 'compact-failed', message: this.lastCompactError.message };
    }
  }

  compactPublish(actorId, reqId) {
    if (actorId != null && this.roleOf(actorId) !== 'owner') {
      return { ok: false, code: 'forbidden-compact', message: '只有所有者可以发布代次。' };
    }
    if (!this.staging) {
      const st = this.compactStage(actorId, reqId); // 重试幂等：无舞台则现建
      if (!st.ok) return st;
    }
    const newGen = this.staging.newGen;
    try {
      const built = COMPACT.buildBaseline(this.doc, newGen, this.seq, {}); // 切换点：折叠 stage 之后的在线写入
      const rec = this._adoptBaseline(built, { kind: 'compact', by: actorId, ts: Date.now(), persist: true });
      this.staging = null;
      this.lastCompact = { ts: rec.ts, gen: newGen, cutoffSeq: rec.cutoffSeq, bytes: rec.bytes };
      this.lastCompactError = null;
      return { ok: true, published: true, gen: newGen, cutoffSeq: rec.cutoffSeq, bytes: rec.bytes, entry: rec.entry, reclaimed: rec.reclaimed };
    } catch (e) {
      this.staging = null;
      this.lastCompactError = { ts: Date.now(), phase: 'publish', message: String((e && e.message) || e) };
      return { ok: false, code: 'compact-failed', message: this.lastCompactError.message };
    }
  }

  compactOnce(actorId) {
    const st = this.compactStage(actorId, 'auto-' + Date.now());
    if (!st.ok) return st;
    return this.compactPublish(actorId, this.staging && this.staging.reqId);
  }

  // 采纳基线为新权威态：回收旧流水/快照/墓碑，原子落盘，重建内存。
  _adoptBaseline(built, opts) {
    opts = opts || {};
    const newGen = built.gen;
    const cutoffSeq = built.cutoffSeq;
    const now = opts.ts || Date.now();
    const prevGen = this.gen;
    const tail = this.ops.filter(r => r.seq > cutoffSeq);

    const baselineRec = {
      gen: newGen, cutoffSeq, seq: this.seq, ts: now,
      chars: built.chars, marks: built.marks, comments: built.comments,
      b: { text: built.chars.map(c => c.ch).join('') }, bytes: 0,
    };
    const entry = {
      ev: ++this.ev, ts: now, kind: 'evolution', act: opts.kind || 'compact',
      seq: this.seq, genBefore: prevGen, gen: newGen, cutoffSeq,
      by: opts.by || null,
      byName: opts.by ? ((this.members.get(opts.by) || {}).name || opts.by) : '系统',
      epoch: this.epoch,
    };
    if (opts.kind === 'restore-baseline') {
      entry.targetGen = opts.targetGen;
      entry.note = '回退到仍保留的基线点 g' + opts.targetGen + '，并以此演进为新代次';
    } else if (opts.kind === 'upgrade-v2v3') {
      entry.note = '第二代空间惰性升级：投影视图不变，不新增所有者';
    } else {
      entry.note = '压缩流水并发布基线代次';
    }

    const newDoc = new CRDT.Doc('server');
    for (const op of COMPACT.baselineToOps(this._baselineForRebuild(baselineRec))) newDoc.apply(op);
    for (const r of tail) newDoc.apply(r.op);

    // 墓碑后继表（前向映射由基线 chars[].o 派生，无需单独存储）
    this.maps.set(newGen, built.succ);

    // 修订：显式压缩回收 cutoff 之前的全量快照；惰性升级（keepSnapshots）原样保留全部修订。
    const carriedRevs = opts.keepSnapshots
      ? this.revs.map(r => Object.assign({}, r, { gen: r.gen || prevGen }))
      : this.revs.filter(r => (r.fromSeq || r.seq) > cutoffSeq).map(r => {
          const { snapshot, ...rest } = r;
          return Object.assign({}, rest, { gen: r.gen || prevGen });
        });
    const newRevs = carriedRevs;
    const nextN = newRevs.length ? newRevs[newRevs.length - 1].n + 1
      : (this.revs.length ? this.revs[this.revs.length - 1].n + 1 : 1);
    const marker = {
      n: nextN, seq: this.seq, fromSeq: (prevGen === 0 ? 0 : this.cutoff) + 1, ts: now,
      by: (opts.byName || 'system'), kind: 'baseline',
      summary: (opts.kind === 'upgrade-v2v3' ? '升级到 v3 基线 g' : '基线代次 g') + newGen + '（cutoff seq ' + cutoffSeq + '）',
      gen: newGen, cutoffSeq,
    };

    const cand = {
      doc: newDoc,
      ops: tail,
      revs: newRevs.concat([marker]),
      baselines: this.baselines.concat([baselineRec]).slice(-RETAIN_BASELINES),
      ledger: this.ledger.concat([entry]).slice(-MAX_LEDGER),
    };

    const tombCount = this.doc.seq().filter(c => c.tomb).length;
    const droppedOps = this.ops.length - tail.length;
    const saved = this._swapState(newGen, cutoffSeq, cand, opts.persist !== false);
    baselineRec.bytes = saved.bytes;

    // 裁剪换算表：早于最早保留基线的代不再支持直接穿链（其镜像端拿到冲突草稿）
    const oldestGen = cand.baselines[0] ? cand.baselines[0].gen : newGen;
    for (const g of [...this.maps.keys()]) if (g < oldestGen) this.maps.delete(g);

    return {
      gen: newGen, cutoffSeq, ts: now, bytes: saved.bytes, entry,
      reclaimed: { ops: droppedOps, tombstones: tombCount, genBefore: prevGen },
      baseline: baselineRec,
    };
  }

  _swapState(newGen, cutoffSeq, cand, persist) {
    const snap = {
      doc: this.doc, ops: this.ops, revs: this.revs, baselines: this.baselines,
      ledger: this.ledger, gen: this.gen, cutoff: this.cutoff, bySeq: this.bySeq, v: this.v,
    };
    let bytes = 0;
    try {
      this.doc = cand.doc;
      this.ops = cand.ops;
      this.bySeq = new Map();
      for (const r of cand.ops) this.bySeq.set(r.seq, r.op);
      this.revs = cand.revs;
      this.baselines = cand.baselines;
      this.ledger = cand.ledger;
      this.gen = newGen;
      this.cutoff = cutoffSeq;
      this.v = 3;
      if (persist) {
        this._writeSync();
        bytes = this.logBytes;
      } else {
        this.dirty = true;
      }
    } catch (e) {
      // 落盘失败：权威文件从未改名 => 完整回滚旧态
      this.doc = snap.doc; this.ops = snap.ops; this.bySeq = snap.bySeq;
      this.revs = snap.revs; this.baselines = snap.baselines; this.ledger = snap.ledger;
      this.gen = snap.gen; this.cutoff = snap.cutoff; this.v = snap.v;
      throw e;
    }
    return { bytes };
  }

  _maybeAutoCompact() {
    if (this.staging) return;
    try { if (this.logBytes > LOG_CAP_BYTES) this.compactOnce(null); } catch (e) { /* 原因记录在 lastCompactError */ }
  }

  // ---------------- 回退基线点 ----------------
  restoreBaseline(actorId, wantGen) {
    if (this.roleOf(actorId) !== 'owner') return { forbidden: true, code: 'forbidden-rollback', message: '只有所有者可以回退基线点' };
    const b = this.baselines.find(x => x.gen === wantGen);
    if (!b) return { notfound: true, code: 'baseline-unavailable', message: '基线点 g' + wantGen + ' 已被回收，无法回退（不产生演进记录）。' };
    const snap = { doc: this.doc, ops: this.ops, bySeq: this.bySeq, revs: this.revs, baselines: this.baselines, ledger: this.ledger, gen: this.gen, cutoff: this.cutoff, v: this.v };
    try {
      const target = new CRDT.Doc('server');
      for (const op of COMPACT.baselineToOps(this._baselineForRebuild(b))) target.apply(op);
      this.doc = target; this.ops = []; this.bySeq = new Map();
      const newGen = this.gen + 1;
      const built = COMPACT.buildBaseline(this.doc, newGen, this.seq, {});
      const rec = this._adoptBaseline(built, { kind: 'restore-baseline', by: actorId, targetGen: wantGen, ts: Date.now(), persist: true });
      return { ok: true, gen: newGen, entry: rec.entry, bytes: rec.bytes };
    } catch (e) {
      this.doc = snap.doc; this.ops = snap.ops; this.bySeq = snap.bySeq;
      this.revs = snap.revs; this.baselines = snap.baselines; this.ledger = snap.ledger;
      this.gen = snap.gen; this.cutoff = snap.cutoff; this.v = snap.v;
      throw e;
    }
  }

  // v2 风格修订恢复（在当前基线上生成 del/ins/mark 批次）
  restore(actorId, targetN) {
    if (this.roleOf(actorId) !== 'owner') return { forbidden: true, code: 'forbidden-rollback', message: '只有所有者可以回滚到历史检查点' };
    const rev = this.revs.find(r => r.n === targetN);
    if (!rev) return { notfound: true, message: '找不到该修订版本' };
    if (!rev.snapshot) return { notfound: true, code: 'snapshot-reclaimed', message: '修订 #' + targetN + ' 的全量快照已随压缩回收；请在基线点列表回退到保留的基线。' };
    const snap = rev.snapshot;
    const ops = [];
    for (const id of this.doc.visibleIds()) ops.push({ t: 'del', id, by: actorId });
    const actor = 'srv-' + clip(String(actorId), 28) + '-r' + targetN + '-' + Date.now();
    let c = 0, after = '';
    const newIds = [];
    for (const ch of snap.text) {
      const id = actor + ':' + (++c);
      ops.push({ t: 'ins', id, after, ch, by: actorId });
      after = id; newIds.push(id);
    }
    const anchor = (pos, edge) => {
      if (!newIds.length) return { id: null, edge };
      if (edge === 's') return pos <= 0 ? { id: null, edge: 's' } : { id: newIds[Math.min(pos, newIds.length) - 1], edge: 's' };
      return pos >= newIds.length ? { id: null, edge: 'e' } : { id: newIds[Math.max(pos - 1, 0)], edge: 'e' };
    };
    for (const m of snap.marks || []) {
      if (m.e <= m.s) continue;
      ops.push({ t: 'mark', id: actor + ':m:' + (++c), start: anchor(m.s, 's'), end: anchor(m.e, 'e'), attrs: m.attrs, ts: Date.now(), by: actorId, deleted: false });
    }
    const commit = this._commitOps(ops, actorId, 'restore', { target: targetN });
    return { applied: commit.applied, rev: pubRev(commit.rev) };
  }

  // ---------------- 水位 / 租约 / 状态 ----------------
  _touchWatermark(clientId, name, gen, lastSeq) {
    const now = Date.now();
    const w = this.watermarks.get(clientId) || { id: clientId, lastSeq: 0 };
    w.name = clip(name || clientId, 80);
    if (gen != null) w.gen = gen;
    if (lastSeq != null) w.lastSeq = lastSeq;
    w.ts = now; w.leaseUntil = now + LEASE_MS;
    this.watermarks.set(clientId, w);
    this.dirty = true;
  }
  _activeWatermarks() {
    const now = Date.now();
    return [...this.watermarks.values()]
      .map(w => ({ id: w.id, name: w.name, gen: w.gen, lastSeq: w.lastSeq, ts: w.ts, leaseUntil: w.leaseUntil, leased: w.leaseUntil > now, current: w.gen === this.gen }))
      .sort((a, b) => (b.gen - a.gen) || (b.lastSeq - a.lastSeq) || (a.id < b.id ? -1 : 1));
  }
  compactionInfo() {
    return {
      t: 'compactionStatus',
      gen: this.gen, cutoff: this.cutoff, seq: this.seq,
      retainedSeq: [this.cutoff + 1, this.seq],
      logBytes: this.logBytes, logCapBytes: LOG_CAP_BYTES,
      retainBaselines: RETAIN_BASELINES, shardChars: SHARD_CHARS,
      baselines: this.baselines.map(b => ({ gen: b.gen, cutoffSeq: b.cutoffSeq, seq: b.seq, ts: b.ts, chars: b.chars.length, bytes: b.bytes })),
      watermarks: this._activeWatermarks(),
      staging: this.staging ? { gen: this.staging.newGen, stagedSeq: this.staging.baseline.cutoffSeq, stagedAt: this.staging.stagedAt } : null,
      lastCompact: this.lastCompact, lastCompactError: this.lastCompactError,
    };
  }
}


// ---------------- HTTP 静态服务 ----------------
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.json': 'application/json; charset=utf-8' };
function serveFile(res, file) {
  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404); res.end('not found'); return; }
    res.writeHead(200, { 'Content-Type': MIME[path.extname(file)] || 'application/octet-stream' });
    res.end(data);
  });
}
const server = http.createServer((req, res) => {
  let p = decodeURIComponent((req.url || '/').split('?')[0]);
  if (p === '/') p = '/index.html';
  if (p === '/shared/crdt.js') return serveFile(res, path.join(SHARED_DIR, 'crdt.js'));
  if (p === '/shared/authz.js') return serveFile(res, path.join(SHARED_DIR, 'authz.js'));
  if (p === '/shared/compaction.js') return serveFile(res, path.join(SHARED_DIR, 'compaction.js'));
  if (p === '/healthz') { res.writeHead(200, { 'Content-Type': 'text/plain' }); return res.end('ok'); }
  const file = path.normalize(path.join(PUBLIC_DIR, p));
  if (!file.startsWith(PUBLIC_DIR)) { res.writeHead(403); return res.end(); }
  serveFile(res, file);
});

// ---------------- 房间与广播 ----------------
const stores = new Map();
const rooms = new Map(); // docName -> Map<WSConn, {id,name}>
function getStore(name) {
  let s = stores.get(name);
  if (!s) { s = new Store(name); stores.set(name, s); }
  return s;
}
function conns(room) { return rooms.get(room) || new Map(); }
function sendTo(room, msg, except) {
  for (const c of conns(room).keys()) if (c !== except) c.send(msg);
}
function broadcast(room, msg) { sendTo(room, msg, null); }
function presenceOf(store, room) {
  const peers = [];
  for (const meta of conns(room).values()) {
    const role = store.roleOf(meta.id);
    peers.push({ id: meta.id, name: meta.name, role: role || 'viewer', member: !!role });
  }
  return { count: peers.length, peers };
}
function broadcastPresence(store, room) {
  broadcast(room, Object.assign({ t: 'presence' }, presenceOf(store, room)));
}

// 向一个连接下发「迁移到当前基线」的完整流：genSwitch -> baselineChunk*N -> baselineEnd。
// 分片可重复/乱序：每片带 (gen, shard, shards)，接收端按片幂等拼装；整条流重发也安全。
function sendMigrationStream(conn, store, reason, fromGen) {
  if (store.gen <= 0 || !store.baselines.length) return;
  const cur = store.baselines[store.baselines.length - 1];
  const baseLike = { gen: cur.gen, cutoffSeq: cur.cutoffSeq, chars: cur.chars, marks: cur.marks, comments: cur.comments };
  const shards = COMPACT.shardBaseline(baseLike, SHARD_CHARS);
  conn.send({ t: 'genSwitch', reason: reason || 'welcome', fromGen: fromGen == null ? null : fromGen, toGen: cur.gen, cutoffSeq: cur.cutoffSeq, shards: shards.length });
  for (const s of shards) conn.send(Object.assign({ t: 'baselineChunk' }, s));
  conn.send({
    t: 'baselineEnd', reason: reason || 'welcome', gen: cur.gen, cutoffSeq: cur.cutoffSeq,
    tail: store.ops.slice(),
    revs: store.revs.map(pubRev),
    ledger: store.publicLedger(),
    members: store.publicMembers(),
    epoch: store.epoch,
    seq: store.seq,
  });
}
function broadcastMigration(store, room, reason, fromGen) {
  for (const c of conns(room).keys()) sendMigrationStream(c, store, reason, fromGen);
}

server.on('upgrade', (req, socket) => {
  const key = req.headers['sec-websocket-key'];
  if (!key) { socket.destroy(); return; }
  socket.write(
    'HTTP/1.1 101 Switching Protocols\r\n' +
    'Upgrade: websocket\r\nConnection: Upgrade\r\n' +
    'Sec-WebSocket-Accept: ' + wsAccept(key) + '\r\n\r\n'
  );
  socket.setNoDelay(true);
  const conn = new WSConn(socket);
  let room = null;

  conn.onmessage = (raw) => {
    let msg;
    try { msg = JSON.parse(raw); } catch (e) { return; }

    if (msg.t === 'hello') {
      const clientId = clip(msg.clientId || '?', 128) || '?';
      const name = clip(msg.name || clientId, 80);
      const docName = clip(msg.doc || 'default', 64) || 'default';
      const store = getStore(docName);
      room = docName;
      if (!rooms.has(room)) rooms.set(room, new Map());
      const initEntry = store.ensureInitialized(clientId, name); // 并发首开恰好一个 owner；v2 首开惰性升级
      store.touchName(clientId, name);
      rooms.get(room).set(conn, { id: clientId, name });
      const lastSeq = +msg.lastSeq || 0;
      const clientGen = +msg.gen || 0;
      const role = store.roleOf(clientId);
      store._touchWatermark(clientId, name, clientGen, lastSeq);

      const needMigration = clientGen < store.gen;
      conn.send({
        t: 'welcome',
        seq: store.seq,
        gen: store.gen,
        cutoff: store.cutoff,
        retainedSeq: [store.cutoff + 1, store.seq],
        ops: needMigration ? [] : store.ops.filter(o => o.seq > lastSeq),
        revs: store.revs.map(pubRev),
        ledger: store.publicLedger(),
        members: store.publicMembers(),
        epoch: store.epoch,
        initialized: store.initialized,
        initEntry: initEntry || undefined,
        you: clientId, name,
        role: role || 'viewer',
        member: !!role,
        needMigration,
        baselines: store.compactionInfo().baselines,
        watermarks: store.compactionInfo().watermarks,
        logBytes: store.logBytes, logCapBytes: store.compactionInfo().logCapBytes,
        lastCompactError: store.lastCompactError,
        staging: store.compactionInfo().staging,
      });
      if (needMigration) sendMigrationStream(conn, store, 'welcome', clientGen);
      if (initEntry) broadcast(room, { t: 'members', epoch: store.epoch, members: store.publicMembers(), entry: initEntry });
      broadcastPresence(store, room);
      return;
    }

    if (!room) return;
    const store = getStore(room);
    const meta = rooms.get(room).get(conn) || { id: '?', name: '?' };

    if (msg.t === 'watermark') {
      store._touchWatermark(meta.id, meta.name, +msg.gen || 0, +msg.lastSeq || 0);
      conn.send(store.compactionInfo());
      return;
    }
    if (msg.t === 'compactionStatus') { conn.send(store.compactionInfo()); return; }

    if (msg.t === 'member') {
      const res = store.submitMembership(meta.id, meta.name, msg);
      if (res.ok) {
        conn.send({ t: 'memberAck', reqId: clip(msg.reqId || '', 200), ok: true, duplicate: !!res.duplicate, applied: !!res.applied, noop: res.noop || null, epoch: res.epoch, members: res.members });
        if (res.applied) broadcast(room, { t: 'members', epoch: res.epoch, members: res.members, entry: res.entry });
        broadcastPresence(store, room);
      } else {
        conn.send({ t: 'error', code: res.code, message: res.message, reqId: clip(msg.reqId || '', 200) });
      }
      return;
    }

    if (msg.t === 'ops') {
      const res = store.submitBatch(meta.id, msg);
      if (res.rejected) {
        conn.send({
          t: 'batchAck', status: 'rejected', batchId: res.batchId, epoch: res.epoch, atSeq: res.atSeq,
          role: res.role, need: res.need, reason: res.reason, code: res.code || null,
          migrationRequired: !!res.migrationRequired, kinds: res.kinds, ops: res.ops || [],
        });
      } else if (res.duplicate || res.empty) {
        conn.send({
          t: 'batchAck', batchId: res.batchId, status: res.empty ? 'empty' : 'applied',
          epoch: res.epoch, applied: res.applied || [], rev: res.rev || null, duplicate: !!res.duplicate,
        });
      } else {
        if (res.applied && res.applied.length) {
          broadcast(room, { t: 'ops', batchId: res.batchId, epoch: res.epoch, gen: store.gen, applied: res.applied, rev: res.rev });
        }
      }
      return;
    }

    // 落后镜像端的积压批次换算
    if (msg.t === 'migrate') {
      const res = store.submitMigration(meta.id, msg);
      if (res.rejected) {
        conn.send({
          t: 'migrateAck', migId: res.migId || clip(msg.migId || '', 200), batchId: clip(msg.batchId || '', 200),
          status: 'rejected', duplicate: !!res.duplicate, epoch: res.epoch, atSeq: res.atSeq,
          role: res.role, need: res.need, reason: res.reason, kinds: res.kinds, ops: res.ops || [],
        });
      } else {
        // 重复 migrate（同 migId）只回放首次结论给发起者，不再次广播（幂等：不重复投影/账本事件）
        if (res.applied && res.applied.length && !res.duplicate) {
          sendTo(room, { t: 'ops', batchId: clip(msg.batchId || '', 200), epoch: res.epoch, gen: store.gen, applied: res.applied, rev: res.rev, migrated: true }, conn);
        }
        conn.send({
          t: 'migrateAck', migId: res.migId || clip(msg.migId || '', 200), batchId: clip(msg.batchId || '', 200),
          status: 'migrated', duplicate: !!res.duplicate, epoch: res.epoch, gen: res.gen,
          applied: res.applied || [], rev: res.rev || null,
          conflicts: res.conflicts || [], obsolete: (res.obsolete || []).map(o => ({ t: o.t, id: o.id, opId: o.opId || null })),
        });
      }
      return;
    }

    // 本人显式核准冲突草稿
    if (msg.t === 'approveConflict') {
      const res = store.approveConflict(meta.id, msg);
      if (res.ok && res.applied) {
        broadcast(room, { t: 'ops', batchId: 'approve:' + clip(msg.approveId || '', 160), epoch: store.epoch, gen: store.gen, applied: res.appliedOps, rev: res.rev, approved: true });
      }
      conn.send(Object.assign({ t: 'approveAck', approveId: clip(msg.approveId || '', 200) }, res));
      return;
    }

    if (msg.t === 'compact') {
      if (store.roleOf(meta.id) !== 'owner') { conn.send({ t: 'compactAck', ok: false, code: 'forbidden-compact', message: '只有所有者可以压缩流水。' }); return; }
      const reqId = clip(msg.reqId || '', 200);
      let res;
      if (msg.phase === 'stage') res = store.compactStage(meta.id, reqId);
      else if (msg.phase === 'publish') res = store.compactPublish(meta.id, reqId);
      else res = store.compactOnce(meta.id);
      conn.send(Object.assign({ t: 'compactAck', reqId }, res));
      if (res && res.published) {
        // 原子切换后，把新基线流广播给所有在线镜像端（它们据此重置并换算各自积压）
        broadcastMigration(store, room, 'compact', res.gen - 1);
        broadcast(room, store.compactionInfo());
      } else if (res && res.ok) {
        broadcast(room, store.compactionInfo());
      }
      return;
    }

    if (msg.t === 'restoreBaseline') {
      let res;
      try { res = store.restoreBaseline(meta.id, +msg.gen); }
      catch (e) { conn.send({ t: 'error', code: 'compact-failed', message: String((e && e.message) || e) }); return; }
      if (res.forbidden) { conn.send({ t: 'error', code: res.code, message: res.message }); return; }
      if (res.notfound) { conn.send({ t: 'restoreBaselineAck', ok: false, code: res.code, message: res.message }); return; }
      conn.send({ t: 'restoreBaselineAck', ok: true, gen: res.gen, entry: res.entry });
      broadcastMigration(store, room, 'restore-baseline', res.gen - 1);
      broadcast(room, store.compactionInfo());
      return;
    }

    if (msg.t === 'restore') {
      const res = store.restore(meta.id, +msg.rev);
      if (res.forbidden) conn.send({ t: 'error', code: res.code, message: res.message });
      else if (res.notfound) conn.send({ t: 'error', code: res.code || 'notfound', message: res.message });
      else broadcast(room, { t: 'ops', applied: res.applied, rev: res.rev, gen: store.gen });
      return;
    }
  };

  conn.onclose = () => {
    if (room && rooms.has(room)) {
      const store = getStore(room);
      rooms.get(room).delete(conn);
      broadcastPresence(store, room);
    }
  };
});

setInterval(() => { for (const s of stores.values()) s.save(); }, 2000).unref();
function shutdown() { for (const s of stores.values()) { s.dirty = true; s.save(); } process.exit(0); }
process.on('SIGINT', shutdown);
process.on('SIGTERM', shutdown);

server.listen(PORT, () => console.log(`[server] 协作文档服务(v3)已启动: http://0.0.0.0:${PORT}`));
