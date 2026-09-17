'use strict';
/*
 * 协作服务器：零依赖（仅 Node 内置模块）。
 * - HTTP：托管前端静态文件与共享 CRDT / 授权模块
 * - WebSocket（手写 RFC6455）：接收/广播操作
 * - 每个内容操作分配全局递增 seq => 所有客户端看到一致的修订时间线
 * - 成员治理：owner / editor / commenter / viewer 四角色
 *   · 成员变更进入共享审计账本，审计条目与内容修订共用同一条全局 seq
 *   · epoch 授权纪元 + 整批原子授权；越权整批拒绝、零发布
 *   · reqId / batchId / opId 三级幂等
 * - 有界流水压缩（v3）：
 *   · 长期活跃空间的操作流水达到上界时，在切点构建剪枝基线（不重映射任何字符 id），
 *     回收失去用途的叶子墓碑、窗口外修订快照与操作流水；磁盘占用受 LOG_OP_CAP 约束，
 *     绝不保留隐藏全量副本。新代次只能经 tmp+rename 原子切换成为权威态，
 *     暂存只存在于内存，进程任意时刻被杀 => 重启后只可能是完整旧代或完整新代。
 *   · 落后于保留窗口离线的镜像端：经幂等、分片的快照迁移协议取得新基线，
 *     积压批次走 rebase 换算：引用仍存在则保留意图，引用随墓碑回收则产出显式冲突草稿；
 *     换算仍按当前成员纪元授权，被移除/降权主体不能夹带旧操作。
 *   · 被拒/冲突载荷完整持久化（跨压缩、跨重启），只能由本人显式核准后重提。
 * - 旧版空间（v1/v2）惰性升级：首开时初始化唯一 owner，既有投影不被改写。
 * - JSON 落盘（data/<doc>.json），重启后从基线 + 窗口重放恢复。
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const CRDT = require('../shared/crdt.js');
const AUTHZ = require('../shared/authz.js');

const PORT = Number(process.env.PORT || 8080);
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, '..', 'data');
const PUBLIC_DIR = path.join(__dirname, '..', 'public');
const SHARED_DIR = path.join(__dirname, '..', 'shared');
const MAX_LEDGER = 5000;
const MAX_BATCH_RECORDS = 10000;
const MAX_REQ_RECORDS = 20000;
// 有界流水：保留窗口内操作条数的配置上界（每个空间可被 owner 单独覆盖，见 caps）。
const LOG_OP_CAP = Number(process.env.LOG_OP_CAP || 2000);
// 窗口内最多保留的全量修订快照；更早修订只留元数据（账本时间线不受影响）。
const REV_SNAPSHOT_CAP = Number(process.env.REV_SNAPSHOT_CAP || 50);
// 迁移分片大小（合成操作条数），分片请求幂等，乱序/重复到达均可。
const MIGRATE_CHUNK = Number(process.env.MIGRATE_CHUNK || 300);
// 切点发布延迟：制作基线期间仍允许在线写入，用于验证切点边界不丢不重（毫秒，0=立即）。
const COMPACT_DELAY_MS = Number(process.env.COMPACT_DELAY_MS || 0);
// 水位租约：镜像端超过该毫秒无 hello/watermark 即视为离线（仅展示用，不影响正确性）。
const LEASE_MS = Number(process.env.LEASE_MS || 30000);
fs.mkdirSync(DATA_DIR, { recursive: true });
try { // 上次在原子切换前被杀时，数据目录可能残留 tmp（它们从未成为权威态），启动即清。
  for (const f of fs.readdirSync(DATA_DIR)) if (f.endsWith('.json.tmp')) fs.unlinkSync(path.join(DATA_DIR, f));
} catch (e) { /* ignore */ }

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
      const maskOff = off;
      if (masked) off += 4;
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
    return { t: 'com', id: clip(o.id, 160), start: o.start, end: o.end, text: clip(o.text || '', 4000), quote: clip(o.quote || '', 4000), ts: +o.ts || Date.now(), by, resolved: !!o.resolved, opId: clip(o.opId, 200) };
  }
  return null;
}

function pubRev(r) {
  return r ? {
    n: r.n, seq: r.seq, fromSeq: r.fromSeq || r.seq, ts: r.ts, by: r.by,
    kind: r.kind, summary: r.summary, target: r.target,
    compacted: !!r.compacted, gen: r.gen || 0,
  } : null;
}

// 标准 opId = "actor#counter"（客户端产出）。以每 actor 最大 counter 压缩记账，
// 取代无限增长的 seenOpIds 集合：基线吸收的 opId 同样并入水位。
function parseOpId(opId) {
  if (!opId || typeof opId !== 'string') return null;
  const i = opId.lastIndexOf('#');
  if (i <= 0) return null;
  const c = Number(opId.slice(i + 1));
  if (!Number.isFinite(c)) return null;
  return [opId.slice(0, i), c];
}

// ---------------- 文档 / 成员存储 ----------------
class Store {
  constructor(name) {
    this.name = name;
    this.doc = new CRDT.Doc('server');
    this.seq = 0;
    this.ops = [];              // 保留窗口内的 [{ seq, op }]
    this.bySeq = new Map();     // seq -> op（仅窗口）
    this.revs = [];
    this.opIdMax = new Map();   // actor -> 最大已提交 opId counter
    this.oddOpIds = new Set();  // 非标准 opId 的去重集合
    // 流水压缩（v3）
    this.v = 2;
    this.gen = 0;
    this.baseline = null;       // 当前权威基线 { chars, marks, comments }
    this.logMinSeq = 0;         // 窗口起点（下一条可补发 seq 的下界；基线投影 = seq<=cutSeq）
    this.caps = { logOpCap: LOG_OP_CAP, revSnapshotCap: REV_SNAPSHOT_CAP };
    this.generations = [];      // 代次演进（仅少量元数据，旧基线已物理删除）
    this.staging = null;        // 制作中的代次（只在内存，绝不成隐藏副本落盘）
    this.lastError = null;      // 最近一次压缩失败原因（供主理人排查）
    this.migrateOps = [];       // 当前基线的确定性合成操作（迁移分片用，内存缓存）
    // 成员治理
    this.initialized = false;
    this.members = new Map();
    this.epoch = 0;
    this.ledger = [];
    this.batches = new Map();
    this.seenReq = new Map();
    this.rebaseReqs = new Map(); // reqId -> 首次结论（换算幂等，重启不重算）
    // 完整隔离载荷：被授权拒绝的批次与换算冲突，跨压缩、跨重启保留。
    this.quarantine = new Map(); // key(owner#batchId) -> 完整记录
    // 各镜像端水位回执（仅展示/租约，正确性由 hello/window 保证）
    this.watermarks = new Map(); // userId -> { userId, name, gen, seq, online, lastSeen }
    this.dirty = false;
    this.file = path.join(DATA_DIR, encodeURIComponent(name) + '.json');
    this._load();
  }

  _noteOpId(opId) {
    const p = parseOpId(opId);
    if (p) {
      const [a, c] = p;
      if (c > (this.opIdMax.get(a) || 0)) this.opIdMax.set(a, c);
    } else if (opId) {
      this.oddOpIds.add(opId);
      if (this.oddOpIds.size > MAX_BATCH_RECORDS) this.oddOpIds.delete(this.oddOpIds.keys().next().value);
    }
  }
  _hasOpId(opId) {
    const p = parseOpId(opId);
    if (p) return p[1] <= (this.opIdMax.get(p[0]) || 0);
    return opId ? this.oddOpIds.has(opId) : false;
  }

  _rebuildFromState(baseline, ops) {
    this.doc = new CRDT.Doc('server');
    if (baseline) CRDT.importBaseline(this.doc, baseline);
    for (const { op } of ops) this.doc.apply(op);
  }

  _load() {
    let j;
    try { j = JSON.parse(fs.readFileSync(this.file, 'utf8')); } catch (e) { return; /* 新空间 */ }
    this.seq = j.seq || 0;
    this.epoch = j.epoch || 0;
    this.initialized = !!j.initialized;
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

    if (j.v >= 3) {
      this.v = 3;
      this.gen = j.gen || 0;
      this.baseline = j.baseline || null;
      this.logMinSeq = j.logMinSeq || 0;
      this.caps = Object.assign({ logOpCap: LOG_OP_CAP, revSnapshotCap: REV_SNAPSHOT_CAP }, j.caps || {});
      this.generations = j.generations || [];
      for (const [a, c] of Object.entries(j.opIdMax || {})) this.opIdMax.set(a, c);
      this.ops = j.ops || [];
      this.revs = j.revs || [];
      for (const { seq, op } of this.ops) { this.bySeq.set(seq, op); this._noteOpId(op.opId); }
      this._rebuildFromState(this.baseline, this.ops);
      for (const rec of j.quarantine || []) {
        const key = rec.owner + '#' + rec.batchId;
        this.quarantine.set(key, rec);
      }
      for (const [r, rec] of Object.entries(j.rebaseReqs || {})) this.rebaseReqs.set(r, rec);
      console.log(`[store] "${this.name}" 载入 v3 gen ${this.gen}：基线 ${this.baseline ? this.baseline.chars.length : 0} 字符 / 窗口 ${this.ops.length} 操作 / ${this.members.size} 成员 / epoch ${this.epoch} / 隔离 ${this.quarantine.size}`);
    } else {
      // v1 / v2 惰性升级：内容、批注、修订原样保留（首开时才初始化 owner，见 ensureInitialized）。
      this.v = 3; // 内存态先按 v3 组织；未压缩前 baseline=null、窗口=全部流水，投影不变。
      this.ops = j.ops || [];
      this.revs = j.revs || [];
      for (const { seq, op } of this.ops) {
        this.doc.apply(op); this.bySeq.set(seq, op); this._noteOpId(op.opId);
      }
      if (j.v === 2) {
        for (const id of j.seenOpIds || []) this._noteOpId(id);
      }
      console.log(`[store] "${this.name}" 载入旧版数据（v${j.v || 1}）：${this.ops.length} 操作 / ${this.revs.length} 修订，等待首次打开初始化 owner（惰性升级）`);
    }
  }

  _serialize() {
    return JSON.stringify({
      v: 3,
      seq: this.seq,
      gen: this.gen,
      baseline: this.baseline,
      logMinSeq: this.logMinSeq,
      caps: this.caps,
      generations: this.generations.slice(-50),
      ops: this.ops,
      revs: this.revs,
      opIdMax: Object.fromEntries(this.opIdMax),
      initialized: this.initialized,
      epoch: this.epoch,
      members: Object.fromEntries(this.members),
      ledger: this.ledger,
      batches: Object.fromEntries(this.batches),
      seenReqIds: [...this.seenReq.keys()],
      rebaseReqs: Object.fromEntries(this.rebaseReqs),
      quarantine: [...this.quarantine.values()],
    });
  }
  _writeSync() {
    const tmp = this.file + '.tmp';
    fs.writeFileSync(tmp, this._serialize());
    fs.renameSync(tmp, this.file); // 同一文件系统上原子替换：权威态要么旧要么新
    this.dirty = false;
  }
  save() { if (this.dirty) this._writeSync(); }
  saveSync() { this._writeSync(); }

  roleOf(userId) { const m = this.members.get(userId); return m ? m.role : null; }

  publicMembers() {
    return [...this.members.values()]
      .sort((a, b) => (AUTHZ.rank(b.role) - AUTHZ.rank(a.role)) || (a.id < b.id ? -1 : a.id > b.id ? 1 : 0))
      .map(m => ({ id: m.id, name: m.name, role: m.role, since: m.since, by: m.by, byName: m.byName }));
  }
  publicLedger() { return this.ledger.slice(-MAX_LEDGER); }

  _ownerCount() { let n = 0; for (const m of this.members.values()) if (m.role === 'owner') n++; return n; }

  // 首次打开：新空间或旧版升级。单线程 + 同步落盘 => 并发首开恰好一个 owner。
  ensureInitialized(firstId, firstName) {
    if (this.initialized) return null;
    const legacy = this.ops.length > 0 || this.revs.length > 0 || this.baseline;
    const now = Date.now();
    this.members.set(firstId, { id: firstId, name: clip(firstName || firstId, 80), role: 'owner', since: now, by: null, byName: null });
    this.initialized = true;
    const entry = {
      seq: ++this.seq, ts: now, kind: 'space', act: legacy ? 'upgrade' : 'init',
      by: null, byName: null, target: firstId, targetName: clip(firstName || firstId, 80),
      from: null, to: 'owner', epoch: this.epoch,
      note: legacy ? '旧版空间升级：初始化唯一所有者，既有内容/批注/修订原样保留' : '空间创建，初始化所有者',
    };
    this.ledger.push(entry);
    if (this.ledger.length > MAX_LEDGER) this.ledger.splice(0, this.ledger.length - MAX_LEDGER);
    this.saveSync();
    return entry;
  }

  touchName(userId, name) {
    const m = this.members.get(userId);
    const nm = clip(name || userId, 80);
    if (m && m.name !== nm) { m.name = nm; this.dirty = true; }
    const w = this.watermarks.get(userId);
    if (w) { w.name = nm; w.lastSeen = Date.now(); w.online = true; }
    return m ? m.role : null;
  }

  _rememberReq(reqId) {
    if (!reqId) return;
    this.seenReq.set(reqId, Date.now());
    if (this.seenReq.size > MAX_REQ_RECORDS) {
      const first = this.seenReq.keys().next().value;
      this.seenReq.delete(first);
    }
  }
  _pruneBatches() {
    while (this.batches.size > MAX_BATCH_RECORDS) {
      const oldest = this.batches.keys().next().value;
      this.batches.delete(oldest);
    }
  }
  _batchReply(rec, batchId) {
    if (rec.status === 'rejected') {
      return { rejected: true, batchId, status: 'rejected', epoch: rec.epoch, atSeq: rec.atSeq, role: rec.role, need: rec.need, reason: rec.reason, kinds: rec.kinds || {}, ts: rec.ts, draftId: rec.draftId };
    }
    if (rec.status === 'empty') return { empty: true, batchId, status: 'empty', epoch: rec.epoch };
    return {
      applied: (rec.seqs || []).map(seq => ({ seq, op: this.bySeq.get(seq) })).filter(x => x.op),
      rev: rec.rev || null, batchId, status: 'applied', epoch: rec.epoch,
    };
  }

  // 完整隔离载荷（授权拒绝 / 换算冲突），跨压缩与重启保留，仅本人可取。
  _putQuarantine(rec) {
    this.quarantine.set(rec.owner + '#' + rec.batchId, rec);
    if (this.quarantine.size > 5000) {
      // 上限保护：仅淘汰最旧的"冲突"草稿（授权拒绝记录永不自动淘汰）。
      const oldest = [...this.quarantine.values()]
        .filter(r => r.kind === 'conflict')
        .sort((a, b) => a.ts - b.ts)[0];
      if (oldest) this.quarantine.delete(oldest.owner + '#' + oldest.batchId);
    }
  }
  quarantineFor(userId) {
    return [...this.quarantine.values()]
      .filter(r => r.owner === userId)
      .sort((a, b) => a.ts - b.ts);
  }
  // 本人显式核准后重提并成功生效：相应的旧"被拒"记录即已处置，予以核销。
  // 仅限授权拒绝（kind=rejected）；换算冲突草稿必须逐项显式处置，不自动核销。
  // 未获核准的记录不受影响（仍跨压缩、跨重启完整保留）。
  _resolveRejectionsByOps(actorId, committedOps) {
    const ids = new Set();
    for (const op of committedOps || []) if (op.opId) ids.add(op.opId);
    if (!ids.size) return;
    for (const [k, r] of this.quarantine) {
      if (r.owner !== actorId || r.kind !== 'rejected' || !r.ops || !r.ops.length) continue;
      let covered = 0;
      for (const op of r.ops) if (op.opId && ids.has(op.opId)) covered++;
      if (covered === r.ops.length) this.quarantine.delete(k);
    }
  }
  // 换算冲突草稿：已核准生效的 op 从草稿与 conflicts 中移除；草稿清空则删除。
  _consumeConflictOps(actorId, committedOps) {
    const ids = new Set();
    for (const op of committedOps || []) if (op.opId) ids.add(op.opId);
    if (!ids.size) return;
    for (const [k, r] of this.quarantine) {
      if (r.owner !== actorId || r.kind !== 'conflict' || !r.ops || !r.ops.length) continue;
      const has = r.ops.some(op => op.opId && ids.has(op.opId));
      if (!has) continue;
      r.ops = r.ops.filter(op => !(op.opId && ids.has(op.opId)));
      r.conflicts = (r.conflicts || []).filter(c => !(c.op && c.op.opId && ids.has(c.op.opId)));
      r.mappedOps = (r.mappedOps || []).filter(op => !(op.opId && ids.has(op.opId)));
      if (!r.ops.length) this.quarantine.delete(k);
    }
  }
  _persistRejection(batchId, actorId, auth, ops) {
    const rec = {
      kind: 'rejected', status: 'rejected', draftId: null, ts: Date.now(),
      epoch: this.epoch, atSeq: this.seq,
      role: auth.role, need: auth.need, reason: auth.reason, kinds: auth.kinds || {},
      owner: actorId, batchId, ops, gen: this.gen,
    };
    rec.draftId = 'q-' + crypto.createHash('sha256').update(actorId + '#' + batchId).digest('hex').slice(0, 16);
    this._putQuarantine(rec);
    this.batches.set(batchId, {
      status: 'rejected', ts: rec.ts, epoch: rec.epoch, atSeq: rec.atSeq,
      role: auth.role, need: auth.need, reason: auth.reason, kinds: rec.kinds,
      by: actorId, draftId: rec.draftId,
    });
    this._pruneBatches();
    this.saveSync(); // 隔离载荷必须扛得住重启与下一轮压缩
    return rec;
  }

  // 成员变更：仅 owner；reqId 幂等；成功后 epoch+1 并写审计条目。
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
    let fromRole = cur ? cur.role : null;
    let toRole = null;

    if (act === 'invite') {
      if (!AUTHZ.isValidRole(wantRole)) return { ok: false, code: 'bad-role', message: '角色不合法' };
      if (cur) {
        if (cur.role === wantRole) { this._rememberReq(reqId); this.saveSync(); return { ok: true, applied: false, duplicate: false, noop: 'already-member', epoch: this.epoch, members: this.publicMembers() }; }
        effectiveAct = 'role';
        toRole = wantRole;
      } else {
        toRole = wantRole;
      }
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
    if (effectiveAct === 'remove') {
      this.members.delete(target);
    } else if (!cur) {
      this.members.set(target, { id: target, name: clip(msg.name || target, 80), role: toRole, since: now, by: actorId, byName: actor.name });
    } else {
      cur.role = toRole;
    }
    this.epoch += 1;
    const entry = {
      seq: ++this.seq, ts: now, kind: 'membership', act: effectiveAct,
      by: actorId, byName: actor.name,
      target, targetName: cur ? cur.name : target,
      from: fromRole, to: effectiveAct === 'remove' ? null : toRole,
      epoch: this.epoch,
    };
    this.ledger.push(entry);
    if (this.ledger.length > MAX_LEDGER) this.ledger.splice(0, this.ledger.length - MAX_LEDGER);
    this._rememberReq(reqId);
    this.saveSync();
    return { ok: true, applied: true, duplicate: false, epoch: this.epoch, entry, members: this.publicMembers() };
  }

  // ---------------- 有界流水压缩 ----------------
  compactStatus() {
    const now = Date.now();
    return {
      gen: this.gen,
      seq: this.seq,
      logMinSeq: this.logMinSeq,
      windowOps: this.ops.length,
      logOpCap: this.caps.logOpCap,
      revSnapshotCap: this.caps.revSnapshotCap,
      baselineChars: this.baseline ? this.baseline.chars.length : 0,
      diskBytes: this._diskBytes(),
      staging: this.staging ? {
        gen: this.staging.gen, cutSeq: this.staging.cutSeq,
        since: this.staging.startedAt, phase: this.staging.phase,
      } : null,
      lastError: this.lastError,
      generations: this.generations.slice(-12),
      watermarks: this.publicWatermarks(now),
      epochs: this.epoch,
    };
  }
  _diskBytes() {
    try { return fs.statSync(this.file).size; } catch (e) { return 0; }
  }
  publicWatermarks(now) {
    now = now || Date.now();
    return [...this.watermarks.values()]
      .map(w => ({
        userId: w.userId, name: w.name, gen: w.gen, seq: w.seq,
        online: !!w.online && now - w.lastSeen < LEASE_MS,
        ageMs: now - w.lastSeen,
      }))
      .sort((a, b) => (b.online - a.online) || (b.gen - a.gen) || (a.userId < b.userId ? -1 : 1));
  }
  _recordWatermark(userId, name, gen, seq) {
    let w = this.watermarks.get(userId);
    if (!w) { w = { userId, name: name || userId, gen: 0, seq: 0, lastSeen: Date.now(), online: true }; this.watermarks.set(userId, w); }
    w.name = name || w.name;
    if (gen != null) w.gen = Math.max(w.gen, gen | 0);
    if (seq != null) w.seq = Math.max(w.seq, seq | 0);
    w.lastSeen = Date.now();
    w.online = true;
  }
  markOffline(userId) { const w = this.watermarks.get(userId); if (w) w.online = false; }

  // 阶段一（可与在线写入并发）：在切点冻结"恰好到 cutSeq"的基线投影。
  // 切点之后到达的写入不烤进基线（继续留在窗口），边界两侧变动都不丢、不重。
  // 不修改任何权威状态，不产生磁盘副本；失败仅记录原因。
  prepareCompact(forced) {
    if (this.staging) return { ok: false, code: 'already-compacting', staging: this.staging.gen };
    const cap = this.caps.logOpCap;
    if (this.ops.length <= cap && !forced) {
      return { ok: false, code: 'below-cap', windowOps: this.ops.length, cap };
    }
    if (this.ops.length === 0) return { ok: false, code: 'nothing-to-compact' };
    // 切点：保留最后 cap 条流水；窗口不足时压到最早一条之前。
    const cutIdx = Math.max(0, this.ops.length - cap);
    const cutSeq = cutIdx === 0 ? this.logMinSeq - 1 : this.ops[cutIdx - 1].seq;
    const windowAtCut = this.ops.slice(cutIdx);
    try {
      // 权威态 = 当前基线 + 全窗口。独立重放到 cutSeq => 切点投影，
      // 与"切点之后是否已有在线写入"无关（写入不停服）。
      const scratch = new CRDT.Doc('compact');
      if (this.baseline) CRDT.importBaseline(scratch, this.baseline);
      for (const x of this.ops) { if (x.seq > cutSeq) break; scratch.apply(x.op); }
      // windowAtCut 中的引用必须可在新基线上解释（其锚点墓碑予以保留）。
      const baseline = CRDT.buildBaseline(scratch, windowAtCut);
      this.staging = {
        gen: this.gen + 1, cutSeq, baseline,
        startedAt: Date.now(), phase: 'prepared', forced: !!forced,
      };
    } catch (e) {
      this.lastError = { ts: Date.now(), phase: 'prepare', message: String(e && e.message || e) };
      return { ok: false, code: 'prepare-failed', message: this.lastError.message };
    }
    return { ok: true, gen: this.staging.gen, cutSeq, delayed: COMPACT_DELAY_MS };
  }

  // 阶段二：原子切换。切点之后到达的写入全部保留；投影指纹必须逐字节不变。
  commitCompact() {
    const st = this.staging;
    if (!st) return { ok: false, code: 'no-staging' };
    try {
      // 提交时重新取权威窗口：制作基线期间的在线写入全部位于 cutSeq 之后。
      const newWindow = this.ops.filter(x => x.seq > st.cutSeq);
      // 独立重放"新基线 + 新窗口"，必须与当前权威投影逐字节一致，否则拒绝切换。
      const check = new CRDT.Doc('verify');
      check.actor = this.doc.actor || 'server';
      CRDT.importBaseline(check, st.baseline);
      for (const x of newWindow) check.apply(x.op);
      const fpRebuilt = CRDT.fingerprint(check);
      const fpCurrent = CRDT.fingerprint(this.doc);
      if (fpRebuilt !== fpCurrent) {
        throw new Error('投影指纹不一致：拒绝切换（权威态保持旧代次，可安全重试）');
      }
      // opId 水位并入切点前已吸收范围（水位只升不降）。
      for (const { seq, op } of this.ops) if (seq <= st.cutSeq) this._noteOpId(op.opId);
      // 修订：切点外 / 超量的全量快照回收（只留元数据），账本时间线不变。
      const snapKeep = this.caps.revSnapshotCap;
      const withSnap = new Set(this.revs.filter(r => r.snapshot).slice(-snapKeep).map(r => r.n));
      const newRevs = this.revs.map(r => {
        const rr = Object.assign({}, r, { gen: r.gen || 0 });
        if (r.snapshot && (r.seq <= st.cutSeq || !withSnap.has(r.n))) {
          return Object.assign({}, rr, { snapshot: null, compacted: true });
        }
        return rr;
      });
      // 权威态切换：单一同步赋值段 + tmp/rename 原子落盘。
      // 进程在切换前后被杀 => 磁盘上只可能读到完整旧文件或完整新文件。
      this.baseline = st.baseline;
      this.gen = st.gen;
      this.ops = newWindow;
      this.logMinSeq = st.cutSeq + 1;
      this.bySeq = new Map();
      for (const x of newWindow) this.bySeq.set(x.seq, x.op);
      this.revs = newRevs;
      // 关键：内存权威 doc 直接采用上面"已逐字节校验过"的 check（= 新基线 + 新窗口）。
      // 剪枝前内存里仍保留已被磁盘回收的墓碑；若继续沿用，可达性判定（stale/rebase）
      // 会误放行指向已回收锚点的操作。采用 check 后内存态、迁移端所见、磁盘投影严格一致。
      this.doc = check;
      this.migrateOps = CRDT.baselineOps(st.baseline);
      this.generations.push({
        gen: this.gen, cutSeq: st.cutSeq, ts: st.startedAt, commitTs: Date.now(),
        baselineChars: st.baseline.chars.length, windowOps: newWindow.length,
        forced: !!st.forced,
      });
      if (this.generations.length > 50) this.generations.splice(0, this.generations.length - 50);
      this.staging = null;
      this.lastError = null;
      this.saveSync();
      return {
        ok: true, gen: this.gen, cutSeq: st.cutSeq,
        windowOps: newWindow.length, logMinSeq: this.logMinSeq,
        retainedRange: [this.logMinSeq, this.seq],
      };
    } catch (e) {
      this.lastError = { ts: Date.now(), phase: 'commit', message: String(e && e.message || e) };
      this.staging = null; // 失败不改动权威态，重试安全
      return { ok: false, code: 'commit-failed', message: this.lastError.message };
    }
  }

  setCaps(actorId, msg) {
    if (this.roleOf(actorId) !== 'owner') return { ok: false, code: 'forbidden-caps', message: '只有所有者可以调整流水上限' };
    const logOpCap = Math.max(1, Math.min(100000, Number(msg.logOpCap) || this.caps.logOpCap));
    const revSnapshotCap = Math.max(0, Math.min(1000, Number(msg.revSnapshotCap) || this.caps.revSnapshotCap));
    this.caps = { logOpCap, revSnapshotCap };
    this.saveSync();
    return { ok: true, caps: this.caps };
  }

  // ---------------- 内容批次：原子授权 + 幂等 ----------------
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
      const rec = { seq: this.seq, op, gen: this.gen };
      this.ops.push(rec);
      this.bySeq.set(this.seq, op);
      this.doc.apply(op);
      applied.push({ seq: this.seq, op });
    }
    const rev = Object.assign({
      n: this.revs.length ? this.revs[this.revs.length - 1].n + 1 : 1,
      seq: this.seq, fromSeq: applied[0].seq, ts: Date.now(), by: clip(by || '?', 128),
      kind: kind || 'edit', summary: this._summarize(ops), snapshot: this._snapshot(),
      gen: this.gen,
    }, extra || {});
    this.revs.push(rev);
    this._trimRevs();
    this.dirty = true;
    return { applied, rev };
  }
  _trimRevs() {
    if (this.revs.length > 1000) this.revs.splice(0, this.revs.length - 1000);
    const keep = this.caps.revSnapshotCap;
    const snapRevs = this.revs.filter(r => r.snapshot);
    if (snapRevs.length > keep) {
      const drop = snapRevs.slice(0, snapRevs.length - keep);
      const dropSet = new Set(drop.map(r => r.n));
      for (const r of this.revs) if (dropSet.has(r.n)) { r.snapshot = null; r.compacted = true; }
    }
  }

  // 引用是否在"当前基线 + 窗口 + 本批次新插入"中可达。批内链式插入需把新 id 计入。
  _reachableCheck(valid) {
    const batchNew = new Set();
    for (const op of valid) if (op.t === 'ins') batchNew.add(op.id);
    const known = (id) => id === CRDT.ROOT || this.doc.hasId(id) || batchNew.has(id);
    for (const op of valid) {
      for (const id of CRDT.refIdsOfOp(op)) {
        if (!known(id)) return { missing: id, op };
      }
    }
    return null;
  }

  // 普通在线批次。落后于保留窗口的端其引用已无法解释 => 要求先迁移/换算，绝不猜测挂靠。
  submitBatch(actorId, msg) {
    const batchId = clip(msg.batchId || ('srv-' + Date.now().toString(36) + '-' + Math.random().toString(36).slice(2, 10)), 200);
    const cached = this.batches.get(batchId);
    if (cached) return Object.assign({ duplicate: true, batchId }, this._batchReply(cached, batchId));

    const raw = Array.isArray(msg.ops) ? msg.ops.slice(0, 5000) : [];
    const valid = [];
    for (const r of raw) { const op = sanitizeOp(r); if (op) valid.push(op); }

    const miss = this._reachableCheck(valid);
    if (miss) {
      return {
        stale: true, code: 'behind-window', batchId, gen: this.gen, seq: this.seq,
        logMinSeq: this.logMinSeq,
        message: '该批次引用的字符早于保留窗口且其墓碑已被回收，请先取得新基线并进行基线换算（rebase）。',
        missing: miss.missing,
      };
    }

    const role = AUTHZ.effectiveRole(this.roleOf(actorId));
    const auth = AUTHZ.authorizeBatch(role, valid);
    if (!auth.ok) {
      const rec = this._persistRejection(batchId, actorId, auth, valid);
      return Object.assign({ rejected: true, batchId }, this._batchReply(this.batches.get(batchId), batchId));
    }

    if (!valid.length) {
      const rec = { status: 'empty', ts: Date.now(), epoch: this.epoch };
      this.batches.set(batchId, rec);
      this._pruneBatches();
      return Object.assign({ empty: true, batchId }, this._batchReply(rec, batchId));
    }

    const novel = [];
    for (const op of valid) {
      if (op.opId && this._hasOpId(op.opId)) continue;
      if (op.opId) this._noteOpId(op.opId);
      novel.push(op);
    }
    const commit = novel.length ? this._commitOps(novel, actorId, 'edit') : null;
    if (commit) this._resolveRejectionsByOps(actorId, novel);
    const rec = {
      status: 'applied', ts: Date.now(), epoch: this.epoch,
      seqs: novel.map((_, i) => commit.applied[i].seq),
      rev: commit ? pubRev(commit.rev) : null, by: actorId,
    };
    this.batches.set(batchId, rec);
    this._pruneBatches();
    return {
      applied: commit ? commit.applied : [],
      rev: commit ? pubRev(commit.rev) : null,
      batchId, status: 'applied', epoch: this.epoch,
    };
  }

  // ---------------- 快照迁移（落后于保留窗口的镜像端） ----------------
  migrationInfo() {
    return {
      gen: this.gen, seq: this.seq, logMinSeq: this.logMinSeq,
      chunkSize: MIGRATE_CHUNK,
      members: this.publicMembers(), epoch: this.epoch,
      ledger: this.publicLedger(),
      revs: this.revs.map(pubRev),
      ops: this.ops, // 迁移最后一片附带窗口增量
    };
  }
  _baselineOps() {
    if (!this.migrateOps.length && this.baseline) this.migrateOps = CRDT.baselineOps(this.baseline);
    return this.migrateOps;
  }
  migrationTotal() { return Math.max(1, Math.ceil(this._baselineOps().length / MIGRATE_CHUNK)); }
  // 幂等分片：同一 (gen,index) 永远返回同一片；乱序/重复到达不产生重复投影。
  // 幂等分片：同一 (gen,index) 永远返回同一片；乱序/重复到达不产生重复投影。
  // 尾片附带窗口增量与治理状态，以及本人完整隔离/冲突草稿（跨压缩、跨重启可见）。
  migrateChunk(reqGen, index, userId) {
    if (reqGen !== this.gen) return { ok: false, code: 'gen-changed', gen: this.gen };
    const all = this._baselineOps();
    const total = Math.max(1, Math.ceil(all.length / MIGRATE_CHUNK));
    if (index < 0 || index >= total) return { ok: false, code: 'bad-index', total };
    return {
      ok: true, gen: this.gen, index, total, chunkSize: MIGRATE_CHUNK,
      final: index === total - 1,
      ops: all.slice(index * MIGRATE_CHUNK, (index + 1) * MIGRATE_CHUNK),
      tail: index === total - 1 ? {
        gen: this.gen,
        logMinSeq: this.logMinSeq, seq: this.seq,
        window: this.ops,
        members: this.publicMembers(), epoch: this.epoch,
        ledger: this.publicLedger(), revs: this.revs.map(pubRev),
        quarantine: userId ? this.quarantineFor(userId) : [],
      } : null,
    };
  }

  // ---------------- 基线换算（积压批次确定性投射到新基线） ----------------
  // 引用仍在（活字符或保留墓碑）=> 保留改动意图；引用随墓碑被回收 => 显式冲突草稿。
  // 换算与授权都按"当前"成员纪元；任一冲突或越权 => 零发布。
  submitRebase(actorId, msg) {
    const reqId = clip(msg.reqId || '', 200);
    const batchId = clip(msg.batchId || '', 200);
    const key = actorId + '#' + batchId;
    if (reqId && this.rebaseReqs.has(reqId)) {
      return Object.assign({ duplicate: true }, this.rebaseReqs.get(reqId));
    }
    if (this.quarantine.has(key)) {
      // 同一 (本人, batchId) 的重复换算：回放首次结论，绝不重复入账/生效。
      const prev = this.quarantine.get(key);
      return Object.assign({ duplicate: true }, this._rebaseReply(prev, batchId));
    }
    const raw = Array.isArray(msg.ops) ? msg.ops.slice(0, 5000) : [];
    const valid = [];
    for (const r of raw) { const op = sanitizeOp(r); if (op) valid.push(op); }

    // 1) 引用映射（恒等映射 + 可达性判定；批内链式插入的新 id 可达）
    const batchNew = new Set();
    for (const op of valid) if (op.t === 'ins') batchNew.add(op.id);
    const conflicts = [];
    const mapped = [];
    for (const op of valid) {
      const bad = CRDT.refIdsOfOp(op).find(id => id !== CRDT.ROOT && !this.doc.hasId(id) && !batchNew.has(id));
      if (bad) {
        conflicts.push({
          op,
          reason: '锚点所指字符（' + clip(bad, 48) + '）的墓碑已在第 ' + this.gen + ' 代压缩中回收，无法确定性映射；该改动未被挂接到任何其他字句。',
          missing: bad,
        });
      } else {
        mapped.push(op);
      }
    }
    const role = AUTHZ.effectiveRole(this.roleOf(actorId));
    const auth = AUTHZ.authorizeBatch(role, valid);

    if (conflicts.length || !auth.ok) {
      // 冲突优先于授权解释；降权/移除主体同样零发布，但冲突草稿只给本人。
      let reason, need = null, kinds = auth.kinds || {};
      if (conflicts.length) {
        reason = '积压批次中有 ' + conflicts.length + ' 条操作的锚点无法映射到第 ' + this.gen + ' 代新基线（所指墓碑已回收），整批未发布，已生成冲突草稿供你逐项处置。';
      } else {
        reason = auth.reason; need = auth.need;
      }
      const rec = {
        kind: 'conflict', status: 'conflict',
        draftId: 'q-' + crypto.createHash('sha256').update(key).digest('hex').slice(0, 16),
        ts: Date.now(), epoch: this.epoch, atSeq: this.seq,
        role: auth.role, need, reason, kinds,
        owner: actorId, batchId, ops: valid, gen: this.gen,
        conflicts: conflicts.map(c => ({ op: c.op, reason: c.reason, missing: c.missing })),
        mappedOps: mapped, authOk: !!auth.ok,
      };
      this._putQuarantine(rec);
      const reply = this._rebaseReply(rec, batchId);
      if (reqId) this.rebaseReqs.set(reqId, reply);
      if (this.rebaseReqs.size > 5000) this.rebaseReqs.delete(this.rebaseReqs.keys().next().value);
      this.saveSync();
      return reply;
    }

    if (!mapped.length) {
      const reply = { empty: true, batchId, status: 'empty', epoch: this.epoch, gen: this.gen };
      if (reqId) this.rebaseReqs.set(reqId, reply);
      return reply;
    }

    const novel = [];
    for (const op of mapped) {
      if (op.opId && this._hasOpId(op.opId)) continue;
      if (op.opId) this._noteOpId(op.opId);
      novel.push(op);
    }
    const commit = novel.length ? this._commitOps(novel, actorId, 'rebase', { rebasedFromGen: msg.fromGen != null ? msg.fromGen : null }) : null;
    if (commit) {
      // 冲突草稿中被本人显式核准并成功换算的操作从草稿移除；仍冲突的锚点项继续保留。
      this._consumeConflictOps(actorId, novel);
    }
    const reply = {
      applied: commit ? commit.applied : [],
      rev: commit ? pubRev(commit.rev) : null,
      batchId, status: 'applied', epoch: this.epoch, gen: this.gen,
      conflicts: [], rebased: true,
    };
    if (reqId) this.rebaseReqs.set(reqId, reply);
    this.saveSync(); // 换算生效与授权纪元同样需要抗宕机
    return reply;
  }
  _rebaseReply(rec, batchId) {
    return {
      conflict: true, batchId, status: 'conflict', epoch: rec.epoch, atSeq: rec.atSeq,
      role: rec.role, need: rec.need, reason: rec.reason, kinds: rec.kinds || {},
      draftId: rec.draftId, gen: rec.gen,
      conflicts: rec.conflicts || [],
      ops: rec.ops,
      ts: rec.ts,
    };
  }

  // 本人显式核准：清除隔离/冲突草稿（重提本身是新 batchId 的 ops/rebase 调用）。
  dismissQuarantine(actorId, draftId) {
    for (const [k, r] of this.quarantine) {
      if (r.owner === actorId && r.draftId === clip(draftId || '', 80)) {
        this.quarantine.delete(k);
        this.saveSync();
        return { ok: true, draftId };
      }
    }
    return { ok: false, code: 'not-found' };
  }

  // 恢复检查点：仅 owner；已随压缩回收的快照 => 明确错误且不产生修订/演进记录。
  restore(actorId, targetN) {
    const role = this.roleOf(actorId);
    if (role !== 'owner') return { forbidden: true, code: 'forbidden-rollback', message: '只有所有者可以回滚到历史检查点' };
    const rev = this.revs.find(r => r.n === targetN);
    if (!rev) return { notfound: true, code: 'rev-not-found', message: '找不到该修订版本（可能已超出保留范围）' };
    if (!rev.snapshot) {
      return {
        compacted: true, code: 'checkpoint-compacted',
        message: rev.compacted
          ? '修订 #' + targetN + ' 的快照已在第 ' + (rev.gen || 0) + ' 代压缩中回收，无法恢复；当前可恢复的检查点见修订时间线。'
          : '该检查点没有快照，无法恢复。',
      };
    }
    const snap = rev.snapshot;
    const ops = [];
    for (const id of this.doc.visibleIds()) ops.push({ t: 'del', id, by: actorId });
    const actor = 'srv-' + clip(String(actorId), 32) + '-r' + targetN + '-' + Date.now();
    let c = 0, after = '';
    const newIds = [];
    for (const ch of snap.text) {
      const id = actor + ':' + (++c);
      ops.push({ t: 'ins', id, after, ch, by: actorId });
      after = id;
      newIds.push(id);
    }
    const anchor = (pos, edge) => {
      if (!newIds.length) return { id: null, edge };
      if (edge === 's') return pos <= 0 ? { id: null, edge: 's' } : { id: newIds[Math.min(pos, newIds.length - 1)], edge: 's' };
      return pos >= newIds.length ? { id: null, edge: 'e' } : { id: newIds[Math.max(pos - 1, 0)], edge: 'e' };
    };
    for (const m of snap.marks || []) {
      if (m.e <= m.s) continue;
      ops.push({ t: 'mark', id: actor + ':m:' + (++c), start: anchor(m.s, 's'), end: anchor(m.e, 'e'), attrs: m.attrs, ts: Date.now(), by: actorId, deleted: false });
    }
    const commit = this._commitOps(ops, actorId, 'restore', { target: targetN });
    return { applied: commit.applied, rev: pubRev(commit.rev) };
  }

  // 回退到"仍保留的基线点"：不删数据、不回放旧代，而是像修订恢复一样产生新演进；
  // 请求已清除的基线点 => 明确错误且不增加演进记录。
  restoreGeneration(actorId, targetGen) {
    const role = this.roleOf(actorId);
    if (role !== 'owner') return { forbidden: true, code: 'forbidden-rollback', message: '只有所有者可以回退到历史代次' };
    targetGen = Number(targetGen);
    if (!Number.isInteger(targetGen) || targetGen < 0 || targetGen > this.gen) {
      return { notfound: true, code: 'generation-not-found', message: '请求的基线代次不存在' };
    }
    if (targetGen === this.gen) {
      return { ok: true, noop: true, gen: this.gen, message: '已处于该代次' };
    }
    // 旧代基线已物理删除（不得用隐藏副本规避回收）：只有当前权威基线可作为回退点。
    return {
      compacted: true, code: 'generation-compacted',
      message: '第 ' + targetGen + ' 代基线已在后续压缩中物理回收；无法回退到已清除的基线点。回退到当前基线会产生新的演进记录。',
      currentGen: this.gen,
    };
  }
  // 回到当前基线点：丢弃窗口内的内容演进（以"删除可见字符 + 基线文本重放"作为新修订），
  // 产生新的代次演进记录。
  restoreCurrentBaseline(actorId) {
    const role = this.roleOf(actorId);
    if (role !== 'owner') return { forbidden: true, code: 'forbidden-rollback', message: '只有所有者可以回退到基线点' };
    if (!this.baseline) return { notfound: true, code: 'no-baseline', message: '当前空间尚未压缩，没有基线点' };
    const check = new CRDT.Doc('base');
    CRDT.importBaseline(check, this.baseline);
    const snap = { text: check.text(), marks: check.activeMarks().map(m => ({ s: m.s, e: m.e, attrs: m.attrs })) };
    const ops = [];
    for (const id of this.doc.visibleIds()) ops.push({ t: 'del', id, by: actorId });
    const actor = 'srv-' + clip(String(actorId), 28) + '-g' + this.gen + '-' + Date.now();
    let c = 0, after = '';
    const newIds = [];
    for (const ch of snap.text) {
      const id = actor + ':' + (++c);
      ops.push({ t: 'ins', id, after, ch, by: actorId });
      after = id;
      newIds.push(id);
    }
    const anchor = (pos, edge) => {
      if (!newIds.length) return { id: null, edge };
      if (edge === 's') return pos <= 0 ? { id: null, edge: 's' } : { id: newIds[Math.min(pos, newIds.length - 1)], edge: 's' };
      return pos >= newIds.length ? { id: null, edge: 'e' } : { id: newIds[Math.max(pos - 1, 0)], edge: 'e' };
    };
    for (const m of snap.marks || []) {
      if (m.e <= m.s) continue;
      ops.push({ t: 'mark', id: actor + ':m:' + (++c), start: anchor(m.s, 's'), end: anchor(m.e, 'e'), attrs: m.attrs, ts: Date.now(), by: actorId, deleted: false });
    }
    const commit = this._commitOps(ops, actorId, 'baseline-restore', { restoredGen: this.gen });
    this.generations.push({
      gen: this.gen, cutSeq: this.logMinSeq - 1, ts: Date.now(), commitTs: Date.now(),
      baselineChars: this.baseline.chars.length, windowOps: this.ops.length,
      note: 'owner 回退到当前基线点，作为新演进（修订 #' + commit.rev.n + '）',
    });
    this.saveSync();
    return { applied: commit.applied, rev: pubRev(commit.rev) };
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
function broadcastGeneration(store, room, res) {
  broadcast(room, {
    t: 'generation', gen: res.gen, cutSeq: res.cutSeq, seq: store.seq,
    logMinSeq: res.logMinSeq, retainedRange: res.retainedRange,
    ts: Date.now(), windowOps: res.windowOps,
  });
}

// 自动压缩：超过配置上界即制作新一代代；切点发布之间允许在线写入（多轮收敛）。
// AUTO_COMPACT=0 仅用于验收测试精确控制"提交前强杀"窗口；默认开启（生产行为）。
const AUTO_COMPACT = process.env.AUTO_COMPACT !== '0';
function maybeAutoCompact(store, room) {
  if (!AUTO_COMPACT) return;
  if (store.staging) return;
  if (store.ops.length <= store.caps.logOpCap) return;
  const prep = store.prepareCompact(false);
  if (!prep.ok) {
    if (prep.code === 'already-compacting') return;
    broadcast(room, { t: 'compactError', error: store.lastError });
    return;
  }
  const finish = () => {
    const res = store.commitCompact();
    if (res.ok) broadcastGeneration(store, room, res);
    else broadcast(room, { t: 'compactError', error: store.lastError || { message: res.message } });
    if (store.ops.length > store.caps.logOpCap) maybeAutoCompact(store, room); // 多轮直到有界
  };
  if (COMPACT_DELAY_MS > 0) setTimeout(finish, COMPACT_DELAY_MS);
  else finish();
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
      const initEntry = store.ensureInitialized(clientId, name);
      store.touchName(clientId, name);
      rooms.get(room).set(conn, { id: clientId, name });
      const lastSeq = +msg.lastSeq || 0;
      const lastGen = +msg.gen || 0;
      const role = store.roleOf(clientId);
      store._recordWatermark(clientId, name, Math.max(lastGen, +msg.seenGen || 0), lastSeq);

      const base = {
        t: 'welcome',
        seq: store.seq, gen: store.gen, logMinSeq: store.logMinSeq,
        revs: store.revs.map(pubRev),
        ledger: store.publicLedger(),
        members: store.publicMembers(),
        epoch: store.epoch,
        initialized: store.initialized,
        initEntry: initEntry || undefined,
        you: clientId, name,
        role: role || 'viewer',
        member: !!role,
        caps: store.caps,
        compact: store.compactStatus(),
        quarantine: store.quarantineFor(clientId),
      };
      // 落后于保留窗口（或来自更旧代次）的镜像端：不给窗口增量（会无法重放），
      // 改走分片快照迁移 + rebase 换算协议。
      const info = store.migrationInfo();
      const needsMigration = lastSeq < store.logMinSeq - 1 || lastGen < store.gen;
      if (needsMigration && store.gen > 0) {
        conn.send(Object.assign(base, {
          needMigration: true,
          migration: {
            gen: info.gen, seq: info.seq, logMinSeq: info.logMinSeq,
            chunkSize: info.chunkSize, totalChunks: store.migrationTotal(),
          },
          ops: [],
        }));
      } else {
        conn.send(Object.assign(base, {
          ops: store.ops.filter(o => o.seq > lastSeq),
          needMigration: false,
        }));
      }
      if (initEntry) broadcast(room, { t: 'members', epoch: store.epoch, members: store.publicMembers(), entry: initEntry });
      broadcastPresence(store, room);
      broadcast(room, { t: 'watermarks', watermarks: store.publicWatermarks() });
      return;
    }

    if (!room) return;
    const store = getStore(room);
    const meta = rooms.get(room).get(conn) || { id: '?', name: '?' };

    if (msg.t === 'member') {
      const res = store.submitMembership(meta.id, meta.name, msg);
      if (res.ok) {
        conn.send({ t: 'memberAck', reqId: clip(msg.reqId || '', 200), ok: true, duplicate: !!res.duplicate, applied: !!res.applied, noop: res.noop || null, epoch: res.epoch, members: res.members });
        if (res.applied) broadcast(room, { t: 'members', epoch: res.epoch, members: res.members, entry: res.entry });
        broadcastPresence(store, room);
        broadcast(room, { t: 'watermarks', watermarks: store.publicWatermarks() });
      } else {
        conn.send({ t: 'error', code: res.code, message: res.message, reqId: clip(msg.reqId || '', 200) });
      }
      return;
    }

    if (msg.t === 'ops') {
      const res = store.submitBatch(meta.id, msg);
      if (res.stale) {
        conn.send({ t: 'batchAck', batchId: res.batchId, status: 'stale', code: res.code, gen: res.gen, seq: res.seq, logMinSeq: res.logMinSeq, reason: res.message, missing: res.missing });
        return;
      }
      if (res.rejected) {
        conn.send({ t: 'batchAck', batchId: res.batchId, status: 'rejected', epoch: res.epoch, atSeq: res.atSeq, role: res.role, need: res.need, reason: res.reason, kinds: res.kinds, draftId: res.draftId });
        // 完整可阅读、可复制的被拒载荷只回本人，并已落盘（跨压缩/重启）。
        const full = store.quarantineFor(meta.id).find(q => q.batchId === res.batchId);
        if (full) conn.send({ t: 'quarantineItem', item: full });
        broadcast(room, { t: 'watermarks', watermarks: store.publicWatermarks() });
      } else if (res.duplicate || res.empty) {
        conn.send({
          t: 'batchAck', batchId: res.batchId, status: res.empty ? 'empty' : 'applied',
          epoch: res.epoch, applied: res.applied || [], rev: res.rev || null, duplicate: !!res.duplicate,
        });
      } else {
        if (res.applied && res.applied.length) {
          broadcast(room, { t: 'ops', batchId: res.batchId, epoch: res.epoch, applied: res.applied, rev: res.rev });
          maybeAutoCompact(store, room); // 有界流水：超上界即回收
        }
      }
      return;
    }

    // 快照迁移分片：幂等，允许乱序、重复请求。
    if (msg.t === 'migrate') {
      const res = store.migrateChunk(+msg.gen, +msg.index | 0, meta.id);
      conn.send(Object.assign({ t: 'migrateChunk', reqId: clip(msg.reqId || '', 200) }, res));
      return;
    }

    // 积压批次的基线换算（rebase）。
    if (msg.t === 'rebase') {
      const res = store.submitRebase(meta.id, msg);
      if (res.applied && res.applied.length) {
        broadcast(room, { t: 'ops', batchId: res.batchId, epoch: res.epoch, applied: res.applied, rev: res.rev, rebased: true });
        conn.send({ t: 'rebaseAck', reqId: clip(msg.reqId || '', 200), batchId: res.batchId, status: 'applied', epoch: res.epoch, gen: res.gen, applied: res.applied, rev: res.rev });
        maybeAutoCompact(store, room);
      } else if (res.conflict) {
        conn.send({ t: 'rebaseAck', reqId: clip(msg.reqId || '', 200), batchId: res.batchId, status: 'conflict', epoch: res.epoch, gen: res.gen, atSeq: res.atSeq, role: res.role, need: res.need, reason: res.reason, kinds: res.kinds, draftId: res.draftId, conflicts: res.conflicts, duplicate: !!res.duplicate });
        const full = store.quarantineFor(meta.id).find(q => q.batchId === res.batchId);
        if (full) conn.send({ t: 'quarantineItem', item: full });
      } else {
        conn.send({ t: 'rebaseAck', reqId: clip(msg.reqId || '', 200), batchId: res.batchId, status: 'empty', epoch: res.epoch, gen: store.gen, applied: [], duplicate: !!res.duplicate });
      }
      return;
    }

    if (msg.t === 'dismissQuarantine') {
      const res = store.dismissQuarantine(meta.id, msg.draftId);
      conn.send({ t: 'dismissAck', draftId: clip(msg.draftId || '', 80), ok: !!res.ok, code: res.code });
      return;
    }

    if (msg.t === 'watermark') {
      store._recordWatermark(meta.id, meta.name, +msg.gen, +msg.seq);
      broadcast(room, { t: 'watermarks', watermarks: store.publicWatermarks() });
      return;
    }

    // 主理人：手动压缩 / 查看状态 / 调整上界 / 回退基线点（均无需改存储文件即可排查）。
    if (msg.t === 'compact') {
      if (store.roleOf(meta.id) !== 'owner') { conn.send({ t: 'error', code: 'forbidden-compact', message: '只有所有者可以发起流水压缩' }); return; }
      const reqId = clip(msg.reqId || '', 200);
      const prep = store.prepareCompact(true);
      if (!prep.ok && prep.code !== 'already-compacting') {
        conn.send({ t: 'compactAck', reqId, ok: false, code: prep.code, message: store.lastError ? store.lastError.message : '暂无可压缩内容', compact: store.compactStatus() });
        return;
      }
      const finish = () => {
        const res = store.commitCompact();
        if (res.ok) {
          broadcastGeneration(store, room, res);
          conn.send({ t: 'compactAck', reqId, ok: true, gen: res.gen, cutSeq: res.cutSeq, retainedRange: res.retainedRange, windowOps: res.windowOps, compact: store.compactStatus() });
          if (store.ops.length > store.caps.logOpCap) maybeAutoCompact(store, room);
        } else {
          conn.send({ t: 'compactAck', reqId, ok: false, code: res.code, message: res.message, compact: store.compactStatus() });
        }
      };
      if (COMPACT_DELAY_MS > 0) setTimeout(finish, COMPACT_DELAY_MS);
      else finish();
      return;
    }

    if (msg.t === 'compactStatus') {
      conn.send({ t: 'compactStatus', compact: store.compactStatus() });
      return;
    }

    if (msg.t === 'setCaps') {
      const res = store.setCaps(meta.id, msg);
      conn.send(res.ok ? { t: 'capsAck', ok: true, caps: res.caps, compact: store.compactStatus() } : { t: 'error', code: res.code, message: res.message });
      return;
    }

    if (msg.t === 'restoreGen') {
      const res = store.restoreGeneration(meta.id, +msg.gen);
      if (res.forbidden || res.notfound || res.compacted) {
        conn.send({ t: 'error', code: res.code, message: res.message, currentGen: res.currentGen });
      } else {
        conn.send({ t: 'restoreGenAck', ok: true, gen: res.gen, noop: !!res.noop, message: res.message });
      }
      return;
    }
    if (msg.t === 'restoreBaseline') {
      const res = store.restoreCurrentBaseline(meta.id);
      if (res.forbidden || res.notfound) {
        conn.send({ t: 'error', code: res.code, message: res.message });
      } else {
        broadcast(room, { t: 'ops', applied: res.applied, rev: res.rev, baselineRestore: true });
      }
      return;
    }

    if (msg.t === 'restore') {
      const res = store.restore(meta.id, +msg.rev);
      if (res.forbidden) {
        conn.send({ t: 'error', code: res.code, message: res.message });
      } else if (res.notfound || res.compacted) {
        conn.send({ t: 'error', code: res.code || 'not-found', message: res.message });
      } else {
        broadcast(room, { t: 'ops', applied: res.applied, rev: res.rev });
        maybeAutoCompact(store, room);
      }
      return;
    }
  };

  conn.onclose = () => {
    if (room && rooms.has(room)) {
      const store = getStore(room);
      const meta = rooms.get(room).get(conn);
      rooms.get(room).delete(conn);
      if (meta) { store.markOffline(meta.id); broadcast(room, { t: 'watermarks', watermarks: store.publicWatermarks() }); }
      broadcastPresence(store, room);
    }
  };
});

setInterval(() => { for (const s of stores.values()) s.save(); }, 2000).unref();
function shutdown() { for (const s of stores.values()) { s.dirty = true; s.save(); } process.exit(0); }
process.on('SIGINT', shutdown);
process.on('SIGTERM', shutdown);

server.listen(PORT, () => console.log(`[server] 协作文档服务已启动: http://0.0.0.0:${PORT}`));
