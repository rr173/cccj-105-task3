'use strict';
/*
 * 协作服务器：零依赖（仅 Node 内置模块）。
 * - HTTP：托管前端静态文件与共享 CRDT / 授权模块
 * - WebSocket（手写 RFC6455）：接收/广播操作
 * - 每个内容操作分配全局递增 seq => 所有客户端看到一致的修订时间线
 * - 成员治理：owner / editor / commenter / viewer 四角色
 *   · 成员变更（邀请 / 改角色 / 移除 / 空间初始化）全部进入共享审计账本，
 *     审计条目与内容修订共用同一条全局 seq => 二者顺序对所有人明确一致
 *   · 每次成员变更令授权纪元 epoch 单调 +1；每个操作批次按当前 epoch 原子授权，
 *     整批越权则整批拒绝且绝不发布，并持久化隔离引用（重启后重试仍幂等）
 *   · reqId / batchId / opId 三级幂等键，重试、重复投递、重启均不重复生效
 *   · 仅 owner 可回滚检查点
 * - 旧版无成员元数据的空间：首次打开时初始化唯一 owner，ops/revs 原样保留
 * - JSON 落盘（data/<doc>.json），重启后重放恢复
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
const MAX_REVS = 1000;
const MAX_LEDGER = 5000;
const MAX_BATCH_RECORDS = 10000;
const MAX_REQ_RECORDS = 20000;
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

function pubRev(r) { return r ? { n: r.n, seq: r.seq, fromSeq: r.fromSeq || r.seq, ts: r.ts, by: r.by, kind: r.kind, summary: r.summary, target: r.target } : null; }

// ---------------- 文档 / 成员存储 ----------------
class Store {
  constructor(name) {
    this.name = name;
    this.doc = new CRDT.Doc('server');
    this.seq = 0;
    this.ops = [];              // [{ seq, op }]
    this.bySeq = new Map();     // seq -> op（幂等重放批次时重建响应）
    this.revs = [];
    this.seenOpIds = new Set();
    // 成员治理
    this.initialized = false;   // 是否已初始化 owner（旧版空间/新空间首次打开时置位）
    this.members = new Map();   // userId -> { id, name, role, since, by, byName }
    this.epoch = 0;             // 授权纪元：每次成员变更 +1
    this.ledger = [];           // 审计条目（与内容修订共用 seq）
    this.batches = new Map();   // batchId -> 处理结果（applied/rejected/empty，持久化）
    this.seenReq = new Map();   // reqId -> ts（成员变更幂等）
    this.dirty = false;
    this.file = path.join(DATA_DIR, encodeURIComponent(name) + '.json');
    this._load();
  }

  _load() {
    let j;
    try { j = JSON.parse(fs.readFileSync(this.file, 'utf8')); } catch (e) { return; /* 新空间 */ }
    this.seq = j.seq || 0;
    this.ops = j.ops || [];
    this.revs = j.revs || [];
    for (const { seq, op } of this.ops) {
      this.doc.apply(op);
      this.bySeq.set(seq, op);
      if (op.opId) this.seenOpIds.add(op.opId);
    }
    if (j.v === 2) {
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
      console.log(`[store] "${this.name}" 载入 v2：${this.ops.length} 操作 / ${this.revs.length} 修订 / ${this.members.size} 成员 / epoch ${this.epoch}`);
    } else {
      // 旧版数据：内容与修订原样保留，成员元数据留待首次打开时初始化
      console.log(`[store] "${this.name}" 载入旧版数据：${this.ops.length} 操作 / ${this.revs.length} 修订，等待首次打开初始化 owner`);
    }
  }

  _serialize() {
    return JSON.stringify({
      v: 2,
      seq: this.seq,
      ops: this.ops,
      revs: this.revs,
      initialized: this.initialized,
      epoch: this.epoch,
      members: Object.fromEntries(this.members),
      ledger: this.ledger,
      batches: Object.fromEntries(this.batches),
      seenReqIds: [...this.seenReq.keys()],
    });
  }
  _writeSync() {
    const tmp = this.file + '.tmp';
    fs.writeFileSync(tmp, this._serialize());
    fs.renameSync(tmp, this.file);
    this.dirty = false;
  }
  save() { if (this.dirty) this._writeSync(); }
  // 成员变更 / 隔离引用必须立刻落盘（重启不丢、并发首开恰好一个 owner）
  saveSync() { this._writeSync(); }

  roleOf(userId) { const m = this.members.get(userId); return m ? m.role : null; }

  publicMembers() {
    return [...this.members.values()]
      .sort((a, b) => (AUTHZ.rank(b.role) - AUTHZ.rank(a.role)) || (a.id < b.id ? -1 : a.id > b.id ? 1 : 0))
      .map(m => ({ id: m.id, name: m.name, role: m.role, since: m.since, by: m.by, byName: m.byName }));
  }
  publicLedger() { return this.ledger.slice(-MAX_LEDGER); }

  _ownerCount() { let n = 0; for (const m of this.members.values()) if (m.role === 'owner') n++; return n; }

  // 首次打开：新空间或旧版升级。Node 单线程 + 同步落盘 => 并发首开恰好初始化一个 owner，
  // 且旧空间的 ops / revs 不被重写（序列化时原样带上）。
  ensureInitialized(firstId, firstName) {
    if (this.initialized) return null;
    const legacy = this.ops.length > 0 || this.revs.length > 0;
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

  // 刷新已知成员 / 访客的显示名（不是成员变更，不进审计）
  touchName(userId, name) {
    const m = this.members.get(userId);
    const nm = clip(name || userId, 80);
    if (m && m.name !== nm) { m.name = nm; this.dirty = true; }
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
      return { rejected: true, batchId, status: 'rejected', epoch: rec.epoch, atSeq: rec.atSeq, role: rec.role, need: rec.need, reason: rec.reason, kinds: rec.kinds || {}, ts: rec.ts };
    }
    if (rec.status === 'empty') return { empty: true, batchId, status: 'empty', epoch: rec.epoch };
    return {
      applied: (rec.seqs || []).map(seq => ({ seq, op: this.bySeq.get(seq) })).filter(x => x.op),
      rev: rec.rev || null, batchId, status: 'applied', epoch: rec.epoch,
    };
  }

  // 成员变更：仅 owner；reqId 幂等；成功后 epoch+1 并写审计条目（与内容共用 seq）。
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
      // 重试 / 重复投递：不再产生任何成员变化或审计条目
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
        effectiveAct = 'role'; // 邀请已是成员的人且角色不同 => 视为角色变更
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

    // 最后一个所有者不可被降权或移除
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
    this.saveSync(); // 成员变更立即持久化
    return { ok: true, applied: true, duplicate: false, epoch: this.epoch, entry, members: this.publicMembers() };
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

  // 调用方已完成授权与去重，这里只负责定序、应用、建修订
  _commitOps(ops, by, kind, extra) {
    const applied = [];
    for (const op of ops) {
      this.seq++;
      this.ops.push({ seq: this.seq, op });
      this.bySeq.set(this.seq, op);
      this.doc.apply(op);
      applied.push({ seq: this.seq, op });
    }
    const rev = Object.assign({
      n: this.revs.length ? this.revs[this.revs.length - 1].n + 1 : 1,
      seq: this.seq, fromSeq: applied[0].seq, ts: Date.now(), by: clip(by || '?', 128),
      kind: kind || 'edit', summary: this._summarize(ops), snapshot: this._snapshot(),
    }, extra || {});
    this.revs.push(rev);
    if (this.revs.length > MAX_REVS) this.revs.splice(0, this.revs.length - MAX_REVS);
    this.dirty = true;
    return { applied, rev };
  }

  // 原子授权一个传入批次：
  //  1) batchId 已处理过 => 原样返回首次结论（重复投递绝不二次生效）
  //  2) 按当前 epoch 对全批授权；任一越权 => 整批拒绝，不占 seq、不发布，落盘隔离引用
  //  3) opId 去重后提交，形成一个修订
  submitBatch(actorId, msg) {
    const batchId = clip(msg.batchId || ('srv-' + Date.now().toString(36) + '-' + Math.random().toString(36).slice(2, 10)), 200);
    const cached = this.batches.get(batchId);
    if (cached) return Object.assign({ duplicate: true, batchId }, this._batchReply(cached, batchId));

    const raw = Array.isArray(msg.ops) ? msg.ops.slice(0, 5000) : [];
    const valid = [];
    for (const r of raw) { const op = sanitizeOp(r); if (op) valid.push(op); }

    const role = AUTHZ.effectiveRole(this.roleOf(actorId));
    const auth = AUTHZ.authorizeBatch(role, valid);
    if (!auth.ok) {
      // 关键冲突路径：断连期间被降权/移除，重连补发批次。整批拒绝、零发布。
      const rec = {
        status: 'rejected', ts: Date.now(), epoch: this.epoch, atSeq: this.seq,
        role: auth.role, need: auth.need, reason: auth.reason, kinds: auth.kinds || {}, by: actorId,
      };
      this.batches.set(batchId, rec);
      this._pruneBatches();
      this.saveSync(); // 隔离引用必须扛得住重启，且重试按 batchId 幂等
      return Object.assign({ rejected: true, batchId }, this._batchReply(rec, batchId));
    }

    if (!valid.length) {
      const rec = { status: 'empty', ts: Date.now(), epoch: this.epoch };
      this.batches.set(batchId, rec);
      this._pruneBatches();
      return Object.assign({ empty: true, batchId }, this._batchReply(rec, batchId));
    }

    const novel = [];
    for (const op of valid) {
      if (op.opId && this.seenOpIds.has(op.opId)) continue; // 操作级重放去重
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
    return {
      applied: commit ? commit.applied : [],
      rev: commit ? pubRev(commit.rev) : null,
      batchId, status: 'applied', epoch: this.epoch,
    };
  }

  // 恢复历史检查点：仅 owner。生成普通删除/插入/格式批次作为新修订。
  restore(actorId, targetN) {
    const role = this.roleOf(actorId);
    if (role !== 'owner') return { forbidden: true, code: 'forbidden-rollback', message: '只有所有者可以回滚到历史检查点' };
    const rev = this.revs.find(r => r.n === targetN);
    if (!rev || !rev.snapshot) return { notfound: true, message: '找不到该修订版本' };
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
      const initEntry = store.ensureInitialized(clientId, name); // 并发首开恰好一个 owner
      store.touchName(clientId, name);
      rooms.get(room).set(conn, { id: clientId, name });
      const lastSeq = +msg.lastSeq || 0;
      const role = store.roleOf(clientId);
      conn.send({
        t: 'welcome',
        seq: store.seq,
        ops: store.ops.filter(o => o.seq > lastSeq),
        revs: store.revs.map(pubRev),
        ledger: store.publicLedger(),
        members: store.publicMembers(),
        epoch: store.epoch,
        initialized: store.initialized,
        initEntry: initEntry || undefined,
        you: clientId, name,
        role: role || 'viewer',
        member: !!role,
      });
      if (initEntry) broadcast(room, { t: 'members', epoch: store.epoch, members: store.publicMembers(), entry: initEntry });
      broadcastPresence(store, room);
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
        broadcastPresence(store, room); // 角色变化立即反映到在线名单
      } else {
        conn.send({ t: 'error', code: res.code, message: res.message, reqId: clip(msg.reqId || '', 200) });
      }
      return;
    }

    if (msg.t === 'ops') {
      const res = store.submitBatch(meta.id, msg);
      if (res.rejected) {
        // 仅回复发起者：整批被隔离，房间内其他人收不到任何内容
        conn.send({ t: 'batchAck', batchId: res.batchId, status: 'rejected', epoch: res.epoch, atSeq: res.atSeq, role: res.role, need: res.need, reason: res.reason, kinds: res.kinds });
      } else if (res.duplicate || res.empty) {
        // 重复投递：首次结论只回给发起者，不再次广播
        conn.send({
          t: 'batchAck', batchId: res.batchId, status: res.empty ? 'empty' : 'applied',
          epoch: res.epoch, applied: res.applied || [], rev: res.rev || null, duplicate: !!res.duplicate,
        });
      } else {
        if (res.applied && res.applied.length) {
          broadcast(room, { t: 'ops', batchId: res.batchId, epoch: res.epoch, applied: res.applied, rev: res.rev });
        }
      }
      return;
    }

    if (msg.t === 'restore') {
      const res = store.restore(meta.id, +msg.rev);
      if (res.forbidden) {
        conn.send({ t: 'error', code: res.code, message: res.message }); // 不产生修订
      } else if (res.notfound) {
        conn.send({ t: 'error', message: res.message });
      } else {
        broadcast(room, { t: 'ops', applied: res.applied, rev: res.rev });
      }
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

server.listen(PORT, () => console.log(`[server] 协作文档服务已启动: http://0.0.0.0:${PORT}`));
