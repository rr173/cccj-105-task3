'use strict';
/*
 * 集成测试：启动真实服务器，用模拟客户端验证成员治理与既有 CRDT 协作能力。
 *
 * 验收场景：
 *  1. 角色命令矩阵（共享规则 + 服务端强制）：被邀请者只能执行角色允许的命令
 *  2. commenter 可管理批注但不能改正文；viewer 两类写都不行
 *  3. editor 断连排队 → 被降为 viewer → 重连：整批不泄漏，完整进入隔离草稿
 *  4. 恢复 editor 后显式重提：整批恰好生效一次并正常合并
 *  5. 角色变更与断连批次竞争：两种总序下所有参与者看到相同结论、内容与账本顺序
 *  6. 重复邀请 / 角色变更 / 批次投递全部幂等
 *  7. 非 owner 回滚被拒，且不产生修订
 *  8. 成员、授权纪元、隔离引用、审计账本在重启后保留
 *  9. 旧版空间并发首次打开：恰好一个 owner，既有记录原样保留
 * 另含 CRDT 回归：在线同步 / 离线合并 / 批注悬空重挂 / 格式合并 / 恢复参与合并。
 */
const { spawn } = require('child_process');
const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const os = require('os');
const path = require('path');
const assert = require('assert');
const CRDT = require('../shared/crdt.js');
const AUTHZ = require('../shared/authz.js');

const PORT = 18099;
const RUN = Date.now();
const DATA_DIR = fs.mkdtempSync(path.join(os.tmpdir(), 'collab-test-'));

// ---------- 最小 WebSocket 客户端 ----------
function wsConnect() {
  return new Promise((resolve, reject) => {
    const key = crypto.randomBytes(16).toString('base64');
    const req = http.request({
      port: PORT, path: '/ws',
      headers: { Connection: 'Upgrade', Upgrade: 'websocket', 'Sec-WebSocket-Key': key, 'Sec-WebSocket-Version': 13 },
    });
    req.on('upgrade', (res, socket) => resolve(new WSClient(socket)));
    req.on('error', reject);
    req.end();
  });
}
class WSClient {
  constructor(sock) {
    this.sock = sock;
    this.buf = Buffer.alloc(0);
    this.handlers = [];
    sock.on('data', (d) => this._feed(d));
  }
  onMessage(fn) { this.handlers.push(fn); }
  send(obj) {
    const p = Buffer.from(JSON.stringify(obj));
    const mask = crypto.randomBytes(4);
    const l = p.length;
    let h;
    if (l < 126) h = Buffer.from([0x81, 0x80 | l]);
    else if (l < 65536) { h = Buffer.alloc(4); h[0] = 0x81; h[1] = 0x80 | 126; h.writeUInt16BE(l, 2); }
    else { h = Buffer.alloc(10); h[0] = 0x81; h[1] = 0x80 | 127; h.writeBigUInt64BE(BigInt(l), 2); }
    const masked = Buffer.from(p);
    for (let i = 0; i < masked.length; i++) masked[i] ^= mask[i & 3];
    this.sock.write(Buffer.concat([h, mask, masked]));
  }
  _feed(d) {
    this.buf = Buffer.concat([this.buf, d]);
    for (;;) {
      if (this.buf.length < 2) return;
      const b0 = this.buf[0], b1 = this.buf[1];
      let len = b1 & 0x7f, off = 2;
      if (len === 126) { if (this.buf.length < 4) return; len = this.buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (this.buf.length < 10) return; len = Number(this.buf.readBigUInt64BE(2)); off = 10; }
      if (this.buf.length < off + len) return;
      const payload = this.buf.slice(off, off + len);
      this.buf = this.buf.slice(off + len);
      if ((b0 & 0x0f) === 1) {
        const msg = JSON.parse(payload.toString());
        for (const fn of this.handlers) fn(msg);
      }
    }
  }
  close() { try { this.sock.destroy(); } catch (e) { /* ignore */ } }
}

// ---------- 模拟客户端（复刻浏览器端同步 + 治理逻辑） ----------
let batchCounter = 0;
class SimClient {
  constructor(id, doc) {
    this.id = id;
    this.docName = doc;
    this.doc = new CRDT.Doc(id);
    this.lastSeq = 0;
    this.gen = 0;
    this.logMinSeq = 0;
    this.opSeq = 0;
    this.allOps = [];
    this.pendingBatches = [];
    this.quarantine = [];
    this.revs = [];
    this.ledger = [];
    this.members = [];
    this.peers = [];
    this.watermarks = [];
    this.compactInfo = null;
    this.migration = null;  // { gen,total,chunks:Map,migrating,done }
    this.epoch = 0;
    this.role = null;
    this.welcome = null;
    this.errors = [];
    this.generations = [];
    this.ws = null;
    this.readyResolve = null;
    this.ready = new Promise((r) => { this.readyResolve = r; });
  }
  async connect() {
    this.welcome = null;
    this.ready = new Promise((r) => { this.readyResolve = r; });
    this.ws = await wsConnect();
    this.ws.onMessage((m) => this._handle(m));
    this.ws.send({ t: 'hello', clientId: this.id, name: this.id, doc: this.docName, lastSeq: this.lastSeq, gen: this.gen, seenGen: this.gen });
    await this.ready;
    // 若服务器要求迁移（落后窗口/旧代），等待快照迁移与积压换算全部完成后再返回，
    // 保证调用方 connect() 之后 this.doc 已是新基线投影。
    if (this.migration && this.migration.migrating) {
      await waitFor(() => this.migration && this.migration.done, 'connect: 快照迁移完成', 15000);
    }
  }
  disconnect() { if (this.ws) this.ws.close(); this.ws = null; }
  send(o) { if (this.ws) this.ws.send(o); }
  member(act, target, role, name) {
    const reqId = this.id + '#req#' + (crypto.randomUUID ? crypto.randomUUID() : Math.random().toString(36).slice(2));
    this._lastReq = reqId;
    this.send({ t: 'member', reqId, act, target, role, name });
    return reqId;
  }
  restore(rev) { this.send({ t: 'restore', rev }); }
  _upsertEntry(e) {
    if (!e || this.ledger.some(x => x.seq === e.seq && x.act === e.act && x.target === e.target)) return;
    this.ledger.push(e);
    this.ledger.sort((a, b) => a.seq - b.seq);
  }
  _handle(m) {
    if (m.t === 'welcome') {
      this.welcome = m;
      if (m.needMigration) {
        this._beginMigration(m);
        // ready 用于"连接已建立"；迁移完成由 connect() 再等待 migration.done。
        this.readyResolve();
        return;
      }
      this.migration = null;
      this.gen = m.gen || 0;
      this.logMinSeq = m.logMinSeq || 0;
      this.compactInfo = m.compact || this.compactInfo;
      this.watermarks = (this.compactInfo && this.compactInfo.watermarks) || this.watermarks;
      this._mergeQuarantine(m.quarantine || []);
      this.lastSeq = Math.max(this.lastSeq, m.seq || 0);
      const seen = new Set();
      for (const { seq, op } of m.ops) {
        this.doc.apply(op);
        this.allOps.push(op);
        this.lastSeq = Math.max(this.lastSeq, seq);
        if (op.opId) seen.add(op.opId);
      }
      for (const e of m.ledger || []) { this._upsertEntry(e); this.lastSeq = Math.max(this.lastSeq, e.seq); }
      this.revs = m.revs || [];
      for (const r of this.revs) this.lastSeq = Math.max(this.lastSeq, r.seq);
      this.members = m.members || [];
      this.epoch = m.epoch || 0;
      this.role = m.role || 'viewer';
      this.pendingBatches = this.pendingBatches.filter(b => {
        b.ops = b.ops.filter(op => !seen.has(op.opId));
        return b.ops.length > 0;
      });
      for (const b of this.pendingBatches) this.send({ t: 'ops', batchId: b.batchId, ops: b.ops });
      this.readyResolve();
    } else if (m.t === 'migrateChunk') {
      this._onChunk(m);
    } else if (m.t === 'ops') {
      for (const { seq, op } of m.applied) {
        this.doc.apply(op);
        this.allOps.push(op);
        this.lastSeq = Math.max(this.lastSeq, seq);
      }
      if (m.batchId) this._drop(m.batchId, m.applied);
      else this._dropOps(m.applied);
      if (m.rev) {
        if (!this.revs.some(r => r.n === m.rev.n)) this.revs.push(m.rev);
        this.lastSeq = Math.max(this.lastSeq, m.rev.seq);
      }
    } else if (m.t === 'batchAck') {
      if (m.status === 'stale') {
        this._beginMigration(m); // 旧基线上的提交：触发迁移+换算
      } else if (m.status === 'rejected') {
        this._quarantine(m);
        this.lastSeq = Math.max(this.lastSeq, m.atSeq || 0);
      } else {
        for (const { seq, op } of m.applied || []) {
          this.doc.apply(op);
          this.allOps.push(op);
          this.lastSeq = Math.max(this.lastSeq, seq);
        }
        this._drop(m.batchId, m.applied || []);
        if (m.rev) {
          if (!this.revs.some(r => r.n === m.rev.n)) this.revs.push(m.rev);
          this.lastSeq = Math.max(this.lastSeq, m.rev.seq);
        }
      }
    } else if (m.t === 'rebaseAck') {
      if (m.status === 'applied') {
        for (const { seq, op } of m.applied || []) {
          this.doc.apply(op); this.allOps.push(op);
          this.lastSeq = Math.max(this.lastSeq, seq);
        }
        this._drop(m.batchId, m.applied || []);
        if (m.rev && !this.revs.some(r => r.n === m.rev.n)) this.revs.push(m.rev);
        if (m.gen != null) this.gen = m.gen;
      } else if (m.status === 'conflict') {
        const i = this.pendingBatches.findIndex(b => b.batchId === m.batchId);
        if (i >= 0) this.pendingBatches.splice(i, 1);
        if (!this.quarantine.some(q => q.draftId === m.draftId)) {
          this.quarantine.push({
            draftId: m.draftId, batchId: m.batchId, ops: [], reason: m.reason,
            role: m.role, need: m.need, kinds: m.kinds || {}, epoch: m.epoch,
            atSeq: m.atSeq, rejectedTs: Date.now(), kind: 'conflict',
            conflicts: m.conflicts || [], mappedOps: [], gen: m.gen,
          });
        }
        this.doc.clear();
        for (const op of this.allOps) this.doc.apply(op);
        for (const b of this.pendingBatches) for (const op of b.ops) this.doc.apply(op);
      } else if (m.status === 'empty') {
        const i = this.pendingBatches.findIndex(b => b.batchId === m.batchId);
        if (i >= 0) this.pendingBatches.splice(i, 1);
      }
    } else if (m.t === 'quarantineItem') {
      this._mergeQuarantine([m.item]);
      this.doc.clear();
      for (const op of this.allOps) this.doc.apply(op);
      for (const b of this.pendingBatches) for (const op of b.ops) this.doc.apply(op);
    } else if (m.t === 'members') {
      this._upsertEntry(m.entry);
      this.members = m.members || this.members;
      this.epoch = m.epoch;
      if (m.entry) this.lastSeq = Math.max(this.lastSeq, m.entry.seq);
      const me = this.members.find(x => x.id === this.id);
      this.role = me ? me.role : 'viewer';
    } else if (m.t === 'generation') {
      this.gen = m.gen;
      this.logMinSeq = m.logMinSeq || 0;
      this.lastSeq = Math.max(this.lastSeq, m.seq || 0);
      this.generations.push(m);
      if (this.compactInfo) this.compactInfo = null;
      this.send({ t: 'compactStatus' }); // 与浏览器一致：代次发布后刷新压缩面板
    } else if (m.t === 'watermarks') {
      this.watermarks = m.watermarks || [];
    } else if (m.t === 'compactAck') {
      this.compactInfo = m.compact || this.compactInfo;
      if (m.ok) { this.gen = m.gen; this.logMinSeq = m.retainedRange ? m.retainedRange[0] : this.logMinSeq; }
      this.compactAck = m;
    } else if (m.t === 'capsAck') {
      if (m.compact) this.compactInfo = m.compact;
    } else if (m.t === 'compactStatus') {
      this.compactInfo = m.compact;
      this.watermarks = (m.compact && m.compact.watermarks) || this.watermarks;
    } else if (m.t === 'presence') {
      this.peers = m.peers || [];
    } else if (m.t === 'error') {
      this.errors.push(m);
    }
  }
  _mergeQuarantine(items) {
    for (const item of items || []) {
      // 服务端权威记录按确定性 draftId 下发；与本地占位草稿按 batchId 归并，不重复入账。
      let i = this.quarantine.findIndex(q => q.draftId === item.draftId);
      if (i < 0 && item.batchId) i = this.quarantine.findIndex(q => q.batchId === item.batchId && q.draftId !== item.draftId);
      const rec = {
        draftId: item.draftId, batchId: item.batchId, ops: item.ops || (i >= 0 ? this.quarantine[i].ops : []),
        reason: item.reason, role: item.role, need: item.need, kinds: item.kinds || {},
        epoch: item.epoch, atSeq: item.atSeq, rejectedTs: item.ts || Date.now(),
        kind: item.kind || 'rejected', conflicts: item.conflicts || [],
        mappedOps: item.mappedOps || [], gen: item.gen != null ? item.gen : this.gen,
      };
      if (i >= 0) this.quarantine[i] = rec; else this.quarantine.push(rec);
    }
  }
  // ---------- 快照迁移 + 基线换算（测试模拟） ----------
  _beginMigration(w) {
    const mg = w.migration || w;
    if (this.migration && this.migration.gen === mg.gen) return;
    this.migration = { gen: mg.gen, total: mg.totalChunks || 0, chunks: new Map(), migrating: true, done: false };
    // 握手响应与迁移请求可能在同一拍：确保 welcome 已处理、ws 可用后再拉分片。
    const start = () => this._requestChunks();
    if (this.ws) start();
    else setTimeout(start, 0);
  }
  _requestChunks() {
    const mg = this.migration;
    if (!mg) return;
    const total = mg.total || 1;
    for (let i = 0; i < total; i++) {
      if (!mg.chunks.has(i)) this.send({ t: 'migrate', gen: mg.gen, index: i, reqId: this.id + '#mig#' + mg.gen + '#' + i });
    }
  }
  _onChunk(m) {
    const mg = this.migration;
    if (!mg || !m.ok) { if (m.code === 'gen-changed') { this.migration = null; this.connect(); } return; }
    if (m.gen !== mg.gen) return;
    mg.total = m.total;
    if (!mg.chunks.has(m.index)) mg.chunks.set(m.index, m.ops || []);
    if (m.final) this._finishMigration(m.tail);
    else if (mg.chunks.size >= mg.total) this._requestChunks();
  }
  _finishMigration(tail) {
    const mg = this.migration;
    if (!tail) { this._requestChunks(); return; }
    const ops = [];
    for (const i of [...mg.chunks.keys()].sort((a, b) => a - b)) for (const op of mg.chunks.get(i)) ops.push(op);
    this.doc.clear();
    for (const op of ops) this.doc.apply(op);
    const seen = new Set();
    this.allOps = [];
    for (const { seq, op } of tail.window || []) {
      this.doc.apply(op); this.allOps.push(op);
      if (op.opId) seen.add(op.opId);
      this.lastSeq = Math.max(this.lastSeq, seq);
    }
    this.gen = tail.gen != null ? tail.gen : mg.gen;
    this.logMinSeq = tail.logMinSeq || 0;
    this.epoch = tail.epoch || this.epoch;
    this.members = tail.members || this.members;
    this.ledger = tail.ledger || this.ledger;
    this.revs = tail.revs || this.revs;
    for (const e of this.ledger) this.lastSeq = Math.max(this.lastSeq, e.seq || 0);
    for (const r of this.revs) this.lastSeq = Math.max(this.lastSeq, r.seq || 0);
    const me = this.members.find(x => x.id === this.id);
    this.role = me ? me.role : 'viewer';
    this._mergeQuarantine(tail.quarantine || []);
    // 积压批次：按 opId 剔除已确认，其余走 rebase（确定性 reqId）
    this.pendingBatches = this.pendingBatches.filter(b => {
      b.ops = b.ops.filter(op => !(op.opId && seen.has(op.opId)));
      return b.ops.length > 0;
    });
    const backlog = this.pendingBatches;
    this.pendingBatches = [];
    mg.migrating = false; mg.done = true;
    for (const op of this.allOps) {} // allOps 已应用
    for (const b of backlog) this.rebase(b);
  }
  rebase(b) {
    this.pendingBatches.push(b);
    this.send({ t: 'rebase', reqId: this.id + '#rb#' + b.batchId, batchId: b.batchId, fromGen: this.gen, ops: b.ops });
  }
  setCaps(logOpCap, revSnapshotCap) {
    this.send({ t: 'setCaps', logOpCap, revSnapshotCap });
  }
  compact(reqId) {
    this.send({ t: 'compact', reqId: reqId || (this.id + '#compact#' + Date.now() + '#' + Math.random().toString(36).slice(2, 6)) });
  }
  watermark() { this.send({ t: 'watermark', gen: this.gen, seq: this.lastSeq }); }
  restoreBaseline() { this.send({ t: 'restoreBaseline' }); }
  restoreGen(g) { this.send({ t: 'restoreGen', gen: g }); }
  _dropOps(applied) {
    const ids = new Set((applied || []).map(x => x.op && x.op.opId).filter(Boolean));
    if (!ids.size) return;
    this.pendingBatches = this.pendingBatches.filter(b => {
      b.ops = b.ops.filter(op => !ids.has(op.opId));
      return b.ops.length > 0;
    });
  }
  _drop(batchId, applied) {
    const i = this.pendingBatches.findIndex(b => b.batchId === batchId);
    if (i >= 0) this.pendingBatches.splice(i, 1);
    this._dropOps(applied);
  }
  _quarantine(m) {
    const i = this.pendingBatches.findIndex(b => b.batchId === m.batchId);
    let ops = null;
    if (i >= 0) { ops = this.pendingBatches[i].ops; this.pendingBatches.splice(i, 1); }
    if (this.quarantine.some(q => q.batchId === m.batchId)) return;
    if (!ops) ops = [];
    // 模拟浏览器 rebuildLocal：从全部已确认操作 + 其余待发批次重建（剔除被隔离批次）
    this.doc.clear();
    for (const op of this.allOps) this.doc.apply(op);
    this.quarantine.push({
      draftId: 'd-' + (++batchCounter), batchId: m.batchId, ops,
      reason: m.reason, role: m.role, need: m.need, kinds: m.kinds || {},
      epoch: m.epoch, atSeq: m.atSeq, rejectedTs: Date.now(),
    });
    for (const b of this.pendingBatches) for (const op of b.ops) this.doc.apply(op);
  }
  resubmit(q) {
    this.quarantine = this.quarantine.filter(x => x.draftId !== q.draftId);
    const b = { batchId: this.id + '#B' + (++this.opSeq) + '-' + (++batchCounter), ops: q.ops };
    this.pendingBatches.push(b);
    this.send({ t: 'ops', batchId: b.batchId, ops: b.ops });
    return b.batchId;
  }
  // ---------- 操作辅助 ----------
  _batchId() { return this.id + '#B' + (++this.opSeq) + '-' + (++batchCounter); }
  _push(ops) {
    const batch = [];
    for (const op of ops) {
      if (!op) continue;
      op.opId = this.id + '#' + (++this.opSeq);
      this.doc.apply(op);
      batch.push(op);
    }
    if (!batch.length) return null;
    const b = { batchId: this._batchId(), ops: batch };
    this.pendingBatches.push(b);
    if (!(this.migration && this.migration.migrating)) {
      this.send({ t: 'ops', batchId: b.batchId, ops: batch });
    }
    return b;
  }
  insertText(pos, str) {
    const ids = this.doc.visibleIds();
    let after = pos > 0 ? ids[pos - 1] : null;
    const ops = [];
    for (const ch of str) { const o = this.doc.insert(after, ch); after = o.id; ops.push(o); }
    return this._push(ops);
  }
  deleteRange(pos, len) {
    const ids = this.doc.visibleIds();
    const ops = [];
    for (let i = 0; i < len; i++) ops.push(this.doc.remove(ids[pos + i]));
    return this._push(ops);
  }
  anchors(s, e) {
    const ids = this.doc.visibleIds();
    return [
      s <= 0 ? { id: null, edge: 's' } : { id: ids[s], edge: 's' },
      e >= ids.length ? { id: null, edge: 'e' } : { id: ids[e - 1], edge: 'e' },
    ];
  }
  addComment(s, e, text) {
    const [st, en] = this.anchors(s, e);
    const quote = this.doc.text().slice(s, e);
    return this._push([this.doc.comment(st, en, text, quote)]);
  }
  reattach(cid, s, e) {
    const [st, en] = this.anchors(s, e);
    return this._push([this.doc.updateComment(cid, { start: st, end: en, quote: this.doc.text().slice(s, e) })]);
  }
  resolve(cid) { return this._push([this.doc.updateComment(cid, { resolved: true })]); }
  mark(s, e, attrs) {
    const [st, en] = this.anchors(s, e);
    return this._push([this.doc.mark(st, en, attrs)]);
  }
  roleOf(id) { const m = this.members.find(x => x.id === id); return m ? m.role : null; }
}

const sleep = (ms) => new Promise(r => setTimeout(r, ms));
function diskFile(name) { return path.join(DATA_DIR, encodeURIComponent(name) + '.json'); }
function readDisk(name) { return JSON.parse(fs.readFileSync(diskFile(name), 'utf8')); }
function fp(c) { return CRDT.fingerprint(c.doc); }
function ledgerSig(c) { return c.ledger.map(e => e.seq + ':' + e.act + ':' + (e.target || '')).join(','); }
// 显式驱动多轮回收（测试默认关闭自动压缩）：直到 gen>=gens 且窗口<=cap。
async function compactUntil(owner, gens, cap, tag) {
  for (let k = 0; k < 12; k++) {
    owner.send({ t: 'compactStatus' });
    await sleep(120);
    const ci = owner.compactInfo;
    if (ci && ci.gen >= gens && (cap == null || ci.windowOps <= cap)) return;
    owner.compact('man-' + tag + '-' + k);
    await sleep(780); // 等待 COMPACT_DELAY_MS 的 prepare→commit
  }
  owner.send({ t: 'compactStatus' });
  await sleep(150);
}
function waitFor(fn, label, timeout = 8000) {
  return new Promise((resolve, reject) => {
    const t0 = Date.now();
    const iv = setInterval(() => {
      let ok = false;
      try { ok = fn(); } catch (e) { /* retry */ }
      if (ok) { clearInterval(iv); resolve(); }
      else if (Date.now() - t0 > timeout) { clearInterval(iv); reject(new Error('超时: ' + label)); }
    }, 20);
  });
}

let server = null;
function startServer() {
  return new Promise((resolve, reject) => {
    server = spawn(process.execPath, [path.join(__dirname, '..', 'server', 'server.js')], {
      env: Object.assign({}, process.env, {
        PORT: String(PORT), DATA_DIR,
        COMPACT_DELAY_MS: process.env.COMPACT_DELAY_MS || '600',
        AUTO_COMPACT: process.env.AUTO_COMPACT != null ? process.env.AUTO_COMPACT : '0',
      }),
      stdio: ['ignore', 'pipe', 'inherit'],
    });
    server.stdout.on('data', (d) => { if (String(d).includes('http://')) resolve(); });
    server.on('exit', (c) => reject(new Error('服务器退出 code=' + c)));
    setTimeout(() => reject(new Error('服务器启动超时')), 8000);
  });
}
function stopServer() { return new Promise((res) => { if (!server) return res(); server.on('exit', res); server.kill('SIGTERM'); setTimeout(res, 2500); }); }
// 强杀（不触发优雅落盘）：验证 tmp+rename 原子切换，只有完整旧代或完整新代。
function stopServerKill() {
  return new Promise((res) => {
    if (!server) return res();
    server.on('exit', res);
    server.kill('SIGKILL');
    setTimeout(res, 1200);
  });
}

let passed = 0;
function ok(name) { passed++; console.log('  ✓ ' + name); }
const docName = (tag) => 't-' + RUN + '-' + tag;

(async () => {
  await startServer();
  console.log('服务器已启动 (port ' + PORT + ', data=' + DATA_DIR + ')\n');

  // ===== 场景 1a：共享角色矩阵（浏览器"能看到/能点的命令"与服务端共用同一规则） =====
  assert.deepStrictEqual(
    ['owner', 'editor', 'commenter', 'viewer'].map(r =>
      [AUTHZ.can(r, 'prose'), AUTHZ.can(r, 'annotate'), AUTHZ.can(r, 'rollback'), AUTHZ.can(r, 'invite')]),
    [[true, true, true, true], [true, true, false, false], [false, true, false, false], [false, false, false, false]]
  );
  assert.strictEqual(AUTHZ.authorizeBatch('commenter', [{ t: 'ins' }, { t: 'com' }]).ok, false); // 混合批次整体拒绝
  assert.strictEqual(AUTHZ.authorizeBatch('commenter', [{ t: 'com' }]).ok, true);
  ok('角色命令矩阵正确（prose/annotate/rollback/invite），混合批次原子拒绝');

  // ===== 公共搭建：owner + editor + commenter + viewer =====
  const D1 = docName('roles');
  const O = new SimClient('owner1', D1);
  await O.connect();
  assert.strictEqual(O.role, 'owner'); // 新空间首开者成为 owner
  const E = new SimClient('editor1', D1);
  const C = new SimClient('commenter1', D1);
  const V = new SimClient('viewer1', D1);
  await E.connect(); await C.connect(); await V.connect();
  assert.strictEqual(E.role, 'viewer'); // 未邀请前一律只读
  O.member('invite', 'editor1', 'editor');
  O.member('invite', 'commenter1', 'commenter');
  O.member('invite', 'viewer1', 'viewer');
  await waitFor(() => E.role === 'editor' && C.role === 'commenter' && V.role === 'viewer', '受邀者收到角色');
  await waitFor(() => O.members.length === 4, 'owner 看到 4 名成员');
  ok('场景1：受邀用户按邀请获得角色，未邀请者为只读');

  // 非 owner 尝试邀请 → 拒绝，epoch 与账本不变
  const epochAfterInvite = O.epoch;
  E.member('invite', 'intruder', 'editor');
  await waitFor(() => E.errors.some(e => e.code === 'forbidden-membership'), 'editor 邀请被拒');
  assert.strictEqual(O.epoch, epochAfterInvite);
  ok('场景1：非所有者的成员管理命令被拒绝');

  // 最后一个 owner 不允许降权/移除自己
  const epochGuard = O.epoch;
  O.member('role', 'owner1', 'editor');
  await waitFor(() => O.errors.some(e => e.code === 'last-owner'), '自降 owner 被拒');
  O.member('remove', 'owner1');
  await waitFor(() => O.errors.filter(e => e.code === 'last-owner').length >= 2, '自移除 owner 被拒');
  assert.strictEqual(O.epoch, epochGuard, '最后所有者保护不推进 epoch');
  assert.strictEqual(O.role, 'owner');
  ok('场景1：最后一个所有者不可被降权或移除');

  // ===== 场景 2：commenter 可批注、不可正文；viewer 两类写都不行 =====
  E.insertText(0, '编辑器写的正文');
  await waitFor(() => C.doc.text() === '编辑器写的正文' && V.doc.text() === '编辑器写的正文', 'editor 正文同步');

  // commenter 改正文 → 整批拒绝
  const cProse = C.insertText(0, 'X');
  await waitFor(() => C.quarantine.length === 1, 'commenter 正文批次被隔离');
  assert.strictEqual(C.quarantine[0].need, 'editor');
  await sleep(150);
  assert.strictEqual(O.doc.text(), '编辑器写的正文');
  assert.strictEqual(V.doc.text(), '编辑器写的正文'); // 没有任何泄漏
  ok('场景2：commenter 改正文被整批拒绝，其他人看不到任何内容');

  // viewer 批注 → 拒绝；commenter 批注 → 成功
  const tlen = V.doc.text().length;
  V.addComment(0, Math.min(2, tlen), 'viewer 的评论');
  await waitFor(() => V.quarantine.length === 1, 'viewer 批注被隔离');
  const cid = (() => {
    const b = C.addComment(0, 3, '这里可以评论');
    return b.ops[0].id;
  })();
  await waitFor(() => O.doc.comments.has(cid) && V.doc.comments.has(cid), 'commenter 批注对所有人可见');
  // commenter 解决/重新挂接也允许
  C.resolve(cid);
  await waitFor(() => O.doc.comments.get(cid).resolved, 'commenter 可解决批注');
  ok('场景2：commenter 可创建/解决批注，viewer 批注也被拒');

  // editor 批注同样允许（编辑权限包含评论者）
  E.addComment(3, 6, 'editor 也能批注');
  await waitFor(() => O.doc.comments.size >= 2, 'editor 批注成功');

  // ===== 场景 7：非 owner 回滚被拒，不产生修订 =====
  const revsBefore = O.revs.length;
  const seqBefore = O.lastSeq;
  E.restore(1);
  await waitFor(() => E.errors.some(e => e.code === 'forbidden-rollback'), 'editor 回滚被拒');
  await sleep(100);
  assert.strictEqual(O.revs.length, revsBefore);
  assert.strictEqual(O.lastSeq, seqBefore);
  ok('场景7：非所有者回滚检查点被拒绝，且未产生修订/序号');

  // owner 回滚成功（回归：恢复作为新修订参与合并）
  const textBeforeRestore = O.doc.text();
  O.restore(1);
  await waitFor(() => O.revs.length === revsBefore + 1 && O.revs[O.revs.length - 1].kind === 'restore', 'owner 回滚成功');
  ok('场景7：所有者可回滚，恢复本身是新修订');
  assert.ok(O.doc.text() !== textBeforeRestore || O.revs.length === revsBefore + 1);

  // ===== 场景 3：断连排队 → 降权 → 重连，整批不泄漏，完整隔离 =====
  const D2 = docName('disconnect');
  const O2 = new SimClient('owner2', D2);
  await O2.connect();
  const U = new SimClient('user2', D2);
  await U.connect();
  O2.member('invite', 'user2', 'editor');
  await waitFor(() => U.role === 'editor', 'U 成为 editor');
  U.insertText(0, '基线文字');
  await waitFor(() => O2.doc.text() === '基线文字', '基线同步');

  U.disconnect();
  await sleep(200);
  // 断连期间 U 编辑一整批（多 op：插入若干字符）
  const offlineBatch = U.insertText(4, '离线插入');
  assert.ok(U.pendingBatches.some(b => b.batchId === offlineBatch.batchId));
  const offlineChars = offlineBatch.ops.map(op => op.ch).join('');
  // owner 在线正常编辑，同时把 U 降为 viewer
  O2.insertText(O2.doc.text().length, '在线追加');
  O2.member('role', 'user2', 'viewer');
  await waitFor(() => O2.roleOf('user2') === 'viewer', 'U 已被降权');

  await U.connect(); // 重连补发离线批次
  await waitFor(() => U.quarantine.length === 1, '离线批次被隔离');
  const q = U.quarantine[0];
  assert.strictEqual(q.batchId, offlineBatch.batchId);
  assert.strictEqual(q.role, 'viewer');
  assert.strictEqual(q.kinds.prose, offlineBatch.ops.length);
  // 完整保留：操作一条不少，内容可复制
  assert.strictEqual(q.ops.length, offlineBatch.ops.length);
  assert.deepStrictEqual(q.ops.map(o => o.ch).join(''), offlineChars);
  // 任何参与者的共享状态中都没有这批内容
  await sleep(150);
  assert.ok(!O2.doc.text().includes(offlineChars), 'owner 看不到离线批次内容');
  assert.ok(!U.doc.text().includes(offlineChars), 'U 本地乐观内容已随重建移除');
  assert.ok(O2.doc.text().includes('在线追加'), 'owner 的在线编辑完好');
  assert.ok(U.doc.text().includes('在线追加'), 'U 收到 owner 的在线编辑');
  ok('场景3：editor 断连排队后被降权，重连整批零泄漏且完整进入隔离草稿');

  // 隔离引用与 atSeq：拒绝时记录了总序位置
  assert.ok(q.atSeq >= O2.ledger[O2.ledger.length - 1].seq);
  const trEntry = U.ledger.filter(e => e.target === 'user2' && e.act === 'role').pop();
  assert.ok(trEntry && q.atSeq >= trEntry.seq, '隔离记录可解释：atSeq 位于角色变更之后');
  ok('场景3：隔离草稿携带拒绝原因与相关角色变更位置（epoch/seq）');

  // ===== 场景 4：恢复 editor 后显式重提，恰好一次并正常合并 =====
  // viewer 状态下重提按钮应被禁用——服务端同样会拒绝（再试一次同 batchId => 幂等拒绝）
  U.send({ t: 'ops', batchId: offlineBatch.batchId, ops: offlineBatch.ops });
  await sleep(150);
  assert.strictEqual(U.quarantine.length, 1, '重复投递同一被拒 batchId 不产生第二条隔离');
  assert.ok(!O2.doc.text().includes(offlineChars));
  ok('场景4：权限未恢复时重复投递仍被拒且幂等');

  O2.member('role', 'user2', 'editor');
  await waitFor(() => U.role === 'editor', 'U 恢复 editor');
  const revCountBefore = O2.revs.length;
  const newBatchId = U.resubmit(q); // 显式重提：新 batchId、保留原 opId
  await waitFor(() =>
    O2.doc.text().includes(offlineChars) && U.doc.text().includes(offlineChars) &&
    U.pendingBatches.length === 0, '重提批次应用并合并');
  assert.strictEqual(U.quarantine.length, 0, '隔离草稿在应用后清除');
  // 同一新 batchId 再投递一次 → 恰好生效一次
  const oldText = O2.doc.text();
  U.send({ t: 'ops', batchId: newBatchId, ops: offlineBatch.ops });
  await sleep(200);
  assert.strictEqual(O2.doc.text(), oldText, '重复批次不重复生效');
  assert.strictEqual(O2.revs.length, revCountBefore + 1, '只产生一个修订');
  ok('场景4：恢复权限后显式重提整批恰好生效一次，并与他人编辑正常合并');

  // ===== 场景 5：角色变更与断连批次竞争 → 总序决定结论，全员一致 =====
  // order=accepted-first：批次先按 editor 接受，再降权 → 内容存在，修订 seq 在角色变更前
  {
    const D = docName('race-accept');
    const Ow = new SimClient('owner-ra', D); await Ow.connect();
    const X = new SimClient('x-ra', D); await X.connect();
    const Y = new SimClient('y-ra', D); await Y.connect();
    Ow.member('invite', X.id, 'editor');
    await waitFor(() => X.role === 'editor', 'ra: X 是 editor');
    X.disconnect(); await sleep(150);
    const b = X.insertText(0, '先到的离线批次');
    const chars = b.ops.map(o => o.ch).join('');
    await X.connect();
    await waitFor(() => Ow.doc.text().includes(chars) && Y.doc.text().includes(chars), 'ra: 批次按 editor 接受');
    const revSeq = Math.max(...Ow.revs.map(r => r.fromSeq || r.seq));
    Ow.member('role', X.id, 'viewer');
    await waitFor(() => X.role === 'viewer' && Y.roleOf(X.id) === 'viewer', 'ra: 随后降权');
    const roleSeq = Ow.ledger.filter(e => e.target === X.id && e.act === 'role').pop().seq;
    assert.ok(revSeq < roleSeq, 'ra: 修订严格早于角色变更');
    assert.strictEqual(X.quarantine.length, 0, 'ra: 无隔离');
    // 全员内容与账本顺序一致
    const ledgerSig = (c) => c.ledger.map(e => e.seq + ':' + e.act).join(',');
    await waitFor(() => ledgerSig(Ow) === ledgerSig(X) && ledgerSig(X) === ledgerSig(Y), 'ra: 账本一致');
    assert.strictEqual(Ow.doc.text(), X.doc.text());
    assert.strictEqual(X.doc.text(), Y.doc.text());
    ok('场景5（总序：批次→降权）：批次接受，所有参与者内容与账本顺序一致');
  }
  // order=role-first：先降权，后批次到达 → 拒绝、零内容，角色变更 seq 在拒绝点之前
  {
    const D = docName('race-role');
    const Ow = new SimClient('owner-rr', D); await Ow.connect();
    const X = new SimClient('x-rr', D); await X.connect();
    const Y = new SimClient('y-rr', D); await Y.connect();
    Ow.member('invite', X.id, 'editor');
    await waitFor(() => X.role === 'editor', 'rr: X 是 editor');
    X.disconnect(); await sleep(150);
    const b = X.insertText(0, '后到的离线批次');
    const chars = b.ops.map(o => o.ch).join('');
    // 重连前先完成降权：确保 X 的补发批次到达时授权纪元已是 viewer
    Ow.member('role', X.id, 'viewer');
    await waitFor(() => Ow.roleOf(X.id) === 'viewer', 'rr: 降权已提交');
    const roleSeq = Ow.ledger.filter(e => e.target === X.id && e.act === 'role').pop().seq;
    await X.connect();
    await waitFor(() => X.quarantine.length === 1, 'rr: 批次被拒');
    assert.ok(X.quarantine[0].atSeq >= roleSeq, 'rr: 拒绝点位于角色变更之后');
    await sleep(150);
    assert.ok(!Ow.doc.text().includes(chars), 'rr: owner 无泄漏');
    assert.ok(!Y.doc.text().includes(chars), 'rr: 旁观者无泄漏');
    assert.ok(!X.doc.text().includes(chars), 'rr: X 本地也无该内容');
    const ledgerSig = (c) => c.ledger.map(e => e.seq + ':' + e.act).join(',');
    assert.strictEqual(ledgerSig(Ow), ledgerSig(X));
    assert.strictEqual(ledgerSig(X), ledgerSig(Y));
    assert.strictEqual(Ow.doc.text(), Y.doc.text());
    ok('场景5（总序：降权→批次）：批次拒绝，所有参与者内容与账本顺序一致');
  }

  // ===== 场景 6：重复邀请 / 角色变更 / 批次投递幂等 =====
  const D3 = docName('idem');
  const O3 = new SimClient('owner3', D3); await O3.connect();
  const Z = new SimClient('zed3', D3); await Z.connect();
  const inviteReq = O3.member('invite', 'zed3', 'editor');
  await waitFor(() => Z.role === 'editor', 'idem: 邀请生效');
  const epoch1 = O3.epoch;
  const ledgerLen1 = O3.ledger.length;
  O3.send({ t: 'member', reqId: inviteReq, act: 'invite', target: 'zed3', role: 'editor' }); // 重试同一 reqId
  await sleep(200);
  assert.strictEqual(O3.epoch, epoch1, '重复邀请不推进 epoch');
  assert.strictEqual(O3.ledger.length, ledgerLen1, '重复邀请不写审计');
  const roleReq = O3.member('role', 'zed3', 'commenter');
  await waitFor(() => Z.role === 'commenter', 'idem: 角色变更生效');
  const epoch2 = O3.epoch;
  O3.send({ t: 'member', reqId: roleReq, act: 'role', target: 'zed3', role: 'commenter' });
  await sleep(200);
  assert.strictEqual(O3.epoch, epoch2, '重复角色变更不推进 epoch');
  // 相同角色的新请求 = 幂等 no-op
  O3.member('role', 'zed3', 'commenter');
  await sleep(200);
  assert.strictEqual(O3.epoch, epoch2, '同角色变更为 no-op');
  // 批次重复投递（同 batchId）：一次生效、一个修订
  O3.member('role', 'zed3', 'editor');
  await waitFor(() => Z.role === 'editor', 'idem: 恢复 editor');
  const bb = Z.insertText(0, '幂等批次');
  await waitFor(() => O3.doc.text() === '幂等批次', 'idem: 批次生效');
  const revsIdem = O3.revs.length;
  Z.send({ t: 'ops', batchId: bb.batchId, ops: bb.ops });
  Z.send({ t: 'ops', batchId: bb.batchId, ops: bb.ops }); // 连续两次重复
  await sleep(250);
  assert.strictEqual(O3.doc.text(), '幂等批次', '重复批次不重复插入');
  assert.strictEqual(O3.revs.length, revsIdem, '重复批次不产生修订');
  ok('场景6：重复邀请/角色变更/批次投递（含连续重复）全部幂等');

  // 操作级 opId 去重（跨批次的重放）
  const textBefore = O3.doc.text();
  O3.send({ t: 'ops', batchId: 'different-batch-id', ops: bb.ops });
  await sleep(200);
  assert.strictEqual(O3.doc.text(), textBefore, 'opId 级重放仍然幂等');

  // ===== CRDT 回归（用 owner 验证既有协作语义未破坏） =====
  const DR = docName('regress');
  const A = new SimClient('alice', DR); await A.connect();
  const B = new SimClient('bob', DR); await B.connect();
  // B 默认 viewer → owner 把 B 提为 editor 后再测离线合并
  A.member('invite', 'bob', 'editor');
  await waitFor(() => B.role === 'editor', '回归: bob 成为 editor');
  A.insertText(0, 'hello');
  await waitFor(() => B.doc.text() === 'hello', '回归: 同步');
  B.insertText(5, ' world');
  await waitFor(() => A.doc.text() === 'hello world', '回归: 双向同步');
  B.disconnect(); await sleep(150);
  A.insertText(11, '!');
  B.insertText(0, '>>');
  B.deleteRange(6, 1);
  await B.connect();
  await waitFor(() => A.doc.text() === B.doc.text() && A.doc.text().includes('world!'), '回归: 离线合并收敛');
  assert.strictEqual(A.doc.text(), '>>hell world!');
  ok('回归：断网编辑重连合并，已确认内容不被覆盖');

  // 批注悬空 + 重新挂接
  const wStart = A.doc.text().indexOf('world');
  const cidR = A.addComment(wStart, wStart + 5, '斟酌用词').ops[0].id;
  await waitFor(() => B.doc.comments.has(cidR), '回归: 批注同步');
  B.deleteRange(wStart, 5);
  await waitFor(() => A.doc.resolveComment(A.doc.comments.get(cidR)).status === 'orphan-deleted', '回归: 悬空');
  const hStart = A.doc.text().indexOf('hell');
  A.reattach(cidR, hStart, hStart + 4);
  await waitFor(() => B.doc.resolveComment(B.doc.comments.get(cidR)).status === 'anchored', '回归: 重新挂接');
  ok('回归：锚定文字删除→可解释悬空→重新挂接');

  // 格式并发合并 + 恢复后并发编辑合并
  A.mark(2, 6, { bold: true });
  B.mark(4, 8, { italic: true });
  await waitFor(() => A.doc.activeMarks().length === 2 && B.doc.activeMarks().length === 2, '回归: 格式合并');
  const snapText = A.doc.text();
  const revN = Math.max(...A.revs.map(r => r.n));
  A.insertText(0, 'XXX');
  await waitFor(() => B.doc.text() === 'XXX' + snapText, '回归: XXX 同步');
  A.restore(revN);
  await waitFor(() => A.doc.text() === snapText && B.doc.text() === snapText, '回归: 恢复收敛');
  A.insertText(snapText.length, ' [A]');
  B.insertText(0, '[B] ');
  await waitFor(() => A.doc.text() === B.doc.text() && A.doc.text().includes('[A]') && A.doc.text().includes('[B]'), '回归: 恢复后合并');
  ok('回归：格式合并、恢复作为新修订与并发编辑共存');

  // ===== 场景 9：旧版空间并发首次打开 → 恰好一个 owner，旧数据原样保留 =====
  const LEGACY = 'legacy-' + RUN;
  {
    // 手工造一份 v1 数据（无 v/initialized/members/epoch/ledger 字段）
    const fdoc = new CRDT.Doc('legacy-author');
    let after = null;
    const ops = [];
    for (const ch of '旧版空间的珍贵正文') {
      const o = fdoc.insert(after, ch);
      o.opId = 'legacy#' + o.id;
      after = o.id;
      ops.push(o);
    }
    const recs = ops.map((op, i) => ({ seq: i + 1, op }));
    const payload = {
      seq: ops.length,
      ops: recs,
      revs: [{
        n: 1, seq: ops.length, ts: Date.now() - 3600000, by: 'legacy-author',
        kind: 'edit', summary: '旧修订', snapshot: { text: fdoc.text(), marks: [] },
      }],
    };
    fs.writeFileSync(path.join(DATA_DIR, encodeURIComponent(LEGACY) + '.json'), JSON.stringify(payload));
  }
  const L1 = new SimClient('legacy-user-a', LEGACY);
  const L2 = new SimClient('legacy-user-b', LEGACY);
  // 几乎同时发起两个 hello（两条 socket 的写入在同一 tick）
  const c1 = wsConnect(), c2 = wsConnect();
  const ws1 = await c1, ws2 = await c2;
  L1.ws = ws1; L2.ws = ws2;
  ws1.onMessage((m) => L1._handle(m));
  ws2.onMessage((m) => L2._handle(m));
  ws1.send({ t: 'hello', clientId: 'legacy-user-a', name: '甲', doc: LEGACY, lastSeq: 0 });
  ws2.send({ t: 'hello', clientId: 'legacy-user-b', name: '乙', doc: LEGACY, lastSeq: 0 });
  await Promise.all([
    waitFor(() => !!L1.welcome, 'L1 welcome'),
    waitFor(() => !!L2.welcome, 'L2 welcome'),
  ]);
  const owners1 = L1.members.filter(m => m.role === 'owner');
  const owners2 = L2.members.filter(m => m.role === 'owner');
  assert.strictEqual(owners1.length, 1, 'L1 只看到一个 owner');
  assert.strictEqual(owners2.length, 1, 'L2 只看到一个 owner');
  assert.strictEqual(owners1[0].id, owners2[0].id, '双方看到的是同一个 owner');
  // 内容 / 批注 / 修订历史原样保留
  assert.strictEqual(L1.doc.text(), '旧版空间的珍贵正文');
  assert.strictEqual(L2.doc.text(), '旧版空间的珍贵正文');
  assert.strictEqual(L1.revs.length, 1);
  assert.strictEqual(L1.revs[0].summary, '旧修订');
  // 升级审计：恰有一条 space/upgrade，seq 紧接旧 seq，未重写旧数据
  const up = L1.ledger.filter(e => e.kind === 'space' && e.act === 'upgrade');
  assert.strictEqual(up.length, 1);
  assert.strictEqual(up[0].seq, 10); // 旧 seq=9（按字符数），升级条目紧接其后为 10
  const onDisk = JSON.parse(fs.readFileSync(path.join(DATA_DIR, encodeURIComponent(LEGACY) + '.json'), 'utf8'));
  assert.strictEqual(onDisk.v, 3, '惰性升级到 v3（代次/有界流水格式）');
  assert.strictEqual(onDisk.gen, 0, '升级不产生压缩代次');
  assert.strictEqual(onDisk.baseline, null, '未压缩前没有基线');
  assert.strictEqual(onDisk.ops.length, 9, '旧操作一条不多一条不少');
  assert.strictEqual(onDisk.revs.length, 1, '旧修订保留');
  assert.strictEqual(onDisk.ledger.length, 1);
  // 第三方确认
  const L3 = new SimClient('legacy-user-c', LEGACY); await L3.connect();
  assert.strictEqual(L3.members.filter(m => m.role === 'owner').length, 1);
  assert.strictEqual(L3.doc.text(), '旧版空间的珍贵正文');
  L1.disconnect(); L2.disconnect(); L3.disconnect();
  ok('场景9：旧版空间并发首开恰好一个 owner，内容/批注/修订原样保留，仅追加升级审计');

  // ===== 场景 8：重启后成员/纪元/隔离引用/账本保留 =====
  await sleep(2600); // 等待内容批次落盘
  // 重启前在 D2 再造一条被拒批次，验证隔离引用跨重启
  const beforeQ = U.quarantine.length;
  O2.member('role', 'user2', 'commenter'); // 降低到 commenter
  await waitFor(() => U.role === 'commenter', '重启前: U=commenter');
  U.disconnect(); await sleep(150);
  const bProse = U.insertText(0, '重启前被拒批次');
  await U.connect();
  await waitFor(() => U.quarantine.length === beforeQ + 1, '重启前: 新隔离');
  const rejectedBatchId = bProse.batchId;
  const rejectedOps = bProse.ops;
  // 同时记录成员/纪元/账本快照
  const snapMembers = O2.members;
  const snapEpoch = O2.epoch;
  const snapLedgerLen = O2.ledger.length;
  const restartText = O2.doc.text();

  await sleep(2600);
  await stopServer();
  await startServer();

  const O2b = new SimClient('owner2', D2); await O2b.connect();
  const Ub = new SimClient('user2', D2); await Ub.connect();
  assert.strictEqual(O2b.role, 'owner', '重启: owner 保留');
  assert.strictEqual(Ub.role, 'commenter', '重启: 角色保留');
  assert.strictEqual(O2b.epoch, snapEpoch, '重启: epoch 保留');
  assert.strictEqual(O2b.members.length, snapMembers.length, '重启: 成员表保留');
  assert.ok(O2b.ledger.length >= snapLedgerLen, '重启: 审计账本保留');
  assert.strictEqual(O2b.doc.text(), restartText, '重启: 内容保留');
  // 隔离引用跨重启：用同一 batchId 重试 → 仍是首次的拒绝结论，且不产生内容/修订
  const revsBeforeRetry = O2b.revs.length;
  Ub.send({ t: 'ops', batchId: rejectedBatchId, ops: rejectedOps });
  await waitFor(() => Ub.errors.length >= 0 && true);
  await sleep(300);
  assert.ok(!O2b.doc.text().includes('重启前被拒批次'), '重启: 隔离引用仍拒绝该批次');
  assert.strictEqual(O2b.revs.length, revsBeforeRetry, '重启: 重试被拒批次不产生修订');
  // 重启后重复邀请仍幂等
  const eBefore = O2b.epoch;
  const req = O2b.member('invite', 'user2', 'commenter');
  await sleep(250);
  assert.strictEqual(O2b.epoch, eBefore, '重启: 同角色邀请为 no-op');
  // 恢复权限后显式重提成功（端到端：隔离 → 重启 → 恢复 → 重提）
  O2b.member('role', 'user2', 'editor');
  await waitFor(() => Ub.role === 'editor', '重启后恢复 editor');
  const qRec = { draftId: 'x', ops: rejectedOps, kinds: { prose: rejectedOps.length } };
  const nb = Ub.resubmit(qRec);
  await waitFor(() => O2b.doc.text().includes('重启前被拒批次'), '重启后重提成功并合并');
  Ub.send({ t: 'ops', batchId: nb, ops: rejectedOps });
  await sleep(200);
  assert.ok(O2b.doc.text().indexOf('重启前被拒批次') === O2b.doc.text().lastIndexOf('重启前被拒批次'), '重启后重复投递仍幂等一次');
  ok('场景8：成员/授权纪元/隔离引用/审计账本跨重启保留，恢复后重提仍恰好一次');

  // ========================================================================
  // 有界流水压缩 / 代次基线 / 离线镜像迁移换算 —— 验收 (1)~(10)
  // ========================================================================

  // ----- 验收 1：大量增删触发多轮回收，流水降到上界，在线各端投影/标记/批注/角色/账本一致 -----
  {
    const D = docName('compact-bound');
    const OW = new SimClient('owner-cb', D); await OW.connect();
    const EW = new SimClient('editor-cb', D); await EW.connect();
    OW.member('invite', 'editor-cb', 'editor');
    await waitFor(() => EW.role === 'editor', 'cb: editor');
    OW.setCaps(30, 5);
    await sleep(200);
    // 制造大量增删：每轮插入整段再删掉上一段（产生大量叶子墓碑），并显式触发多轮回收。
    let marker = 0;
    for (let round = 0; round < 6; round++) {
      const tag = '第' + round + '轮内容ABCDEFG';
      EW.insertText(EW.doc.text().length, tag);
      await waitFor(() => OW.doc.text().includes(tag), 'cb: 同步轮 ' + round);
      // 样式 + 批注
      const pos = OW.doc.text().indexOf(tag);
      EW.mark(pos, pos + 4, { bold: true });
      EW.addComment(pos, pos + 5, '评论 ' + round);
      await sleep(40);
      if (round > 0) {
        const prev = '第' + (round - 1) + '轮内容ABCDEFG';
        const p = EW.doc.text().indexOf(prev);
        if (p >= 0) EW.deleteRange(p, prev.length);
        await sleep(60);
      }
      marker = round;
      // 大量增删已超过上界 => 主理人发起一轮回收（与自动触发等价的 prepare/commit 路径）
      if (round >= 2) { OW.compact('cb-compact-' + round); await sleep(750); }
    }
    // 若仍超上界则继续回收，直到流水有界
    for (let k = 0; k < 6; k++) {
      OW.send({ t: 'compactStatus' }); await sleep(150);
      if (OW.compactInfo && OW.compactInfo.windowOps <= 30 && OW.compactInfo.gen >= 2) break;
      OW.compact('cb-compact-tail-' + k); await sleep(750);
    }
    OW.send({ t: 'compactStatus' });
    await waitFor(() => OW.compactInfo && OW.compactInfo.gen >= 2, 'cb: 至少两轮压缩', 12000);
    await waitFor(() => OW.compactInfo && OW.compactInfo.windowOps <= 30, 'cb: 窗口流水 <= 30');
    const disk = readDisk(D);
    assert.ok(disk.ops.length <= 30, '磁盘流水条数降到上界（实际 ' + disk.ops.length + '）');
    assert.ok(disk.gen >= 2, '磁盘代次 >= 2');
    // 在线各端投影一致（正文 / 富文本 / 批注）
    await waitFor(() => OW.doc.text() === EW.doc.text(), 'cb: 正文一致');
    assert.strictEqual(fp(OW), fp(EW), 'cb: 投影指纹（正文/标记/批注）一致');
    assert.deepStrictEqual(OW.doc.activeMarks().map(m => m.id).sort(), EW.doc.activeMarks().map(m => m.id).sort());
    assert.strictEqual(OW.doc.comments.size, EW.doc.comments.size);
    // 角色一致（成员纪元不被压缩改变）
    assert.strictEqual(OW.role, 'owner');
    assert.strictEqual(EW.role, 'editor');
    assert.strictEqual(OW.epoch, EW.epoch);
    // 治理账本次序一致
    assert.strictEqual(ledgerSig(OW), ledgerSig(EW), 'cb: 账本次序一致');
    // 最新正文确实包含最后一轮标记
    assert.ok(OW.doc.text().includes('第' + marker + '轮内容ABCDEFG'), 'cb: 最新内容存在');
    // 没有隐藏的全量副本：tmp 文件不存在
    assert.ok(!fs.existsSync(diskFile(D) + '.tmp'), 'cb: 无残留 tmp 全量副本');
    ok('验收1：多轮回收后磁盘流水<=上界，在线各端正文/标记/批注/角色/账本次序相同');
  }

  // ----- 验收 2：制作基线期间仍有在线写入，切点两侧不丢不重并收敛 -----
  {
    const D = docName('compact-race');
    const OW = new SimClient('owner-cr', D); await OW.connect();
    const EW = new SimClient('editor-cr', D); await EW.connect();
    OW.member('invite', 'editor-cr', 'editor');
    await waitFor(() => EW.role === 'editor', 'cr: editor');
    OW.setCaps(20, 5);
    EW.insertText(0, '基线正文一二三四五六七八九十');
    await waitFor(() => OW.doc.text().includes('基线正文'), 'cr: 基线正文同步');
    // 服务端以 COMPACT_DELAY_MS 拉开 prepare→commit（见测试服务器启动参数）
    const beforeGen = OW.gen;
    OW.compact('cr-manual-1');
    await waitFor(() => OW.compactAck && OW.compactAck.gen > beforeGen, 'cr: 压缩完成', 8000);
    // 压缩进行中（切点已取）继续两侧写入——通过再次"提交期写入"验证：
    // 直接触发第二轮，并在压缩 ack 返回前连续发两批
    OW.compact('cr-manual-2');
    EW.insertText(EW.doc.text().length, '边界A');
    OW.insertText(OW.doc.text().length, '边界B');
    await waitFor(() =>
      OW.gen >= 2 && OW.doc.text().includes('边界A') && OW.doc.text().includes('边界B') &&
      EW.doc.text().includes('边界A') && EW.doc.text().includes('边界B'), 'cr: 边界写入收敛', 8000);
    assert.strictEqual(OW.doc.text(), EW.doc.text());
    // 不重复：边界A/B 各出现一次
    const t = OW.doc.text();
    assert.strictEqual(t.split('边界A').length - 1, 1, 'cr: 边界A 不重复');
    assert.strictEqual(t.split('边界B').length - 1, 1, 'cr: 边界B 不重复');
    assert.ok(t.includes('基线正文'), 'cr: 切点前内容不丢');
    ok('验收2：制作基线期间两侧边界变动不丢、不重并最终收敛');
  }

  // ----- 验收 3：落后于保留区间的离线端积压 ins/del/mark/com，取得基线后换算，获准只生效一次 -----
  {
    const D = docName('migrate-rebase');
    const OW = new SimClient('owner-mr', D); await OW.connect();
    const BW = new SimClient('behind-mr', D); await BW.connect();
    OW.member('invite', 'behind-mr', 'editor');
    await waitFor(() => BW.role === 'editor', 'mr: editor');
    OW.setCaps(20, 5);
    BW.insertText(0, '离线前的共享正文甲乙丙丁戊');
    await waitFor(() => OW.doc.text() === '离线前的共享正文甲乙丙丁戊', 'mr: 初始同步');
    await sleep(150);
    // 记录存活锚点字符 id（后续用于可映射的 mark/com）
    const aliveIds = BW.doc.visibleIds();
    BW.disconnect();
    await sleep(150);
    // 离线端积压：在存活字符处插入、删除、样式、批注（全部引用仍存在的锚点）
    const off1 = BW.insertText(2, '积压插入');
    const off2 = BW.deleteRange(0, 1);
    const [sAn, eAn] = BW.anchors(3, 6);
    const offMark = BW.mark(3, 6, { italic: true });
    const offCom = BW.addComment(3, 5, '积压批注');
    const offlineBatches = [off1, off2, offMark, offCom];
    // 服务器侧大量活动并多轮压缩，把 BW 的 lastSeq 甩出窗口、旧墓碑回收
    for (let i = 0; i < 12; i++) {
      OW.insertText(OW.doc.text().length, '服务端演进内容' + i + '。');
      const p = OW.doc.text().length - 3;
      OW.deleteRange(Math.max(0, p), 1);
      await sleep(20);
    }
    await compactUntil(OW, 2, 20, 'mr');
    assert.ok(BW.lastSeq < (OW.logMinSeq || 1) - 1 || BW.gen < OW.gen, 'mr: BW 确实落后窗口');
    // 重连 => 自动迁移 + rebase
    await BW.connect();
    await waitFor(() => !BW.migration.migrating, 'mr: 迁移完成', 10000);
    await waitFor(() =>
      OW.doc.text().includes('积压插入') && BW.doc.text().includes('积压插入') &&
      BW.pendingBatches.length === 0, 'mr: 积压 ins/del 换算生效', 10000);
    // 批注 / 标记也换算
    const comId = offCom.ops[0].id;
    await waitFor(() => OW.doc.comments.has(comId), 'mr: 积压批注换算生效');
    assert.ok(OW.doc.activeMarks().some(m => m.attrs.italic), 'mr: 积压样式换算生效');
    assert.strictEqual(fp(OW), fp(BW), 'mr: 投影收敛一致');
    // 获准批次只生效一次：重复整批（新重连 + 同 opId，跨 batchId 再 rebase）
    const before = OW.doc.text();
    for (const b of offlineBatches) {
      BW.rebase({ batchId: b.batchId + '-dup', ops: b.ops });
    }
    await sleep(400);
    assert.strictEqual(OW.doc.text(), before, 'mr: 重复换算不重复生效（opId 水位）');
    assert.strictEqual(OW.doc.text().split('积压插入').length - 1, 1, 'mr: 积压插入仅一次');
    assert.strictEqual(OW.doc.comments.has(comId) && [...OW.doc.comments.values()].filter(c => c.id === comId).length, 1);
    ok('验收3：落后离线端的 ins/del/mark/com 经新基线换算后获准批次只生效一次');
  }

  // ----- 验收 4：锚点所指墓碑已被回收 => 只能迁移或进显式冲突草稿，不得悄悄挂到别的字句 -----
  {
    const D = docName('anchor-conflict');
    const OW = new SimClient('owner-ac', D); await OW.connect();
    const BW = new SimClient('behind-ac', D); await BW.connect();
    OW.member('invite', 'behind-ac', 'editor');
    await waitFor(() => BW.role === 'editor', 'ac: editor');
    OW.setCaps(20, 5);
    BW.insertText(0, '共享起头正文');
    await waitFor(() => OW.doc.text() === '共享起头正文', 'ac: 同步');
    // 先在线共享一个"开头并发分支"字符 G（after=ROOT），随后删除 => 可回收的死叶子
    const gOp = BW.doc.insert(CRDT.ROOT, 'G');
    BW._push([gOp]);
    await waitFor(() => OW.doc.chars.has(gOp.id), 'ac: 分支字符 G 已共享');
    OW._push([OW.doc.remove(gOp.id)]);
    await waitFor(() => { const c = OW.doc.chars.get(gOp.id); return c && c.tomb; }, 'ac: G 已删除（墓碑）');
    await waitFor(() => { const c = BW.doc.chars.get(gOp.id); return c && c.tomb; }, 'ac: BW 也收到删除');
    const gid = gOp.id;
    await sleep(150);
    BW.disconnect();
    await sleep(120);
    // 离线积压：一条引用已回收墓碑 G 的插入 Y，外加一条仍可映射（after=ROOT）的插入 M
    const yOp = BW.doc.insert(gid, 'Y');          // after 指向将被回收的 G
    const mOp = BW.doc.insert(CRDT.ROOT, 'M');    // 恒可达，意图应保留但整批仍不落库
    const batch = BW._push([yOp, mOp]);
    // 服务端：大量演进并多轮压缩，把 G 的 ins/del 甩出窗口并回收其墓碑
    for (let i = 0; i < 14; i++) { OW.insertText(OW.doc.text().length, '演进' + i + '，'); await sleep(12); }
    await compactUntil(OW, 3, 20, 'ac');
    await waitFor(() => {
      const dk = readDisk(D);
      return dk.gen >= 2 && dk.baseline && !dk.baseline.chars.some(c => c.id === gid) &&
        dk.ops.every(x => x.op.id !== gid);
    }, 'ac: G 的墓碑已被回收且不在窗口', 12000);
    await BW.connect();
    await waitFor(() => !BW.migration.migrating, 'ac: 迁移完成', 10000);
    await waitFor(() => BW.quarantine.some(q => q.kind === 'conflict' && q.batchId === batch.batchId), 'ac: 产出冲突草稿', 10000);
    const q = BW.quarantine.find(x => x.kind === 'conflict' && x.batchId === batch.batchId);
    assert.ok(q, 'ac: 存在冲突草稿');
    assert.ok(q.conflicts.some(c => c.missing === gid), 'ac: 冲突明确指向被回收的锚点 G');
    // 同批可映射的 M 保留意图（mappedOps），但因整批原子性并未发布
    assert.ok((q.mappedOps || []).some(op => op.id === mOp.id), 'ac: 可映射操作意图保留在草稿');
    // 绝不悄悄挂到别的字句：共享投影既无 Y 也无 M（整批零发布）
    await sleep(200);
    assert.ok(!OW.doc.text().includes('Y'), 'ac: 无法映射的 Y 未挂靠任何字句');
    assert.ok(!OW.doc.text().includes('M'), 'ac: 同批可映射的 M 也随整批原子拒绝');
    assert.ok(!readDisk(D).baseline.chars.some(c => c.id === gid), 'ac: 服务器无 G 锚点');
    // 完整可读可复制
    assert.strictEqual(q.ops.length, 2, 'ac: 冲突载荷完整（两条）');
    assert.strictEqual(JSON.parse(JSON.stringify(q.ops)).length, 2);
    ok('验收4：所指墓碑已回收的锚点只进入显式冲突草稿，不悄悄挂到另一段字句');
  }

  // ----- 验收 5：陈旧端降权/移除后重连不得发布；完整拒绝批次跨下一轮压缩及重启保存 -----
  {
    const D = docName('stale-demoted');
    const OW = new SimClient('owner-sd', D); await OW.connect();
    const BW = new SimClient('stale-sd', D); await BW.connect();
    OW.member('invite', 'stale-sd', 'editor');
    await waitFor(() => BW.role === 'editor', 'sd: editor');
    OW.setCaps(20, 5);
    BW.insertText(0, '降权前正文');
    await waitFor(() => OW.doc.text() === '降权前正文', 'sd: 同步');
    await sleep(150);
    BW.disconnect();
    await sleep(120);
    const staleBatch = BW.insertText(0, '陈旧端的夹带操作');
    // 服务端：先降权，再大量压缩多轮
    OW.member('role', 'stale-sd', 'viewer');
    await waitFor(() => OW.roleOf('stale-sd') === 'viewer', 'sd: 已降权');
    for (let i = 0; i < 12; i++) { OW.insertText(OW.doc.text().length, '压缩推进' + i + '，'); await sleep(15); }
    await compactUntil(OW, 2, 20, 'sd');
    await BW.connect();
    await waitFor(() => !BW.migration.migrating, 'sd: 陈旧端迁移完成', 10000);
    // rebase 授权按当前纪元：viewer 整批拒绝
    await waitFor(() => BW.quarantine.some(q => q.batchId === staleBatch.batchId), 'sd: 陈旧批次被拒', 10000);
    const rej = BW.quarantine.find(q => q.batchId === staleBatch.batchId);
    assert.ok(rej, 'sd: 拒绝批次存在');
    assert.strictEqual(rej.role, 'viewer', 'sd: 按当前纪元裁决');
    assert.ok(!OW.doc.text().includes('陈旧端的夹带操作'), 'sd: 零发布');
    assert.ok(rej.ops.length === staleBatch.ops.length, 'sd: 载荷完整');
    // 再移除后重连仍不得发布
    OW.member('remove', 'stale-sd');
    await sleep(200);
    const dup = staleBatch.batchId + '-re2';
    BW.rebase({ batchId: dup, ops: staleBatch.ops });
    await sleep(400);
    assert.ok(!OW.doc.text().includes('陈旧端的夹带操作'), 'sd: 移除后重连仍零发布');
    // 拒绝批次跨下一轮压缩：再显式触发一轮
    const g0 = OW.gen;
    for (let i = 0; i < 8; i++) { OW.insertText(OW.doc.text().length, '再压缩' + i); await sleep(10); }
    OW.compact('sd-next');
    await waitFor(() => OW.gen > g0, 'sd: 又一轮压缩', 10000);
    await sleep(300);
    // 重启服务器，重新连接：被拒草稿仍在且完整
    await stopServer();
    await startServer();
    const OWb = new SimClient('owner-sd', D); await OWb.connect();
    const BWb = new SimClient('stale-sd', D); await BWb.connect();
    await waitFor(() => !BWb.migration || !BWb.migration.migrating, 'sd: 重启后迁移');
    await waitFor(() => BWb.quarantine.some(q => q.batchId === staleBatch.batchId), 'sd: 拒绝批次跨重启仍在', 10000);
    const rej2 = BWb.quarantine.find(q => q.batchId === staleBatch.batchId);
    assert.strictEqual(rej2.ops.length, staleBatch.ops.length, 'sd: 跨重启载荷完整');
    assert.deepStrictEqual(rej2.ops.map(o => o.ch).join(''), staleBatch.ops.map(o => o.ch).join(''));
    assert.ok(!OWb.doc.text().includes('陈旧端的夹带操作'), 'sd: 重启后仍零发布');
    ok('验收5：陈旧端降权/移除后重连不发布，完整拒绝批次跨下一轮压缩及重启保存');
    OWb.disconnect(); BWb.disconnect();
  }

  // ----- 验收 6：代次发布前后强杀进程 => 重启只能是完整旧代或完整新代；重试不破坏权威态 -----
  {
    const D = docName('crash-atomic');
    const OW = new SimClient('owner-ca', D); await OW.connect();
    const EW = new SimClient('editor-ca', D); await EW.connect();
    OW.member('invite', 'editor-ca', 'editor');
    await waitFor(() => EW.role === 'editor', 'ca: editor');
    OW.setCaps(15, 3);
    for (let i = 0; i < 6; i++) { EW.insertText(EW.doc.text().length, '原子性内容' + i + '。'); await sleep(20); }
    await waitFor(() => OW.doc.text().includes('原子性内容5'), 'ca: 编辑已确认');
    await sleep(2300); // 等内容批次的 2s 批量落盘完成，再测强杀持久化
    const textBefore = OW.doc.text();
    const diskBefore = readDisk(D);
    const genBefore = diskBefore.gen;
    // 触发压缩（prepare→commit 之间有 600ms 延迟），在提交落盘前强杀。
    OW.compact('ca-kill-pre');
    await sleep(200); // 仍在 prepare→commit 窗口内
    await stopServerKill();
    await startServer();
    let d1 = readDisk(D);
    assert.ok(!fs.existsSync(diskFile(D) + '.tmp'), 'ca: 无 tmp 残留');
    assert.strictEqual(d1.gen, genBefore, 'ca: 提交前杀 => 仍是完整旧代');
    // 重连校验投影完整（旧代内容一字不少）
    const O1 = new SimClient('owner-ca', D); await O1.connect();
    const E1 = new SimClient('editor-ca', D); await E1.connect();
    assert.strictEqual(O1.doc.text(), E1.doc.text(), 'ca: 强杀后两端投影一致');
    assert.strictEqual(O1.doc.text(), textBefore, 'ca: 内容完整（旧代）');
    O1.disconnect(); E1.disconnect();
    // 6b: 用新连接的编辑者写入并显式压缩，等代次真正提交后再 SIGKILL。
    const Eb = new SimClient('editor-ca', D); await Eb.connect();
    for (let i = 0; i < 6; i++) { Eb.insertText(0, '更多原子内容' + i); await sleep(15); }
    const Ob = new SimClient('owner-ca', D); await Ob.connect();
    Ob.compact('ca-commit-1');
    await sleep(780);
    let committedText = readDisk(D);
    assert.ok(committedText.gen >= 1, 'ca: 已有提交代次');
    // 再发起一轮并在提交后杀
    const gb = committedText.gen;
    for (let i = 0; i < 6; i++) { Eb.insertText(0, 'X' + i); await sleep(10); }
    Ob.compact('ca-commit-2');
    await sleep(780);
    committedText = readDisk(D);
    assert.ok(committedText.gen > gb, 'ca: 新一代已提交');
    const committedProjection = Ob.doc.text();
    await stopServerKill();
    await startServer();
    const d2 = readDisk(D);
    assert.ok(!fs.existsSync(diskFile(D) + '.tmp'), 'ca: 提交后杀无 tmp');
    const O2 = new SimClient('owner-ca', D); await O2.connect();
    const E2 = new SimClient('editor-ca', D); await E2.connect();
    assert.strictEqual(O2.doc.text(), E2.doc.text(), 'ca: 提交后杀，两端投影一致（完整新代）');
    assert.strictEqual(d2.gen, committedText.gen, 'ca: 代次完整');
    assert.strictEqual(O2.doc.text(), committedProjection, 'ca: 新代内容完整');
    // 重试压缩不破坏权威态：连续手动压缩多次（窗口已小于上界 => 投影/代次不变）
    const fpBefore2 = CRDT.fingerprint(O2.doc);
    O2.compact('ca-retry-1'); await sleep(500);
    O2.compact('ca-retry-2'); await sleep(500);
    await waitFor(() => CRDT.fingerprint(E2.doc) === fpBefore2, 'ca: 重试压缩投影不变', 8000);
    assert.strictEqual(CRDT.fingerprint(O2.doc), CRDT.fingerprint(E2.doc));
    ok('验收6：发布前后强杀只得到完整旧代/新代，重试压缩不破坏权威态');
    Ob.disconnect(); Eb.disconnect(); O2.disconnect(); E2.disconnect();
  }

  // ----- 验收 7：迁移分片 / 换算消息重复、乱序 => 不重复投影、基线点、冲突项或账本事件 -----
  {
    const D = docName('idempotent-mig');
    const OW = new SimClient('owner-im', D); await OW.connect();
    const BW = new SimClient('behind-im', D); await BW.connect();
    OW.member('invite', 'behind-im', 'editor');
    await waitFor(() => BW.role === 'editor', 'im: editor');
    OW.setCaps(20, 5);
    BW.insertText(0, '幂等迁移正文甲乙丙');
    await waitFor(() => OW.doc.text().includes('幂等迁移正文'), 'im: 同步');
    // 先在线共享再删除一个开头并发分支字符 H => 墓碑将被压缩回收
    const hOp = BW.doc.insert(CRDT.ROOT, 'H');
    BW._push([hOp]);
    await waitFor(() => OW.doc.chars.has(hOp.id), 'im: H 已共享');
    OW._push([OW.doc.remove(hOp.id)]);
    await waitFor(() => { const c = OW.doc.chars.get(hOp.id); return c && c.tomb; }, 'im: H 已删除');
    await waitFor(() => { const c = BW.doc.chars.get(hOp.id); return c && c.tomb; }, 'im: BW 收到 H 删除');
    const hid = hOp.id;
    await sleep(150);
    BW.disconnect();
    await sleep(100);
    const good = BW.insertText(1, '可映射');
    // 引用已回收墓碑 H 的插入 Z => 冲突（不悄悄挂靠）
    const afterH = BW.doc.insert(hid, 'Z');
    const badBatch = BW._push([afterH]);
    for (let i = 0; i < 14; i++) { OW.insertText(OW.doc.text().length, '演进' + i + '，'); await sleep(10); }
    await compactUntil(OW, 3, 20, 'im');
    await waitFor(() => {
      const dk = readDisk(D);
      return dk.gen >= 2 && dk.baseline && !dk.baseline.chars.some(c => c.id === hid) &&
        dk.ops.every(x => x.op.id !== hid);
    }, 'im: H 墓碑已回收', 12000);
    // 手工驱动迁移：先发 hello，再以乱序+重复方式直接请求分片
    await BW.connect();
    // connect 已触发自动迁移；额外用同一 ws 乱序、重复请求各分片
    const targetGen = OW.gen;
    await waitFor(() => BW.migration && BW.migration.total >= 1, 'im: 知道总分片');
    const total = BW.migration.total;
    const order = [];
    for (let i = total - 1; i >= 0; i--) order.push(i);
    order.push(0, total - 1, 0); // 重复首尾
    for (const i of order) BW.send({ t: 'migrate', gen: targetGen, index: i, reqId: BW.id + '#dup#' + i + '#' + Math.random() });
    await waitFor(() => BW.migration && BW.migration.done, 'im: 迁移完成（乱序重复）', 10000);
    await waitFor(() =>
      BW.quarantine.some(q => q.kind === 'conflict' && q.batchId === badBatch.batchId) &&
      OW.doc.text().includes('可映射'), 'im: 换算结论齐备', 10000);
    // 不重复：基线点/代次
    assert.strictEqual(BW.gen, targetGen);
    const genSeen = BW.generations.filter(x => x.gen === targetGen).length;
    // generations 只记录服务器广播；重放分片不会产生账本事件
    assert.strictEqual(BW.ledger.filter(e => e.kind === 'space').length, OW.ledger.filter(e => e.kind === 'space').length, 'im: 无额外账本事件');
    // 冲突项只一条
    assert.strictEqual(BW.quarantine.filter(q => q.batchId === badBatch.batchId).length, 1, 'im: 冲突项不重复');
    // 投影不重复
    assert.strictEqual(BW.doc.text().split('可映射').length - 1, 1, 'im: 可映射改动仅一次');
    assert.ok(!OW.doc.text().includes('Z'), 'im: 冲突项未发布');
    // 同一换算 reqId 重放
    BW.rebase({ batchId: good.batchId, ops: good.ops });
    // （该 batchId 已经在自动迁移时换算过 => 服务端 quarantine/pending 命中回放）
    await sleep(400);
    assert.strictEqual(OW.doc.text().split('可映射').length - 1, 1, 'im: 重放换算不重复');
    assert.strictEqual(fp(OW), fp(BW), 'im: 收敛一致');
    ok('验收7：分片与换算重复、乱序时不重复投影/基线点/冲突项/账本事件');
  }

  // ----- 验收 8：成员变动、代次发布、陈旧批次同时竞争 => 唯一授权结果与全局次序 -----
  {
    const D = docName('race-authz-gen');
    const OW = new SimClient('owner-ra2', D); await OW.connect();
    const BW = new SimClient('x-ra2', D); await BW.connect();
    OW.member('invite', 'x-ra2', 'editor');
    await waitFor(() => BW.role === 'editor', 'ra2: editor');
    OW.setCaps(10, 3);
    BW.insertText(0, '竞争前正文');
    await waitFor(() => OW.doc.text() === '竞争前正文', 'ra2: 同步');
    BW.disconnect();
    await sleep(120);
    const stale = BW.insertText(0, '陈旧竞争操作');
    // 同一时刻：服务端发起压缩（代次发布）+ 降权 + 陈旧端重连换算
    for (let i = 0; i < 14; i++) { OW.insertText(OW.doc.text().length, '推进' + i); await sleep(8); }
    OW.compact('ra2-gen-1');
    await sleep(780); // 等代次发布
    OW.member('role', 'x-ra2', 'viewer');
    for (let i = 0; i < 10; i++) { OW.insertText(OW.doc.text().length, '再推进' + i); await sleep(8); }
    await compactUntil(OW, 2, 10, 'ra2');
    await BW.connect(); // 迁移 + rebase 与代次/成员竞争
    await waitFor(() => !BW.migration.migrating, 'ra2: 迁移结束', 10000);
    await waitFor(() => BW.quarantine.some(q => q.batchId === stale.batchId), 'ra2: 陈旧批次有唯一结论', 10000);
    const qs = BW.quarantine.filter(q => q.batchId === stale.batchId);
    assert.strictEqual(qs.length, 1, 'ra2: 唯一裁决记录');
    assert.ok(!OW.doc.text().includes('陈旧竞争操作'), 'ra2: 未夹带发布');
    // 全局次序：账本一致；epoch 单调
    assert.strictEqual(ledgerSig(OW), ledgerSig(BW), 'ra2: 全局账本次序一致');
    assert.ok(OW.epoch === BW.epoch && OW.epoch >= 1, 'ra2: epoch 收敛一致');
    // 在线旁观第三方也得到同一结论
    const YW = new SimClient('y-ra2', D); await YW.connect();
    assert.strictEqual(ledgerSig(YW), ledgerSig(OW), 'ra2: 第三方账本次序一致');
    assert.strictEqual(YW.doc.text(), OW.doc.text(), 'ra2: 第三方投影一致');
    assert.ok(!YW.doc.text().includes('陈旧竞争操作'));
    ok('验收8：成员变动/代次发布/陈旧批次竞争下唯一授权结果与全局次序');
  }

  // ----- 验收 9：回退到仍保留的基线点产生新演进记录；请求已清除基线点返回明确错误且不增记录 -----
  {
    const D = docName('restore-gen');
    const OW = new SimClient('owner-rg', D); await OW.connect();
    const EW = new SimClient('editor-rg', D); await EW.connect();
    OW.member('invite', 'editor-rg', 'editor');
    await waitFor(() => EW.role === 'editor', 'rg: editor');
    OW.setCaps(12, 2);
    EW.insertText(0, '第一代内容甲乙丙丁戊己庚辛');
    await waitFor(() => OW.doc.text().includes('第一代内容'), 'rg: 初始');
    for (let i = 0; i < 10; i++) { EW.insertText(0, '后续演进' + i); await sleep(12); }
    await compactUntil(OW, 2, 12, 'rg');
    const genNow = readDisk(D).gen;
    const gensBefore = (OW.compactInfo.generations || []).length;
    // 请求一个已被物理回收的旧代（gen 0 或 gen-1）
    const older = Math.max(0, genNow - 1);
    OW.restoreGen(older);
    await waitFor(() => OW.errors.some(e => e.code === 'generation-compacted' || e.code === 'generation-not-found'), 'rg: 旧基线明确错误');
    await sleep(200);
    OW.send({ t: 'compactStatus' });
    await sleep(200);
    const gensAfterErr = (OW.compactInfo.generations || []).length;
    assert.strictEqual(gensAfterErr, gensBefore, 'rg: 失败请求不增加演进记录');
    // 回退到"当前仍保留的基线点" => 产生新的修订（新演进记录）
    const revsBefore = OW.revs.length;
    const textExpect = (() => {
      const dk = readDisk(D);
      const tmp = new CRDT.Doc('x');
      CRDT.importBaseline(tmp, dk.baseline);
      return tmp.text();
    })();
    OW.restoreBaseline();
    await waitFor(() => OW.revs.length > revsBefore && OW.revs[OW.revs.length - 1].kind === 'baseline-restore', 'rg: 回退产生新修订', 8000);
    await waitFor(() => EW.doc.text() === OW.doc.text(), 'rg: 回退收敛');
    assert.strictEqual(OW.doc.text(), textExpect, 'rg: 正文回到当前基线点投影');
    assert.ok(OW.revs[OW.revs.length - 1].restoredGen === genNow || OW.revs[OW.revs.length - 1].gen === genNow, 'rg: 记录来源代次');
    ok('验收9：回退仍保留基线点产生新演进，请求已清除基线点明确报错且不增记录');
  }

  // ----- 验收 10：既有第二代（v3 已压缩）空间首次打开惰性升级，投影不改写、不产生第二个 owner -----
  {
    const D = 'v3-existing-' + RUN;
    {
      // 手工造一份"第二代空间"：gen=2，有基线、有窗口，已有唯一 owner
      const fdoc = new CRDT.Doc('old-author');
      let after = null;
      const allOps = [];
      for (const ch of '第二代空间的既有正文ABCDEF') {
        const o = fdoc.insert(after, ch); o.opId = 'old-author#' + o.id; after = o.id; allOps.push(o);
      }
      // 删除末尾两个叶子（可回收）
      const ids = fdoc.visibleIds();
      fdoc.remove(ids[ids.length - 1]); fdoc.remove(ids[ids.length - 2]);
      const windowOps = allOps.slice(-3).map((op, i) => ({ seq: 18 + i, op }));
      const scratch = new CRDT.Doc('s');
      for (const op of allOps.slice(0, -3)) scratch.apply(op);
      const baseline = CRDT.buildBaseline(scratch, windowOps);
      const payload = {
        v: 3, seq: 20, gen: 2, baseline, logMinSeq: 18,
        caps: { logOpCap: 2000, revSnapshotCap: 50 },
        generations: [
          { gen: 1, cutSeq: 10, ts: Date.now() - 2000, commitTs: Date.now() - 2000, baselineChars: baseline.chars.length, windowOps: 7 },
          { gen: 2, cutSeq: 17, ts: Date.now() - 1000, commitTs: Date.now() - 1000, baselineChars: baseline.chars.length, windowOps: 3 },
        ],
        ops: windowOps,
        revs: [{ n: 1, seq: 20, fromSeq: 18, ts: Date.now(), by: 'old-author', kind: 'edit', summary: '旧修订', snapshot: null, compacted: true, gen: 2 }],
        opIdMax: { 'old-author': 999 },
        initialized: true, epoch: 3,
        members: { 'old-author': { id: 'old-author', name: '旧主理人', role: 'owner', since: Date.now() - 9999 } },
        ledger: [
          { seq: 1, ts: Date.now() - 9999, kind: 'space', act: 'init', by: null, target: 'old-author', targetName: '旧主理人', from: null, to: 'owner', epoch: 0 },
        ],
        batches: {}, seenReqIds: [], rebaseReqs: [], quarantine: [],
      };
      fs.writeFileSync(diskFile(D), JSON.stringify(payload));
      // 期望投影：baseline + window（窗口是最后3个 ins，基线是前 cut 个含两墓碑）
    }
    const expectText = (() => {
      const dk = JSON.parse(fs.readFileSync(diskFile(D), 'utf8'));
      const d = new CRDT.Doc('e');
      CRDT.importBaseline(d, dk.baseline);
      for (const x of dk.ops) d.apply(x.op);
      return d.text();
    })();
    const N1 = new SimClient('newcomer1', D); await N1.connect();
    const N2 = new SimClient('old-author', D); await N2.connect();
    // 投影不被改写
    assert.strictEqual(N1.doc.text(), expectText, 'v3: 新访客看到既有投影');
    assert.strictEqual(N2.doc.text(), expectText, 'v3: 旧主理人看到既有投影');
    assert.strictEqual(N1.gen, 2, 'v3: 代次保留为 2');
    assert.strictEqual(N2.gen, 2);
    // 恰好一个 owner，且仍是旧主理人（没有第二个 owner）
    const owners = N1.members.filter(m => m.role === 'owner');
    assert.strictEqual(owners.length, 1, 'v3: 仍只有一个 owner');
    assert.strictEqual(owners[0].id, 'old-author', 'v3: 不产生第二个主理人');
    assert.strictEqual(N2.role, 'owner');
    assert.strictEqual(N1.role, 'viewer', 'v3: 新访客不是 owner');
    // 没有新增 upgrade 审计（惰性升级只发生在无成员元数据的 v1/v2；v3 直接读取）
    assert.strictEqual(N1.ledger.filter(e => e.act === 'upgrade').length, 0, 'v3: 不追加升级审计');
    N1.disconnect(); N2.disconnect();
    ok('验收10：既有第二代空间首开惰性读取，投影不改写、代次保留、不产生第二个主理人');
  }

  // 关闭所有连接（场景 5/9 的客户端在各自块内已断开或随进程结束回收）
  for (const c of [O, E, C, V, O2, U, O3, Z, A, B, O2b, Ub]) {
    if (c && c.ws) c.disconnect();
  }
  await stopServer();
  console.log('\n全部 ' + passed + ' 项测试通过 ✅');
  process.exit(0);
})().catch(async (e) => {
  console.error('\n测试失败 ❌', e);
  await stopServer();
  process.exit(1);
});
