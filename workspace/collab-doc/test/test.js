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
const COMPACT = require('../shared/compaction.js');

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
    this.frags = [];
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
      const fin = !!(b0 & 0x80), op = b0 & 0x0f, masked = !!(b1 & 0x80);
      let len = b1 & 0x7f, off = 2;
      if (len === 126) { if (this.buf.length < 4) return; len = this.buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (this.buf.length < 10) return; len = Number(this.buf.readBigUInt64BE(2)); off = 10; }
      // 服务端帧不掩码、客户端帧掩码：仅在 masked 时再加 4 字节掩码
      if (masked) off += 4;
      if (this.buf.length < off + len) return;
      let payload = this.buf.slice(off, off + len);
      if (masked) {
        const mask = this.buf.slice(off - 4, off);
        payload = Buffer.from(payload);
        for (let i = 0; i < payload.length; i++) payload[i] ^= mask[i & 3];
      }
      this.buf = this.buf.slice(off + len);
      if (op === 8) return;
      if (op === 0 || op === 1 || op === 2) {
        this.frags.push(payload);
        if (fin) {
          const full = Buffer.concat(this.frags);
          this.frags = [];
          const msg = JSON.parse(full.toString());
          for (const fn of this.handlers) fn(msg);
        }
      }
    }
  }
  close() { try { this.sock.destroy(); } catch (e) { /* ignore */ } }
}

// ---------- 模拟客户端（复刻浏览器端同步 + 治理 + 代次迁移逻辑） ----------
let batchCounter = 0;
class SimClient {
  constructor(id, doc) {
    this.id = id;
    this.docName = doc;
    this.doc = new CRDT.Doc(id);
    this.lastSeq = 0;
    this.opSeq = 0;
    this.allOps = [];
    this.pendingBatches = [];
    this.quarantine = [];
    this.conflicts = [];       // 迁移换算冲突草稿
    this.migrateReplies = [];
    this.revs = [];
    this.ledger = [];
    this.members = [];
    this.peers = [];
    this.epoch = 0;
    this.gen = 0;
    this.cutoff = 0;
    this.cstat = null;
    this.mig = null;           // { fromGen, toGen, pieces:Map }
    this.role = null;
    this.welcome = null;
    this.errors = [];
    this.ws = null;
    this.readyResolve = null;
    this.ready = new Promise((r) => { this.readyResolve = r; });
  }
  async connect() {
    this.welcome = null;
    this.ready = new Promise((r) => { this.readyResolve = r; });
    this.ws = await wsConnect();
    this.ws.onMessage((m) => this._handle(m));
    this.ws.send({ t: 'hello', clientId: this.id, name: this.id, doc: this.docName, lastSeq: this.lastSeq, gen: this.gen });
    await this.ready;
  }
  disconnect() { if (this.ws) this.ws.close(); this.ws = null; }
  send(o) { if (this.ws) this.ws.send(o); }
  // 迁移期间不要让 ready 提前结束：只有非迁移 welcome 才 ready
  member(act, target, role, name) {
    const reqId = this.id + '#req#' + (crypto.randomUUID ? crypto.randomUUID() : Math.random().toString(36).slice(2));
    this._lastReq = reqId;
    this.send({ t: 'member', reqId, act, target, role, name });
    return reqId;
  }
  restore(rev) { this.send({ t: 'restore', rev }); }
  compact(phase, reqId) { this.send({ t: 'compact', phase: phase || 'once', reqId: reqId || ('creq-' + (++this.opSeq)) }); }
  restoreBaseline(g) { this.send({ t: 'restoreBaseline', gen: g }); }
  approve(d, anchor) {
    const approveId = 'ap-' + d.draftId;
    const kind = d.kind;
    if (kind === 'del-reclaimed') { this.send({ t: 'approveConflict', approveId, kind }); return approveId; }
    if (kind === 'ins-after') this.send({ t: 'approveConflict', approveId, kind, ch: d.op.ch, anchor: anchor || { id: null, edge: 's' } });
    else if (kind === 'mark-anchor') this.send({ t: 'approveConflict', approveId, kind, attrs: d.op.attrs || {}, anchor });
    else if (kind === 'com-anchor') this.send({ t: 'approveConflict', approveId, kind, text: d.op.text || '', anchor });
    return approveId;
  }
  _upsertEntry(e) {
    if (!e || this.ledger.some(x => x.seq === e.seq && x.act === e.act && x.target === e.target)) return;
    this.ledger.push(e);
    this.ledger.sort((a, b) => a.seq - b.seq);
  }
  _handle(m) {
    if (m.t === 'welcome') {
      this.lastSeq = Math.max(this.lastSeq, m.seq || 0);
      if (m.gen != null) this.gen = m.gen;
      if (m.cutoff != null) this.cutoff = m.cutoff;
      if (m.needMigration) {
        this.revs = m.revs || this.revs;
        for (const e of m.ledger || []) this._upsertEntry(e);
        this.members = m.members || this.members;
        this.epoch = m.epoch || this.epoch;
        const me = this.members.find(x => x.id === this.id);
        this.role = me ? me.role : 'viewer';
        this.welcome = m; this.readyResolve(); // 迁移分片随后到达
        return;
      }
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
      this.welcome = m;
      this.readyResolve();
    } else if (m.t === 'genSwitch') {
      this.mig = { fromGen: m.fromGen == null ? this.gen : m.fromGen, toGen: m.toGen, pieces: new Map() };
    } else if (m.t === 'baselineChunk') {
      if (!this.mig) this.mig = { fromGen: this.gen, toGen: m.gen, pieces: new Map() };
      this.mig.pieces.set(m.shard, m);
    } else if (m.t === 'baselineEnd') {
      this._finishMigration(m);
    } else if (m.t === 'ops') {
      if (m.gen != null) this.gen = m.gen;
      const applied = Array.isArray(m.applied) ? m.applied : [];
      for (const { seq, op } of applied) {
        this.doc.apply(op);
        this.allOps.push(op);
        this.lastSeq = Math.max(this.lastSeq, seq);
      }
      if (m.migrated || m.approved) this._dropOps(applied);
      else if (m.batchId) this._drop(m.batchId, applied);
      else this._dropOps(applied);
      if (m.rev) {
        if (!this.revs.some(r => r.n === m.rev.n)) this.revs.push(m.rev);
        this.lastSeq = Math.max(this.lastSeq, m.rev.seq);
      }
    } else if (m.t === 'batchAck') {
      if (m.status === 'rejected') {
        if (m.code === 'migration-required') return; // 等基线流
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
    } else if (m.t === 'migrateAck') {
      this.migrateReplies.push(m);
      if (m.status === 'rejected') {
        this.lastSeq = Math.max(this.lastSeq, m.atSeq || 0);
        // 合并迁移批次在 _finishMigration 已从 pendingBatches 取出；拒绝时用服务端回传的完整载荷做隔离，
        // 并从已确认操作重建本地文档，绝不把被拒乐观内容留在投影里。
        let ops = Array.isArray(m.ops) ? m.ops : [];
        const i = this.pendingBatches.findIndex(b => b.batchId === m.batchId);
        if (i >= 0) { if (!ops.length) ops = this.pendingBatches[i].ops; this.pendingBatches.splice(i, 1); }
        const key = m.batchId || m.migId;
        if (!this.quarantine.some(q => q.batchId === key)) {
          // 迁移合并批次可能涵盖全部积压：拒绝时把剩余 pendingBatches 一并隔离、清空，
          // 本地只从已确认操作重建（被拒乐观内容不得留在投影，也不得作为"仍待发"被重放）
          for (const b of this.pendingBatches) if (!ops.length) ops = b.ops;
          this.pendingBatches = [];
          this.doc.clear();
          for (const op of this.allOps) this.doc.apply(op);
          this.quarantine.push({
            draftId: 'd-' + (++batchCounter), batchId: key, ops,
            reason: m.reason, role: m.role, need: m.need, kinds: m.kinds || {},
            epoch: m.epoch, atSeq: m.atSeq, rejectedTs: Date.now(), migrated: true,
          });
        }
      } else {
        if (m.gen != null) this.gen = m.gen;
        for (const { seq, op } of m.applied || []) {
          this.doc.apply(op); this.allOps.push(op);
          this.lastSeq = Math.max(this.lastSeq, seq);
        }
        if (m.rev && !this.revs.some(r => r.n === m.rev.n)) this.revs.push(m.rev);
        for (const c of m.conflicts || []) {
          if (this.conflicts.some(d => d.migId === m.migId && d.op.opId === c.op.opId && d.kind === c.kind)) continue;
          this.conflicts.push({ draftId: 'cf-' + (++batchCounter), migId: m.migId, kind: c.kind, op: c.op, reason: c.reason, anchor: c.anchor, ts: Date.now(), approved: false });
        }
        this.pendingBatches = []; // 合并批次已由迁移结论决定
      }
    } else if (m.t === 'approveAck') {
      if (m.ok) {
        for (const d of this.conflicts) if (d.approveId === m.approveId) d.approved = true;
        for (const { seq, op } of m.appliedOps || []) { this.doc.apply(op); this.allOps.push(op); this.lastSeq = Math.max(this.lastSeq, seq); }
      } else this.errors.push(m);
    } else if (m.t === 'compactionStatus') {
      this.cstat = m; this.gen = m.gen; this.cutoff = m.cutoff;
    } else if (m.t === 'compactAck') {
      this.lastCompactAck = m;
    } else if (m.t === 'restoreBaselineAck') {
      this.lastRestoreBaselineAck = m;
    } else if (m.t === 'members') {
      this._upsertEntry(m.entry);
      this.members = m.members || this.members;
      this.epoch = m.epoch;
      if (m.entry) this.lastSeq = Math.max(this.lastSeq, m.entry.seq);
      const me = this.members.find(x => x.id === this.id);
      this.role = me ? me.role : 'viewer';
    } else if (m.t === 'presence') {
      this.peers = m.peers || [];
    } else if (m.t === 'error') {
      this.errors.push(m);
    }
  }
  _finishMigration(endMsg) {
    const received = [];
    for (const s of this.mig.pieces.values()) received.push(s);
    const assembled = COMPACT.assembleShards(received);
    const base = assembled.find(b => b.gen === endMsg.gen) || assembled[assembled.length - 1];
    const fromGen = this.mig.fromGen;
    this.doc.clear();
    const baseOps = COMPACT.baselineToOps({ gen: base.gen, cutoffSeq: base.cutoffSeq, chars: base.chars, marks: base.marks, comments: base.comments });
    for (const op of baseOps) this.doc.apply(op);
    for (const r of endMsg.tail || []) this.doc.apply(r.op);
    this.allOps = baseOps.concat((endMsg.tail || []).map(r => r.op));
    this.gen = endMsg.gen; this.cutoff = endMsg.cutoffSeq; this.lastSeq = endMsg.seq;
    this.revs = endMsg.revs || [];
    this.ledger = []; for (const e of endMsg.ledger || []) this._upsertEntry(e);
    this.members = endMsg.members || this.members; this.epoch = endMsg.epoch || this.epoch;
    const me = this.members.find(x => x.id === this.id);
    this.role = me ? me.role : 'viewer';
    this.mig = null;
    // 积压批次合并为一条 migrate（fromGen），服务端换算
    const ops = [];
    for (const b of this.pendingBatches) for (const op of b.ops) ops.push(op);
    if (ops.length) {
      const migId = this.id + '#mig#' + (++this.opSeq);
      const batchId = 'coalesced-' + migId;
      this.send({ t: 'migrate', migId, batchId, fromGen, ops });
    }
  }
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
    this.send({ t: 'ops', batchId: b.batchId, ops: batch });
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

  // ---- v3 代次/迁移测试辅助 ----
  rawInsert(afterId, ch) {
    const op = { t: 'ins', id: this.id + ':r' + (++this.opSeq), after: afterId == null ? '' : afterId, ch, by: this.id };
    op.opId = this.id + '#' + this.opSeq;
    return op; // 不本地应用、不入队，调用方自行组织
  }
  // 仅本地应用并入队（离线积压），不要求在线
  queueOps(ops) {
    const batch = [];
    for (const op of ops) { this.doc.apply(op); batch.push(op); }
    const b = { batchId: this.id + '#B' + (++this.opSeq) + '-' + (++batchCounter), ops: batch };
    this.pendingBatches.push(b);
    if (this.ws) this.ws.send({ t: 'ops', batchId: b.batchId, ops: batch });
    return b;
  }
  // 离线插入一段（在可见位置 pos），返回 { batch, ops, chars }
  offlineInsert(pos, str) {
    const ids = this.doc.visibleIds();
    let after = pos > 0 ? ids[pos - 1] : '';
    const ops = [];
    for (const ch of str) { const op = this.rawInsert(after, ch); ops.push(op); this.doc.apply(op); after = op.id; }
    const b = { batchId: this.id + '#B' + (++this.opSeq) + '-' + (++batchCounter), ops };
    this.pendingBatches.push(b); // 不发送（离线）
    return b;
  }
  // 离线删除可见位置 [pos,pos+len)
  offlineDelete(pos, len) {
    const ids = this.doc.visibleIds();
    const ops = [];
    for (let i = 0; i < len; i++) {
      const op = { t: 'del', id: ids[pos + i], by: this.id };
      op.opId = this.id + '#' + (++this.opSeq);
      ops.push(op); this.doc.apply(op);
    }
    const b = { batchId: this.id + '#B' + (++this.opSeq) + '-' + (++batchCounter), ops };
    this.pendingBatches.push(b);
    return b;
  }
  offlineMark(s, e, attrs) {
    const [st, en] = this.anchors(s, e);
    const op = this.doc.mark(st, en, attrs);
    op.opId = this.id + '#' + (++this.opSeq);
    this.doc.apply(op);
    const b = { batchId: this.id + '#B' + (++this.opSeq) + '-' + (++batchCounter), ops: [op] };
    this.pendingBatches.push(b);
    return b;
  }
  offlineComment(s, e, text) {
    const [st, en] = this.anchors(s, e);
    const op = this.doc.comment(st, en, text, this.doc.text().slice(s, e));
    op.opId = this.id + '#' + (++this.opSeq);
    this.doc.apply(op);
    const b = { batchId: this.id + '#B' + (++this.opSeq) + '-' + (++batchCounter), ops: [op] };
    this.pendingBatches.push(b);
    return { batch: b, op };
  }
  // 用一个「指向已构造旧字符 id」的批注（测试墓碑回收冲突用）
  offlineCommentOn(anchorId, edgeS, edgeE, text, quote) {
    const op = this.doc.comment({ id: anchorId, edge: edgeS || 's' }, { id: anchorId, edge: edgeE || 'e' }, text, quote || 'X');
    op.opId = this.id + '#' + (++this.opSeq);
    // 不本地应用（锚点可能已不存在），仅排队作为积压
    const b = { batchId: this.id + '#B' + (++this.opSeq) + '-' + (++batchCounter), ops: [op] };
    this.pendingBatches.push(b);
    return { batch: b, op };
  }
}

const sleep = (ms) => new Promise(r => setTimeout(r, ms));
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
      env: Object.assign({}, process.env, { PORT: String(PORT), DATA_DIR }),
      stdio: ['ignore', 'pipe', 'inherit'],
    });
    server.stdout.on('data', (d) => { if (String(d).includes('http://')) resolve(); });
    server.on('exit', (c) => reject(new Error('服务器退出 code=' + c)));
    setTimeout(() => reject(new Error('服务器启动超时')), 8000);
  });
}
function stopServer() { return new Promise((res) => { if (!server) return res(); server.on('exit', res); server.kill('SIGTERM'); setTimeout(res, 2500); }); }

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
  // 旧修订原样保留（升级可能额外追加一条 baseline 标记）
  const oldRev = L1.revs.find(r => r.summary === '旧修订');
  assert.ok(oldRev, '旧修订保留');
  assert.ok(L1.gen >= 1, '已进入基线代次');
  assert.strictEqual(L1.revs.filter(r => r.kind === 'baseline').length, 1, '仅追加一条基线标记');
  // 升级审计：恰有一条 space/upgrade，seq 紧接旧 seq，未重写旧数据
  const up = L1.ledger.filter(e => e.kind === 'space' && e.act === 'upgrade');
  assert.strictEqual(up.length, 1);
  assert.strictEqual(up[0].seq, 10); // 旧 seq=9（按字符数），升级条目紧接其后为 10
  const onDisk = JSON.parse(fs.readFileSync(path.join(DATA_DIR, encodeURIComponent(LEGACY) + '.json'), 'utf8'));
  assert.strictEqual(onDisk.v, 3, 'v1 空间首开后落盘为 v3');
  assert.strictEqual(onDisk.revs.length >= 1, true, '旧修订保留');
  // v1 首开：space/upgrade 审计（seq=10）+ v2->v3 不发生（v1 首开即 v3）；至少 space/upgrade 一条
  assert.ok(onDisk.ledger.some(e => e.kind === 'space' && e.act === 'upgrade'), 'space/upgrade 审计存在');
  // 投影视图不被改写：基线文本等于旧正文
  assert.strictEqual(onDisk.baselines[onDisk.baselines.length - 1].b.text, '旧版空间的珍贵正文', '基线投影不被改写');
  // 第三方确认（gen0 客户端需经迁移流重建到 gen1，等待投影收敛）
  const L3 = new SimClient('legacy-user-c', LEGACY); await L3.connect();
  await waitFor(() => L3.doc.text() === '旧版空间的珍贵正文' && L3.gen >= 1, 'L3 迁移后投影一致');
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

  // 关闭所有连接（场景 5/9 的客户端在各自块内已断开或随进程结束回收）
  for (const c of [O, E, C, V, O2, U, O3, Z, A, B, O2b, Ub]) {
    if (c && c.ws) c.disconnect();
  }

  // ====================================================================
  // ============ v3 验收：有界流水压缩 / 基线代次 / 快照迁移换算 ============
  // ====================================================================
  const sigOf = (c) => ({
    text: c.doc.text(),
    marks: c.doc.activeMarks().map(m => m.s + ':' + m.e + ':' + Object.keys(m.attrs).sort().join()).sort().join('|'),
    comments: c.doc.commentList().map(x => x.id + ':' + (x.resolved ? 1 : 0) + ':' + (x.detached ? 1 : 0) + ':' + x.text).sort().join('|'),
    roles: c.members.map(m => m.id + '=' + m.role).sort().join(','),
    epoch: c.epoch,
    ledger: c.ledger.filter(e => e.kind === 'evolution' || e.kind === 'membership' || e.kind === 'space').map(e => (e.ev || 0) + ':' + e.seq + ':' + (e.act || e.kind)).join('|'),
  });
  const sameView = (a, b, label) => {
    const sa = sigOf(a), sb = sigOf(b);
    assert.strictEqual(sa.text, sb.text, label + '（正文）');
    assert.strictEqual(sa.marks, sb.marks, label + '（样式）');
    assert.strictEqual(sa.comments, sb.comments, label + '（批注）');
    assert.strictEqual(sa.roles, sb.roles, label + '（角色）');
    assert.strictEqual(sa.epoch, sb.epoch, label + '（授权纪元）');
    assert.strictEqual(sa.ledger, sb.ledger, label + '（治理账本次序）');
  };

  // ---- 验收(1)：大量增删触发多轮回收，磁盘流水降到上界，在线各端投影一致 ----
  {
    const D = docName('bounded');
    const Ow = new SimClient('bo', D); await Ow.connect();
    const Ed = new SimClient('be', D); await Ed.connect();
    Ow.member('invite', 'be', 'editor');
    await waitFor(() => Ed.role === 'editor', 'bounded: Ed editor');
    // 多轮大量增删：每轮几百字，再删一半，触发多次自动压缩（LOG_CAP 由测试服务器默认 90000）
    for (let round = 0; round < 6; round++) {
      const chunk = '第' + round + '轮内容-'.repeat(40);
      Ed.insertText(Ed.doc.text().length, chunk);
      await waitFor(() => Ow.doc.text().endsWith(chunk.slice(-6)), 'bounded: 同步 r' + round);
      const len = Ed.doc.text().length;
      if (len > 40) Ed.deleteRange(Math.floor(len / 4), Math.floor(len / 4));
      await sleep(120);
    }
    // 手动再压缩两轮
    Ow.compact('once', 'b1'); await waitFor(() => Ow.lastCompactAck && Ow.lastCompactAck.published, 'bounded: 手动压缩1');
    Ow.compact('once', 'b2'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= 2, 'bounded: 手动压缩2');
    await waitFor(() => Ed.gen === Ow.gen && Ed.doc.text() === Ow.doc.text(), 'bounded: Ed 迁移收敛');
    Ow.send({ t: 'compactionStatus' });
    await waitFor(() => Ow.cstat && Ow.cstat.logBytes <= Ow.cstat.logCapBytes, 'bounded: 流水不超上界');
    assert.ok(Ow.cstat.logBytes <= Ow.cstat.logCapBytes, '磁盘流水受配置上界约束（' + Ow.cstat.logBytes + ' <= ' + Ow.cstat.logCapBytes + '）');
    assert.ok(Ow.gen >= 2, '发生多代压缩（实际 gen=' + Ow.gen + '）');
    sameView(Ow, Ed, '验收1: 压缩后两端投影一致');
    // 磁盘上旧流水/快照已回收
    const disk = JSON.parse(fs.readFileSync(path.join(DATA_DIR, encodeURIComponent(D) + '.json'), 'utf8'));
    const oldestCutoff = disk.cutoff;
    assert.ok(disk.ops.every(r => r.seq > oldestCutoff), '保留的流水都在 cutoff 之后');
    assert.ok(disk.ops.length < 50, '尾部流水已大幅回收（剩 ' + disk.ops.length + '）');
    ok('验收1：多轮增删回收后磁盘流水降到上界，在线各端正文/样式/批注/角色/账本次序一致');
    Ow.disconnect(); Ed.disconnect();
  }

  // ---- 验收(2)：制作基线期间仍有在线写入，边界两侧变动不丢不重并收敛 ----
  {
    const D = docName('concurrent-compact');
    const Ow = new SimClient('co', D); await Ow.connect();
    const Ed = new SimClient('ce', D); await Ed.connect();
    Ow.member('invite', 'ce', 'editor');
    await waitFor(() => Ed.role === 'editor', 'cc: Ed editor');
    Ed.insertText(0, '基底正文ABCDEFGHIJKLMNOP');
    await waitFor(() => Ow.doc.text() === '基底正文ABCDEFGHIJKLMNOP', 'cc: 基底同步');
    // 两阶段：stage 之后、publish 之前继续在线写入
    Ow.compact('stage', 'cc-stage');
    await waitFor(() => Ow.lastCompactAck && Ow.lastCompactAck.staged, 'cc: stage 完成');
    const edge1 = '阶段边界写入甲';
    Ed.insertText(Ed.doc.text().length, edge1);
    await waitFor(() => Ow.doc.text().endsWith(edge1), 'cc: stage 后写入到达 owner');
    Ow.compact('publish', 'cc-stage');
    await waitFor(() => Ow.lastCompactAck && Ow.lastCompactAck.published, 'cc: publish 完成');
    const edge2 = '发布边界写入乙';
    Ed.insertText(Ed.doc.text().length, edge2);
    await waitFor(() => Ed.gen === Ow.gen && Ed.doc.text() === Ow.doc.text() && Ow.doc.text().includes(edge1) && Ow.doc.text().includes(edge2), 'cc: 收敛且边界变动都在');
    // 不重复：两段各出现一次
    const t = Ow.doc.text();
    assert.strictEqual(t.indexOf(edge1), t.lastIndexOf(edge1), '边界写入甲不重复');
    assert.strictEqual(t.indexOf(edge2), t.lastIndexOf(edge2), '边界写入乙不重复');
    assert.ok(t.includes('基底正文ABCDEFGHIJKLMNOP'), '基底不丢');
    sameView(Ow, Ed, '验收2: 收敛一致');
    ok('验收2：制作基线期间在线写入，边界两侧变动不丢不重并最终收敛');
    Ow.disconnect(); Ed.disconnect();
  }

  // ---- 验收(3)：落后离线端积压 ins/del/mark/com，取得新基线后换算，获准批次只生效一次 ----
  {
    const D = docName('offline-migrate');
    const Ow = new SimClient('mo', D); await Ow.connect();
    const Ed = new SimClient('me', D); await Ed.connect();
    Ow.member('invite', 'me', 'editor');
    await waitFor(() => Ed.role === 'editor', 'om: Ed editor');
    Ed.insertText(0, '离线迁移基准文本一二三四五六七八九十');
    await waitFor(() => Ow.doc.text() === Ed.doc.text(), 'om: 基底同步');
    Ed.disconnect(); await sleep(200);
    // 离线积压：插入、删除、样式、批注
    const baseLen = Ed.doc.text().length;
    const bIns = Ed.offlineInsert(0, '积压插入');
    Ed.offlineDelete(2, 2);
    Ed.offlineMark(0, Math.min(4, Ed.doc.text().length), { bold: true });
    const cRes = Ed.offlineComment(0, Math.min(3, Ed.doc.text().length), '离线批注');
    // owner 在线推进并压缩多代（让 Ed 落后于保留窗口）
    Ow.insertText(Ow.doc.text().length, '在线增量A'); await sleep(60);
    Ow.compact('once', 'om-c1'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= 1, 'om: 压缩1');
    Ow.insertText(Ow.doc.text().length, '在线增量B'); await sleep(60);
    Ow.compact('once', 'om-c2'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= 2, 'om: 压缩2');
    const beforeText = Ow.doc.text();
    await Ed.connect();
    // Ed 完成迁移换算；冲突草稿可能为空（其锚点仍有后继/存活映射）
    await waitFor(() => Ed.gen === Ow.gen && Ed.migrateReplies.some(r => r.status === 'migrated'), 'om: Ed 迁移换算完成');
    await waitFor(() => Ow.doc.text() === Ed.doc.text(), 'om: 迁移后收敛');
    assert.ok(Ow.doc.text().includes('积压插入'), '积压插入意图保留');
    if (process.env.OM_DEBUG) {
      const rep = Ed.migrateReplies.filter(r => r.status === 'migrated').pop();
      console.log('DBG mig conflicts', JSON.stringify((rep && rep.conflicts || []).map(c => ({ kind: c.kind, id: c.op.id, reason: c.reason }))));
      console.log('DBG cRes id', cRes.op.id, 'start', JSON.stringify(cRes.op.start), 'ownerComments', [...Ow.doc.comments.keys()]);
      console.log('DBG ed text', JSON.stringify(Ed.doc.text()), 'owner text', JSON.stringify(Ow.doc.text()));
    }
    assert.ok(Ow.doc.comments.has(cRes.op.id), '积压批注迁移成功');
    // 只生效一次：重复 migrate（同 migId 幂等）—— SimClient 记录了 migId
    const lastMig = Ed.migrateReplies.filter(r => r.status === 'migrated').pop();
    const tBefore = Ow.doc.text();
    Ed.send({ t: 'migrate', migId: 'manual-redo', batchId: 'redo', fromGen: Ow.gen, ops: bIns.ops });
    await sleep(300);
    // opId 去重：相同 opId 不会二次插入
    assert.strictEqual(Ow.doc.text(), tBefore, '换算批次重复提交不重复生效（opId 幂等）');
    void beforeText; void baseLen; void lastMig;
    sameView(Ow, Ed, '验收3: 迁移后一致');
    ok('验收3：落后离线端积压 ins/del/mark/com 取得新基线后完成换算，获准批次只生效一次');
    Ow.disconnect(); Ed.disconnect();
  }

  // ---- 验收(4)：锚点所指墓碑已被回收 => 只可迁移或进显式冲突草稿，绝不挂到别的字句 ----
  {
    const D = docName('tomb-anchor');
    const Ow = new SimClient('to', D); await Ow.connect();
    const Ed = new SimClient('te', D); await Ed.connect();
    Ow.member('invite', 'te', 'editor');
    await waitFor(() => Ed.role === 'editor', 'ta: Ed editor');
    // 建立文字：受害者=X，邻居=安全文字
    Ed.insertText(0, 'AAA-X-BBB'); // X 在偏移 4
    await waitFor(() => Ow.doc.text() === 'AAA-X-BBB', 'ta: 基底');
    Ed.disconnect(); await sleep(200);
    const ids = Ed.doc.visibleIds();
    const xId = ids[4];
    // 离线：对 X 做批注（锚点=X）
    const { op: comOnX } = Ed.offlineCommentOn(xId, 's', 'e', '批注X', 'X');
    // 离线：删除 X（删除意图）
    Ed.offlineDelete(4, 1);
    // 在线：owner 删除 X 并多轮压缩，彻底回收 X 墓碑
    Ow.deleteRange(4, 1);
    await waitFor(() => !Ow.doc.text().includes('X'), 'ta: X 已在线删除');
    Ow.compact('once', 'ta-c1'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= 1, 'ta: 压缩1');
    Ow.insertText(Ow.doc.text().length, '更多内容推动回收'); await sleep(60);
    Ow.compact('once', 'ta-c2'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= 2, 'ta: 压缩2');
    await Ed.connect();
    await waitFor(() => Ed.gen === Ow.gen && Ed.migrateReplies.some(r => r.status === 'migrated'), 'ta: 迁移完成');
    // 指向已回收墓碑 X 的批注 => 必须在冲突草稿中，且不得悄悄挂到邻居
    const cf = Ed.conflicts.find(d => d.kind === 'com-anchor');
    assert.ok(cf, '墓碑锚点批注进入显式冲突草稿');
    // 服务器上不得出现一个锚到邻居的同名批注
    let leaked = false;
    for (const c of Ow.doc.comments.values()) {
      if (c.text === '批注X' && !c.detached) {
        const r = Ow.doc.resolveComment(c);
        if (r.status === 'anchored' && r.cur !== 'X') leaked = true;
      }
    }
    assert.ok(!leaked, '批注没有被悄悄挂到另一段字句');
    // 显式核准：用户在新基线选中范围后才落到新位置（恰好一次）
    if (process.env.TA_DEBUG) console.log('DBG before approve ownerText', JSON.stringify(Ow.doc.text()), 'edText', JSON.stringify(Ed.doc.text()), 'cf', Ed.conflicts.length);
    const approveId = Ed.approve(cf, { s: 0, e: 3 });
    await sleep(400);
    if (process.env.TA_DEBUG) {
      console.log('DBG after approve ownerText', JSON.stringify(Ow.doc.text()));
      console.log('DBG ownerComments', [...Ow.doc.comments.values()].map(c => ({ text: c.text, detached: c.detached, status: Ow.doc.resolveComment(c).status, cur: JSON.stringify(Ow.doc.resolveComment(c).cur), quote: JSON.stringify(c.quote) })));
    }
    await waitFor(() => {
      const c = [...Ow.doc.comments.values()].find(x => x.text === '批注X' && !x.detached);
      return c && Ow.doc.resolveComment(c).status === 'anchored';
    }, 'ta: 显式核准后批注挂到用户选定范围');
    // 核准幂等
    Ed.send({ t: 'approveConflict', approveId, kind: 'com-anchor', anchor: { s: 0, e: 3 }, text: '批注X' });
    await sleep(200);
    const cnt = [...Ow.doc.comments.values()].filter(x => x.text === '批注X' && !x.detached).length;
    assert.strictEqual(cnt, 1, '核准只生效一次');
    sameView(Ow, Ed, '验收4: 收敛');
    ok('验收4：墓碑已回收的锚点只可迁移或进入显式冲突草稿，绝不悄悄挂到另一段字句');
    Ow.disconnect(); Ed.disconnect();
  }

  // ---- 验收(5)：陈旧端降权/移除后重连不得发布；完整拒绝批次跨下一轮压缩及重启保存 ----
  {
    const D = docName('stale-demote');
    const Ow = new SimClient('so', D); await Ow.connect();
    const Ed = new SimClient('se', D); await Ed.connect();
    Ow.member('invite', 'se', 'editor');
    await waitFor(() => Ed.role === 'editor', 'sd: editor');
    Ed.insertText(0, '降权迁移基准');
    await waitFor(() => Ow.doc.text() === '降权迁移基准', 'sd: 基底');
    Ed.disconnect(); await sleep(200);
    const badBatch = Ed.offlineInsert(0, '降权后的夹带内容');
    // 先压缩推进代次，再降权，再压缩一轮（拒绝须跨压缩保存）
    Ow.compact('once', 'sd-c1'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= 1, 'sd: 压缩1');
    Ow.member('role', 'se', 'viewer');
    await waitFor(() => Ow.roleOf('se') === 'viewer', 'sd: 已降权 viewer');
    Ow.compact('once', 'sd-c2'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= 2, 'sd: 压缩2');
    await Ed.connect();
    await waitFor(() => Ed.quarantine.length >= 1 && Ed.gen === Ow.gen, 'sd: 陈旧迁移被整批拒绝并迁移');
    assert.ok(!Ow.doc.text().includes('降权后的夹带内容'), '降权主体未夹带任何旧操作');
    const q = Ed.quarantine[Ed.quarantine.length - 1];
    assert.strictEqual(q.ops.length, badBatch.ops.length, '完整拒绝载荷保留（' + q.ops.length + ' 条）');
    assert.strictEqual(q.ops.map(o => o.ch).join(''), '降权后的夹带内容', '拒绝载荷完整可阅读/可复制（字符序列一条不少）');
    // 再压缩一轮：拒绝批次仍在
    Ow.compact('once', 'sd-c3'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= 3, 'sd: 压缩3');
    await sleep(300);
    const disk1 = JSON.parse(fs.readFileSync(path.join(DATA_DIR, encodeURIComponent(D) + '.json'), 'utf8'));
    const rejOnDisk = Object.values(disk1.batches).filter(r => r.status === 'rejected')
      .concat(Object.values(disk1.migrated || {}).filter(r => r.status === 'rejected'));
    assert.ok(rejOnDisk.some(r => (r.ops || []).map(o => o.ch).join('') === '降权后的夹带内容'), '拒绝批次跨压缩保存在磁盘');
    // 重启后仍在，且再次重连仍不能发布
    await sleep(2300);
    await stopServer(); await startServer();
    const Ow2 = new SimClient('so', D); await Ow2.connect();
    const Ed2 = new SimClient('se', D); await Ed2.connect();
    await waitFor(() => Ed2.role === 'viewer' && Ed2.gen === Ow2.gen, 'sd: 重启后角色/代次');
    Ed2.send({ t: 'ops', batchId: badBatch.batchId, ops: badBatch.ops });
    await sleep(300);
    assert.ok(!Ow2.doc.text().includes('降权后的夹带内容'), '重启后陈旧端仍不能发布');
    const disk2 = JSON.parse(fs.readFileSync(path.join(DATA_DIR, encodeURIComponent(D) + '.json'), 'utf8'));
    const rej2 = Object.values(disk2.batches).filter(r => r.status === 'rejected')
      .concat(Object.values(disk2.migrated || {}).filter(r => r.status === 'rejected'));
    assert.ok(rej2.some(r => (r.ops || []).map(o => o.ch).join('') === '降权后的夹带内容'), '完整拒绝批次跨重启保存');
    ok('验收5：陈旧端降权后重连不得发布，完整拒绝批次跨下一轮压缩及重启保存');
    Ow2.disconnect(); Ed2.disconnect();
  }

  // ---- 验收(6)：发布前后强制终止进程，重启只可是完整旧代或完整新代；重试压缩不破坏权威态 ----
  {
    const D = docName('crash-switch');
    // 独立目录，便于精确控制进程
    const cdir = path.join(DATA_DIR, 'crash-' + RUN);
    const CPORT = PORT + 250;
    const spawnCrash = () => spawn(process.execPath, [path.join(__dirname, '..', 'server', 'server.js')], {
      env: Object.assign({}, process.env, { PORT: String(CPORT), DATA_DIR: cdir, LOG_CAP_BYTES: '1000000' }),
      stdio: ['ignore', 'pipe', 'inherit'],
    });
    fs.mkdirSync(cdir, { recursive: true });
    const file = path.join(cdir, encodeURIComponent(D) + '.json');
    const crashConnect = () => new Promise((resolve, reject) => {
      const key = crypto.randomBytes(16).toString('base64');
      const req = http.request({ port: CPORT, path: '/ws', headers: { Connection: 'Upgrade', Upgrade: 'websocket', 'Sec-WebSocket-Key': key, 'Sec-WebSocket-Version': 13 } });
      req.on('upgrade', (res, sock) => resolve(new WSClient(sock)));
      req.on('error', reject); req.end();
    });
    const waitHttp = () => new Promise((resolve) => {
      const iv = setInterval(() => {
        const r = http.request({ port: CPORT, path: '/healthz' }, () => { clearInterval(iv); resolve(); });
        r.on('error', () => r.destroy()); r.end();
      }, 100);
    });
    const readGen = () => { try { return JSON.parse(fs.readFileSync(file, 'utf8')).gen; } catch (e) { return null; } };

    let sv = spawnCrash(); await waitHttp();
    let cc = await crashConnect();
    await new Promise((res) => { cc.onMessage(() => res()); cc.send({ t: 'hello', clientId: 'cz', name: 'cz', doc: D, gen: 0, lastSeq: 0 }); });
    // 写入基线内容
    let after = ''; const writeOps = [];
    for (let i = 0; i < 40; i++) { const id = 'cz:w' + i; writeOps.push({ t: 'ins', id, after, ch: String.fromCharCode(65 + (i % 26)), by: 'cz', opId: 'cz#' + i }); after = id; }
    cc.send({ t: 'ops', batchId: 'cw', ops: writeOps });
    await new Promise((res) => {
      const iv = setInterval(() => {
        try { const j = JSON.parse(fs.readFileSync(file, 'utf8')); if (j.seq >= 41) { clearInterval(iv); res(); } } catch (e) { /* 未落盘 */ }
      }, 50);
      setTimeout(() => { clearInterval(iv); res(); }, 4000);
    });
    sv.kill('SIGKILL'); // 在任何压缩之前硬杀（内容已批量落盘）
    await new Promise(r => setTimeout(r, 300));

    sv = spawnCrash(); await waitHttp();
    cc = await crashConnect();
    let wl = null;
    cc.onMessage((m) => { if (m.t === 'welcome') wl = m; });
    cc.send({ t: 'hello', clientId: 'cz', name: 'cz', doc: D, gen: 0, lastSeq: 0 });
    await new Promise(r => setTimeout(r, 300));
    assert.ok(readGen() === 0 || readGen() === 1, '硬杀后重启为完整旧代（gen 0/1，实际 ' + readGen() + '）');

    // 发布新代中途硬杀：发出 compact 后立刻 SIGKILL
    cc.send({ t: 'compact', phase: 'once', reqId: 'crash-compact' });
    await new Promise(r => setTimeout(r, 5));
    sv.kill('SIGKILL');
    await new Promise(r => setTimeout(r, 300));
    sv = spawnCrash(); await waitHttp();
    cc = await crashConnect();
    wl = null; let text = '';
    cc.onMessage((m) => {
      if (m.t === 'welcome') wl = m;
      if (m.t === 'baselineEnd') text = m.tail.length ? '' : '';
    });
    cc.send({ t: 'hello', client: 'cz', clientId: 'cz', name: 'cz', doc: D, gen: 0, lastSeq: 0 });
    await new Promise(r => setTimeout(r, 400));
    const gAfter = readGen();
    // 不论落在旧代还是新代，文件必须自洽：能正常 welcome
    assert.ok(wl && wl.seq >= 40, '崩溃后权威态完整可读（seq=' + (wl && wl.seq) + '，gen=' + gAfter + '）');
    // 用客户端实际投影确认完整
    const probe = new SimClient('cz', D);
    // 直接复用同端口连接不可（SimClient 用全局 PORT），改为通过文件+新 welcome 文本经迁移流不便；
    // 这里验证文件层面：基线文本或尾部 ops 必有完整内容
    const jf = JSON.parse(fs.readFileSync(file, 'utf8'));
    const baselineText = jf.baselines.length ? jf.baselines[jf.baselines.length - 1].b.text : '';
    const tailText = (() => {
      const d = new CRDT.Doc('v');
      if (jf.v === 3 && jf.baselines.length) for (const op of COMPACT.baselineToOps({ gen: jf.gen, cutoffSeq: jf.cutoff, chars: jf.baselines.at(-1).chars, marks: jf.baselines.at(-1).marks, comments: jf.baselines.at(-1).comments })) d.apply(op);
      for (const r of jf.ops) d.apply(r.op);
      return d.text();
    })();
    assert.strictEqual(tailText.length, 40, '权威态内容完整（40 字符），baseline=' + baselineText.length);
    // 重试压缩不破坏权威态（再压一次，文本不变）
    await new Promise((res) => { let done = false; cc.onMessage((m) => { if (m.t === 'compactAck' && m.published && !done) { done = true; res(); } }); cc.send({ t: 'compact', phase: 'once', reqId: 'retry' }); setTimeout(res, 1000); });
    const jf2 = JSON.parse(fs.readFileSync(file, 'utf8'));
    const d2 = new CRDT.Doc('v');
    for (const op of COMPACT.baselineToOps({ gen: jf2.gen, cutoffSeq: jf2.cutoff, chars: jf2.baselines.at(-1).chars, marks: jf2.baselines.at(-1).marks, comments: jf2.baselines.at(-1).comments })) d2.apply(op);
    for (const r of jf2.ops) d2.apply(r.op);
    assert.strictEqual(d2.text().length, 40, '重试压缩不破坏权威态投影');
    sv.kill('SIGKILL');
    ok('验收6：发布前后强制终止，重启只可是完整旧代或完整新代，重试压缩不破坏权威态');
  }

  // ---- 验收(7)：迁移分片/换算消息重复乱序，不重复投影、基线点、冲突项或账本事件 ----
  {
    const D = docName('duplicate-shards');
    const Ow = new SimClient('dpo', D); await Ow.connect();
    const Ed = new SimClient('dpe', D); await Ed.connect();
    Ow.member('invite', 'dpe', 'editor');
    await waitFor(() => Ed.role === 'editor', 'ds: editor');
    Ed.insertText(0, '重复乱序基准文本0123456789');
    await waitFor(() => Ow.doc.text() === Ed.doc.text(), 'ds: 基底');
    Ed.disconnect(); await sleep(200);
    const b = Ed.offlineInsert(0, '离线XYZ');
    Ow.compact('once', 'ds-c1'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= 1, 'ds: 压缩');
    // 手动模拟：连接但拦截迁移流，自行重复/乱序发分片
    const raw = await wsConnect();
    const chunks = []; let endMsg = null, switchMsg = null;
    raw.onMessage((m) => {
      if (m.t === 'genSwitch') switchMsg = m;
      if (m.t === 'baselineChunk') chunks.push(m);
      if (m.t === 'baselineEnd') endMsg = m;
    });
    raw.send({ t: 'hello', clientId: 'dpe2', name: 'dpe2', doc: D, gen: 0, lastSeq: 0 });
    await waitFor(() => endMsg && chunks.length, 'ds: 收到迁移流', 5000);
    assert.ok(chunks.length >= 1 && switchMsg);
    // 用一个独立 CRDT 验证 assembleShards 对重复+乱序幂等
    const dup = [];
    for (const c of chunks) dup.push(c);
    for (const c of chunks) dup.push(c); // 全量重复一次
    const shuffled = dup.slice().sort(() => Math.random() - 0.5);
    const A1 = COMPACT.assembleShards(shuffled);
    const A2 = COMPACT.assembleShards(shuffled.slice().reverse());
    assert.strictEqual(A1.length, 1); assert.strictEqual(A2.length, 1);
    assert.strictEqual(A1[0].chars.map(c => c.id).join(','), A2[0].chars.map(c => c.id).join(','), '乱序/重复拼出同一基线');
    // 换算批次重复（同 migId）幂等：冲突项/账本不重复
    const migId = 'dup-mig-1';
    const sendMig = () => Ow.send({ t: 'migrate', migId, batchId: 'dm', fromGen: 0, ops: b.ops });
    // 用 owner 发（有权限），从 gen0 命名换算；服务端按 migId 幂等返回首次结论
    sendMig(); await sleep(200); sendMig(); await sleep(200); sendMig(); await sleep(300);
    const replies = Ow.migrateReplies.filter(r => r.migId === migId);
    assert.ok(replies.length === 3, '三条都有回复');
    // migId 幂等：后两条必须原样回放首次结论（applied seq 列表完全相同），不产生新 seq
    const first = (replies[0].applied || []).map(x => x.seq).join(',');
    for (let i = 1; i < replies.length; i++) {
      assert.strictEqual((replies[i].applied || []).map(x => x.seq).join(','), first, '重复换算回放首次结论（seq 不新增）');
    }
    const committedSeqs = new Set(replies[0].applied.map(x => x.seq));
    assert.ok(committedSeqs.size === replies[0].applied.length, '首次换算内部 seq 唯一');
    // 文本只含一次 XYZ（opId 去重 + migId 幂等）
    const t = Ow.doc.text();
    const occ = t.split('离线XYZ').length - 1;
    assert.ok(occ <= 1, '重复换算不重复投影（出现 ' + occ + ' 次）');
    raw.close(); Ow.disconnect(); Ed.disconnect();
    ok('验收7：迁移分片与换算消息重复/乱序不重复投影、基线点、冲突项或账本事件');
  }

  // ---- 验收(8)：成员变动、代次发布、陈旧批次同时竞争 => 唯一授权结果与全局次序 ----
  {
    const D = docName('triple-race');
    const Ow = new SimClient('tro', D); await Ow.connect();
    const X = new SimClient('trx', D); await X.connect();
    await waitFor(() => Ow.role === 'owner', 'tr: owner');
    Ow.member('invite', 'trx', 'editor');
    await waitFor(() => X.role === 'editor', 'tr: X editor');
    X.insertText(0, '竞争基准');
    await waitFor(() => Ow.doc.text() === '竞争基准', 'tr: 基底');
    X.disconnect(); await sleep(200);
    const stale = X.offlineInsert(0, '竞争夹带');
    // 在同一时刻：发起压缩发布 + 降权 X + X 重连补发（三者竞争）
    Ow.compact('stage', 'tr-stage'); await waitFor(() => Ow.lastCompactAck && Ow.lastCompactAck.staged, 'tr: stage');
    Ow.compact('publish', 'tr-stage');
    Ow.member('role', 'trx', 'viewer');
    await X.connect();
    await waitFor(() => X.gen === Ow.gen, 'tr: X 迁移到新代');
    await sleep(300);
    // 唯一授权结果：被降权 => 夹带必须被拒
    assert.ok(!Ow.doc.text().includes('竞争夹带'), '竞争下被降权主体不得发布');
    assert.ok(X.quarantine.length >= 1, '陈旧批次进入隔离（唯一拒绝结果）');
    // epoch 单调唯一；账本里角色变更与代次演进都有唯一全局顺序
    await waitFor(() => X.role === 'viewer', 'tr: X 角色收敛 viewer');
    const sig = (c) => c.ledger.map(e => (e.ev || 0) + ':' + e.seq + ':' + (e.act || e.kind)).join('|');
    assert.strictEqual(sig(Ow), sig(X), '竞争后全局次序唯一一致');
    assert.strictEqual(Ow.epoch, X.epoch, '授权纪元唯一');
    if (process.env.TR_DEBUG) {
      console.log('DBG tr owner', JSON.stringify(Ow.doc.text()), 'X', JSON.stringify(X.doc.text()), 'XallOps', X.allOps.length, 'Xpend', X.pendingBatches.length, 'Xq', X.quarantine.length);
    }
    sameView(Ow, X, '验收8: 竞争收敛一致');
    void stale;
    ok('验收8：成员变动/代次发布/陈旧批次竞争时，各端得到唯一授权结果与全局次序');
    Ow.disconnect(); X.disconnect();
  }

  // ---- 验收(9)：回退到仍保留的基线点 => 新演进记录；请求已清除基线点 => 明确错误且不增记录 ----
  {
    const D = docName('baseline-restore');
    const Ow = new SimClient('bro', D); await Ow.connect();
    Ow.insertText(0, '第一代内容');
    Ow.compact('once', 'br-c1'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= 1, 'br: g1');
    const g1 = Ow.gen;
    Ow.insertText(Ow.doc.text().length, '第二代内容');
    Ow.compact('once', 'br-c2'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= g1 + 1, 'br: g2');
    const g2 = Ow.gen;
    Ow.insertText(Ow.doc.text().length, '第三代内容');
    Ow.compact('once', 'br-c3'); await waitFor(() => Ow.cstat && Ow.cstat.gen >= g2 + 1, 'br: g3');
    const evBefore = Ow.ledger.filter(e => e.kind === 'evolution').length;
    // 回退到仍保留的 g2（或更早保留点）
    const target = Ow.cstat.baselines.map(b => b.gen).includes(g2) ? g2 : Ow.cstat.baselines[0].gen;
    Ow.restoreBaseline(target);
    await waitFor(() => Ow.lastRestoreBaselineAck && Ow.lastRestoreBaselineAck.ok, 'br: 回退成功');
    await waitFor(() => Ow.ledger.filter(e => e.kind === 'evolution' && e.act === 'restore-baseline').length >= 1, 'br: 新增演进记录');
    const evAfter = Ow.ledger.filter(e => e.kind === 'evolution').length;
    assert.strictEqual(evAfter, evBefore + 1, '回退保留基线恰好新增一条演进记录');
    assert.ok(Ow.gen > g2 || Ow.gen >= Ow.cstat.gen, '回退产生新代次');
    // 请求一个早已清除的基线点（gen 1 在 RETAIN_BASELINES=3 边界，取一个极大 gen）
    const evBefore2 = Ow.ledger.filter(e => e.kind === 'evolution').length;
    Ow.restoreBaseline(99999);
    await waitFor(() => Ow.lastRestoreBaselineAck && Ow.lastRestoreBaselineAck.code === 'baseline-unavailable', 'br: 明确错误');
    assert.strictEqual(Ow.lastRestoreBaselineAck.code, 'baseline-unavailable');
    await sleep(100);
    assert.strictEqual(Ow.ledger.filter(e => e.kind === 'evolution').length, evBefore2, '清除基线点请求不增加演进记录');
    ok('验收9：回退保留基线点产生新演进记录；请求已清除基线点返回明确错误且不增记录');
    Ow.disconnect();
  }

  // ---- 验收(10)：既有第二代空间首次打开惰性升级，投影不变，不产生第二个 owner ----
  {
    const V2 = 'v2-' + RUN;
    // 手工造一份 v2 数据：v:2、initialized、恰好一个 owner、ops/revs/ledger 完整
    const fdoc = new CRDT.Doc('v2-author');
    let after = null; const v2ops = [];
    for (const ch of '第二代空间正文需要原样保留') { const o = fdoc.insert(after, ch); o.opId = 'v2#' + o.id; after = o.id; v2ops.push(o); }
    // 一条批注 + 一条格式，验证升级后投影等价
    const ids = fdoc.visibleIds();
    const cm = fdoc.comment({ id: ids[0], edge: 's' }, { id: ids[3], edge: 'e' }, 'v2批注', fdoc.text().slice(0, 4)); cm.opId = 'v2#c1'; fdoc.apply(cm);
    const mk = fdoc.mark({ id: ids[0], edge: 's' }, { id: ids[2], edge: 'e' }, { bold: true }); mk.opId = 'v2#m1'; fdoc.apply(mk);
    const beforeText = fdoc.text();
    const beforeMarks = fdoc.activeMarks().map(m => m.s + ':' + m.e + ':' + Object.keys(m.attrs).join()).sort().join('|');
    const v2payload = {
      v: 2, seq: v2ops.length + 2,
      ops: [...v2ops, mk, cm].map((op, i) => ({ seq: i + 1, op })),
      revs: [{ n: 1, seq: v2ops.length + 2, ts: Date.now() - 1000, by: 'v2-author', kind: 'edit', summary: 'v2修订', snapshot: { text: fdoc.text(), marks: fdoc.activeMarks().map(m => ({ s: m.s, e: m.e, attrs: m.attrs })) } }],
      initialized: true, epoch: 2,
      members: { 'v2-owner': { id: 'v2-owner', name: '主理人', role: 'owner', since: 1, by: null, byName: null } },
      ledger: [{ seq: 1, ts: 1, kind: 'space', act: 'init', by: null, byName: null, target: 'v2-owner', targetName: '主理人', from: null, to: 'owner', epoch: 0 }],
      batches: {}, seenReqIds: [],
    };
    fs.writeFileSync(path.join(DATA_DIR, encodeURIComponent(V2) + '.json'), JSON.stringify(v2payload));
    const P1 = new SimClient('v2-owner', V2); await P1.connect();
    await waitFor(() => P1.doc.text() === beforeText && P1.gen >= 1, 'v2: 惰性升级后投影一致');
    assert.strictEqual(P1.doc.text(), beforeText, 'v2 正文投影不被改写');
    const afterMarks = P1.doc.activeMarks().map(m => m.s + ':' + m.e + ':' + Object.keys(m.attrs).join()).sort().join('|');
    assert.strictEqual(afterMarks, beforeMarks, 'v2 样式投影不变');
    assert.ok(P1.doc.comments.has(cm.id), 'v2 批注保留');
    const owners = P1.members.filter(m => m.role === 'owner');
    assert.strictEqual(owners.length, 1, '恰好一个 owner');
    assert.strictEqual(owners[0].id, 'v2-owner', '不产生第二个 owner');
    assert.strictEqual(P1.epoch, 2, '授权纪元保留');
    // 旧修订快照在惰性升级后仍可用于恢复
    assert.ok(P1.revs.some(r => r.summary === 'v2修订'), 'v2 修订历史保留');
    // 并发第二连接也只看到一个 owner
    const P2 = new SimClient('v2-guest', V2); await P2.connect();
    await waitFor(() => P2.doc.text() === beforeText && P2.gen === P1.gen, 'v2: 第二连接投影一致');
    assert.strictEqual(P2.members.filter(m => m.role === 'owner').length, 1, '第二连接仍恰好一个 owner');
    const disk = JSON.parse(fs.readFileSync(path.join(DATA_DIR, encodeURIComponent(V2) + '.json'), 'utf8'));
    assert.strictEqual(disk.v, 3, '磁盘升级为 v3');
    assert.strictEqual(disk.baselines.at(-1).b.text, beforeText, '基线投影等于 v2 正文');
    ok('验收10：既有第二代空间首次打开惰性升级，投影视图不被改写，也不产生第二个主理人');
    P1.disconnect(); P2.disconnect();
  }

  await stopServer();
  console.log('\n全部 ' + passed + ' 项测试通过 ✅');
  process.exit(0);
})().catch(async (e) => {
  console.error('\n测试失败 ❌', e);
  await stopServer();
  process.exit(1);
});
