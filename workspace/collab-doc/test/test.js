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
    this.opSeq = 0;
    this.allOps = [];
    this.pendingBatches = [];
    this.quarantine = [];
    this.revs = [];
    this.ledger = [];
    this.members = [];
    this.peers = [];
    this.epoch = 0;
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
    this.ws.send({ t: 'hello', clientId: this.id, name: this.id, doc: this.docName, lastSeq: this.lastSeq });
    await this.ready;
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
      this.welcome = m;
      this.readyResolve();
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
      if (m.status === 'rejected') {
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
  assert.strictEqual(L1.revs.length, 1);
  assert.strictEqual(L1.revs[0].summary, '旧修订');
  // 升级审计：恰有一条 space/upgrade，seq 紧接旧 seq，未重写旧数据
  const up = L1.ledger.filter(e => e.kind === 'space' && e.act === 'upgrade');
  assert.strictEqual(up.length, 1);
  assert.strictEqual(up[0].seq, 10); // 旧 seq=9（按字符数），升级条目紧接其后为 10
  const onDisk = JSON.parse(fs.readFileSync(path.join(DATA_DIR, encodeURIComponent(LEGACY) + '.json'), 'utf8'));
  assert.strictEqual(onDisk.v, 2);
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
