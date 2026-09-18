/* global CRDT, AUTHZ, COMPACT */
'use strict';
/*
 * 前端逻辑（v3：代次压缩 + 快照迁移 + 基线换算）
 * - 本地即真：编辑先应用到本地 CRDT，再以批次异步同步；断网批次留在本地
 * - 角色治理：owner/editor/commenter/viewer；服务端最终授权；整批越权 => 隔离草稿（显式重提）
 * - 代次迁移：服务端压缩发布新基线后（或 hello 发现自己落后），接收
 *   genSwitch -> baselineChunk*（可重复/乱序，按片幂等拼装）-> baselineEnd；
 *   重置到新基线后，把积压批次合并为一条 migrate（fromGen）提交换算：
 *   可投射的保留意图只生效一次；无法映射的锚点进入「迁移冲突草稿」，绝不悄悄挂到别的字句，
 *   必须本人显式核准（在新基线选定新位置）后才再次提交。
 * - 水位/租约：定期上报 (gen,lastSeq)；界面展示各镜像端水位与压缩状态。
 */
(() => {
  const $ = (s) => document.querySelector(s);
  const docName = new URLSearchParams(location.search).get('doc') || 'default';
  const clientId = localStorage.getItem('cid') ||
    (crypto.randomUUID ? crypto.randomUUID() : 'c-' + Math.random().toString(36).slice(2));
  localStorage.setItem('cid', clientId);
  let myName = localStorage.getItem('cname') || clientId.slice(0, 8);
  const LS_KEY = 'collab3:' + docName;
  const LOCAL_OPS_CAP = 20000;

  const doc = new CRDT.Doc(clientId);
  let lastSeq = 0, opSeq = 0, allOps = [];
  let pendingBatches = []; // [{ batchId, ops }]
  let quarantine = [];     // 授权拒绝批次
  let conflictDrafts = []; // 迁移换算冲突 [{ draftId, migId, kind, op, reason, anchor, ts, approved }]
  let revs = [], ledger = [], members = [], peers = [];
  let myRole = 'viewer', member = false, epoch = 0, initialized = false;
  let gen = 0, cutoff = 0, cstat = null;
  let mig = null;          // { reason, fromGen, toGen, pieces: Map, cutoffSeq }
  let ws = null, online = false, reconnectDelay = 500;
  let curText = '';
  let reattachFor = null;
  let pendingCommentRange = null;
  let composing = false;
  let approveFor = null;   // 待核准的冲突草稿（等待用户在文档上选新范围）

  // ---------- 本地持久化 ----------
  function saveLocal() {
    try {
      if (allOps.length > LOCAL_OPS_CAP) { localStorage.removeItem(LS_KEY); return; }
      localStorage.setItem(LS_KEY, JSON.stringify({
        v: 3, lastSeq, opSeq, allOps, pendingBatches, quarantine, conflictDrafts,
        revs, ledger, members, epoch, myRole, member, gen, cutoff,
      }));
    } catch (e) { /* 存储满则忽略 */ }
  }
  let saveTimer = null;
  function saveLocalSoon() { clearTimeout(saveTimer); saveTimer = setTimeout(saveLocal, 300); }
  (function loadLocal() {
    try {
      const j = JSON.parse(localStorage.getItem(LS_KEY) || 'null');
      if (!j) return;
      if (j.v === 3 || j.v === 2) {
        lastSeq = j.lastSeq || 0; opSeq = j.opSeq || 0;
        allOps = j.allOps || []; pendingBatches = j.pendingBatches || [];
        quarantine = j.quarantine || []; conflictDrafts = j.conflictDrafts || [];
        revs = j.revs || []; ledger = j.ledger || []; members = j.members || [];
        epoch = j.epoch || 0; myRole = j.myRole || 'viewer'; member = !!j.member;
        gen = j.gen || 0; cutoff = j.cutoff || 0;
      }
      for (const op of allOps) doc.apply(op);
      for (const b of pendingBatches) for (const op of b.ops) doc.apply(op);
    } catch (e) { /* 忽略损坏缓存 */ }
  })();

  // ---------- 网络 ----------
  function connect() {
    const proto = location.protocol === 'https:' ? 'wss' : 'ws';
    ws = new WebSocket(proto + '://' + location.host + '/ws');
    ws.onopen = () => {
      online = true; reconnectDelay = 500; setStatus();
      ws.send(JSON.stringify({ t: 'hello', clientId, name: myName, doc: docName, lastSeq, gen }));
    };
    ws.onmessage = (ev) => { try { handle(JSON.parse(ev.data)); } catch (e) { console.error(e); } };
    ws.onclose = () => {
      online = false; setStatus();
      setTimeout(connect, reconnectDelay);
      reconnectDelay = Math.min(reconnectDelay * 2, 8000);
    };
    ws.onerror = () => { try { ws.close(); } catch (e) { /* ignore */ } };
  }
  function send(obj) { if (online && ws && ws.readyState === 1) ws.send(JSON.stringify(obj)); }
  function reportWatermark() { send({ t: 'watermark', gen, lastSeq }); }

  function upsertRev(rev) {
    if (!rev) return;
    const i = revs.findIndex(r => r.n === rev.n);
    if (i >= 0) revs[i] = rev; else revs.push(rev);
  }
  function upsertLedgerEntry(e) {
    if (!e || ledger.some(x => x.seq === e.seq && x.act === e.act && x.target === e.target && x.ev === e.ev)) return;
    ledger.push(e);
    ledger.sort((a, b) => (a.seq - b.seq) || ((a.ev || 0) - (b.ev || 0)));
    if (ledger.length > 3000) ledger.splice(0, ledger.length - 3000);
  }
  function applyMyState(newRole, newMember, newEpoch, newMembers) {
    const before = myRole;
    myRole = newRole; member = newMember;
    epoch = newEpoch; members = newMembers || members;
    if (before !== myRole) {
      const label = AUTHZ.LABELS[myRole] || myRole;
      setHint('你的角色已变更为：' + label, myRole === 'viewer' && before !== 'viewer');
    }
  }

  // ---------- 代次迁移 ----------
  function beginMigration(reason, fromGen, toGen, shards) {
    mig = { reason, fromGen: fromGen == null ? gen : fromGen, toGen, pieces: new Map(), total: shards || 0 };
    setHint('空间已发布新基线代次 g' + toGen + '，正在迁移快照…');
  }
  function finishMigration(endMsg) {
    if (!mig) return;
    const received = [];
    for (const s of mig.pieces.values()) received.push(s);
    const assembled = COMPACT.assembleShards(received);
    const base = assembled.find(b => b.gen === mig.toGen) || assembled[assembled.length - 1];
    if (!base) { mig = null; return; }
    // 权威重置：新基线 + 尾部流水（积压的待确认批次稍后经 migrate 换算）
    doc.clear();
    const baseLike = { gen: base.gen, cutoffSeq: base.cutoffSeq, chars: base.chars, marks: base.marks, comments: base.comments };
    const baseOps = COMPACT.baselineToOps(baseLike);
    for (const op of baseOps) doc.apply(op);
    for (const r of endMsg.tail || []) doc.apply(r.op);
    allOps = baseOps.concat((endMsg.tail || []).map(r => r.op));
    gen = endMsg.gen; cutoff = endMsg.cutoffSeq;
    lastSeq = endMsg.seq;
    revs = endMsg.revs || revs;
    ledger = [];
    for (const e of endMsg.ledger || []) upsertLedgerEntry(e);
    members = endMsg.members || members;
    epoch = endMsg.epoch || epoch;
    const me = members.find(m => m.id === clientId);
    applyMyState(me ? me.role : 'viewer', !!me, epoch, members);
    const m = mig;
    mig = null;
    renderAll(); saveLocalSoon(); reportWatermark();
    // 把积压批次（引用旧基线）合并为一条 migrate 提交换算，保证批次内引用可解析
    flushMigration(m);
  }
  function flushMigration(m) {
    const ops = [];
    for (const b of pendingBatches) for (const op of b.ops) ops.push(op);
    if (!ops.length) return;
    const migId = clientId + '#mig#' + (++opSeq) + '-' + Date.now().toString(36);
    pendingBatches = []; // 乐观内容已随基线重置；换算结论决定它们如何回到文档
    send({ t: 'migrate', migId, batchId: 'coalesced-' + migId, fromGen: m.fromGen, ops });
    window.__lastMigId = migId;
  }

  function handle(msg) {
    if (msg.t === 'welcome') {
      gen = msg.gen || 0; cutoff = msg.cutoff || 0; cstat = msg;
      if (msg.needMigration) {
        // 服务器会紧接 genSwitch/分片流；这里只记录治理态，正文等基线到达再重建
        lastSeq = Math.max(lastSeq, msg.seq || 0);
        revs = msg.revs || revs;
        ledger = []; for (const e of msg.ledger || []) upsertLedgerEntry(e);
        members = msg.members || members; epoch = msg.epoch || epoch;
        const me = members.find(m => m.id === clientId);
        applyMyState(me ? me.role : 'viewer', !!me, epoch, members);
        initialized = !!msg.initialized;
        renderAll(); saveLocalSoon();
        return;
      }
      lastSeq = Math.max(lastSeq, msg.seq || 0);
      const seen = new Set();
      for (const { seq, op } of msg.ops) {
        doc.apply(op); allOps.push(op);
        lastSeq = Math.max(lastSeq, seq);
        if (op.opId) seen.add(op.opId);
      }
      for (const e of msg.ledger || []) { upsertLedgerEntry(e); lastSeq = Math.max(lastSeq, e.seq); }
      revs = msg.revs || revs;
      for (const r of revs) lastSeq = Math.max(lastSeq, r.seq);
      pendingBatches = pendingBatches.filter(b => {
        b.ops = b.ops.filter(op => !seen.has(op.opId));
        return b.ops.length > 0;
      });
      const role = msg.role || 'viewer';
      applyMyState(role, !!msg.member, msg.epoch || 0, msg.members || []);
      initialized = !!msg.initialized;
      for (const b of pendingBatches) send({ t: 'ops', batchId: b.batchId, ops: b.ops });
      if (msg.initEntry && msg.initEntry.target === clientId) setHint('你是这个空间的所有者，可以邀请协作者并分配角色。');
      else if (!msg.member) setHint('你尚未被邀请加入此空间，当前为只读。把你的用户 ID 发给所有者即可受邀。');
      renderAll(); saveLocalSoon(); reportWatermark();
    } else if (msg.t === 'genSwitch') {
      beginMigration(msg.reason, msg.fromGen, msg.toGen, msg.shards);
    } else if (msg.t === 'baselineChunk') {
      if (!mig) beginMigration('chunk', null, msg.gen, msg.shards);
      mig.pieces.set(msg.shard, msg); // 幂等：重复片覆盖无副作用
      if (mig.pieces.size >= msg.shards && mig.pieces.has(msg.shards - 1 >= 0 ? msg.shards - 1 : 0)) { /* 等 baselineEnd 收口 */ }
    } else if (msg.t === 'baselineEnd') {
      if (!mig) beginMigration(msg.reason, null, msg.gen, 0);
      mig.toGen = msg.gen;
      finishMigration(msg);
    } else if (msg.t === 'ops') {
      const applied = Array.isArray(msg.applied) ? msg.applied : [];
      for (const { seq, op } of applied) {
        doc.apply(op); allOps.push(op);
        lastSeq = Math.max(lastSeq, seq);
      }
      if (msg.batchId && !msg.migrated) dropPending(msg.batchId, applied);
      else dropPendingOps(applied);
      upsertRev(msg.rev);
      if (msg.rev) lastSeq = Math.max(lastSeq, msg.rev.seq);
      if (msg.gen != null) gen = msg.gen;
      renderAll(); saveLocalSoon(); reportWatermark();
    } else if (msg.t === 'batchAck') {
      if (msg.status === 'rejected') {
        lastSeq = Math.max(lastSeq, msg.atSeq || 0);
        if (msg.code === 'migration-required') { setHint('本地代次落后，正在获取新基线后自动换算…', true); return; }
        quarantineBatch(msg.batchId, msg);
      } else {
        for (const { seq, op } of msg.applied || []) {
          doc.apply(op); allOps.push(op);
          lastSeq = Math.max(lastSeq, seq);
        }
        dropPending(msg.batchId, msg.applied || []);
        upsertRev(msg.rev);
        if (msg.rev) lastSeq = Math.max(lastSeq, msg.rev.seq);
      }
      renderAll(); saveLocalSoon(); reportWatermark();
    } else if (msg.t === 'migrateAck') {
      handleMigrateAck(msg);
    } else if (msg.t === 'approveAck') {
      if (!msg.ok) setHint(msg.message || '核准未被接受', true);
      else {
        for (const d of conflictDrafts) if (d.approveId === msg.approveId) d.approved = true;
        for (const { seq, op } of msg.appliedOps || []) { doc.apply(op); allOps.push(op); lastSeq = Math.max(lastSeq, seq); }
        if (msg.applied === false && msg.resolved) setHint('该删除意图在新基线已成立，已显式消解。');
        else setHint('冲突草稿已按你的明确核准在新基线上生效（仅一次）。');
      }
      renderAll(); saveLocalSoon();
    } else if (msg.t === 'members') {
      upsertLedgerEntry(msg.entry);
      if (msg.entry) lastSeq = Math.max(lastSeq, msg.entry.seq);
      const newMembers = msg.members || members;
      const me = newMembers.find(m => m.id === clientId);
      applyMyState(me ? me.role : 'viewer', !!me, msg.epoch, newMembers);
      if (msg.entry && msg.entry.target === clientId) {
        const txt = AUTHZ.transitionText(msg.entry);
        if (txt) setHint(txt, true);
      }
      renderAll(); saveLocalSoon();
    } else if (msg.t === 'memberAck') {
      if (msg.epoch != null) {
        const newMembers = msg.members || members;
        const me = newMembers.find(m => m.id === clientId);
        applyMyState(me ? me.role : myRole, !!me, msg.epoch, newMembers);
        renderAll(); saveLocalSoon();
      }
    } else if (msg.t === 'compactionStatus') {
      cstat = msg; gen = msg.gen; cutoff = msg.cutoff;
      renderCompaction(); setStatus();
    } else if (msg.t === 'compactAck') {
      if (!msg.ok) { setHint('压缩失败：' + (msg.message || msg.code), true); renderCompaction(); }
      else if (msg.published) setHint('已原子切换到新基线代次 g' + msg.gen + '，投影不变，旧流水已回收。');
      else if (msg.staged) setHint('基线已制作（stage），等待发布。');
      send({ t: 'compactionStatus' });
    } else if (msg.t === 'restoreBaselineAck') {
      if (msg.ok) setHint('已回退到保留的基线点并演进为 g' + msg.gen + '。');
      else setHint(msg.message || '该基线点不可用', true);
    } else if (msg.t === 'presence') {
      peers = msg.peers || [];
      $('#presence').textContent = msg.count + ' 人在线';
      renderPeers();
    } else if (msg.t === 'error') {
      const loud = msg.code === 'forbidden-rollback' || msg.code === 'forbidden-membership' || msg.code === 'baseline-unavailable';
      setHint(msg.message || '操作被拒绝', loud);
    }
  }

  function handleMigrateAck(msg) {
    if (msg.status === 'rejected') {
      // 迁移批次仍按当前 epoch 裁决：降权/移除 => 整批进入隔离，完整可读、可复制。
      // 合并迁移涵盖全部积压：清空待发队列，本地只从已确认操作重建，被拒乐观内容不留在投影里。
      lastSeq = Math.max(lastSeq, msg.atSeq || 0);
      let ops = msg.ops || [];
      if (!ops.length) for (const b of pendingBatches) ops = ops.concat(b.ops);
      pendingBatches = [];
      quarantine.push({
        draftId: 'd-' + Date.now().toString(36),
        batchId: msg.batchId || msg.migId, ops,
        reason: msg.reason || '迁移批次按当前授权纪元被拒绝', role: msg.role, need: msg.need,
        kinds: msg.kinds || {}, epoch: msg.epoch, atSeq: msg.atSeq, rejectedTs: Date.now(), migrated: true,
      });
      rebuildLocal();
      setHint('积压批次在新授权纪元下被整批拒绝，已进入隔离草稿，未发布任何内容。', true);
    } else {
      for (const { seq, op } of msg.applied || []) {
        doc.apply(op); allOps.push(op); lastSeq = Math.max(lastSeq, seq);
      }
      upsertRev(msg.rev);
      if (msg.rev) lastSeq = Math.max(lastSeq, msg.rev.seq);
      if (msg.gen != null) gen = msg.gen;
      for (const c of msg.conflicts || []) addConflictDraft(msg.migId, c);
      if ((msg.conflicts || []).length) setHint('有 ' + msg.conflicts.length + ' 条积压操作的锚点无法映射，已进入显式冲突草稿（不会悄悄挂到别处）。', true);
    }
    renderAll(); saveLocalSoon(); reportWatermark();
  }
  function addConflictDraft(migId, c) {
    if (conflictDrafts.some(d => d.migId === migId && d.op && c.op && d.op.opId === c.op.opId && d.kind === c.kind)) return;
    conflictDrafts.push({
      draftId: 'cf-' + Date.now().toString(36) + '-' + Math.random().toString(36).slice(2, 6),
      approveId: null, migId, kind: c.kind, op: c.op, reason: c.reason, anchor: c.anchor, ts: Date.now(), approved: false,
    });
  }

  function dropPendingOps(applied) {
    const ids = new Set((applied || []).map(x => x.op && x.op.opId).filter(Boolean));
    if (!ids.size) return;
    pendingBatches = pendingBatches.filter(b => {
      b.ops = b.ops.filter(op => !ids.has(op.opId));
      return b.ops.length > 0;
    });
  }
  function dropPending(batchId, applied) {
    const i = pendingBatches.findIndex(b => b.batchId === batchId);
    if (i < 0) { dropPendingOps(applied); return; }
    pendingBatches.splice(i, 1);
    dropPendingOps(applied);
  }

  function quarantineBatch(batchId, info) {
    const i = pendingBatches.findIndex(b => b.batchId === batchId);
    let ops = null;
    if (i >= 0) { ops = pendingBatches[i].ops; pendingBatches.splice(i, 1); }
    if (quarantine.some(q => q.batchId === batchId)) return;
    if (!ops) ops = info.ops || (info.kinds ? new Array((info.kinds.prose || 0) + (info.kinds.annotate || 0)).fill(null) : []);
    let transition = null;
    for (let k = ledger.length - 1; k >= 0; k--) {
      const e = ledger[k];
      if (e.target === clientId && e.kind === 'membership' && e.seq <= (info.atSeq || Infinity)) { transition = e; break; }
    }
    quarantine.push({
      draftId: 'd-' + Date.now().toString(36) + '-' + Math.random().toString(36).slice(2, 8),
      batchId, ops: ops.filter(Boolean),
      reason: info.reason || '操作被服务端拒绝',
      role: info.role || myRole, need: info.need || null, kinds: info.kinds || {},
      epoch: info.epoch != null ? info.epoch : epoch, atSeq: info.atSeq || null,
      transition: transition ? { act: transition.act, from: transition.from, to: transition.to, by: transition.byName, seq: transition.seq } : null,
      rejectedTs: Date.now(),
    });
    rebuildLocal();
    setHint('一批操作被拒绝（' + (AUTHZ.LABELS[info.role] || info.role) + '），已原样放入「隔离草稿」，未进入共享文档。', true);
  }
  function rebuildLocal() {
    doc.clear();
    for (const op of allOps) doc.apply(op);
    for (const b of pendingBatches) for (const op of b.ops) doc.apply(op);
  }

  function newBatchId() { return clientId + '#' + (++opSeq) + '#b' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6); }
  function pushOps(ops) {
    const batch = [];
    for (const op of ops) {
      if (!op) continue;
      op.opId = clientId + '#' + (++opSeq);
      doc.apply(op);
      batch.push(op);
    }
    if (batch.length) {
      const b = { batchId: newBatchId(), ops: batch };
      pendingBatches.push(b);
      send({ t: 'ops', batchId: b.batchId, ops: batch });
      saveLocalSoon();
    }
    return true;
  }

  // ---------- 编辑器 <-> CRDT ----------
  const ed = $('#editor');
  function localEdit(nt) {
    const ot = curText;
    let p = 0;
    while (p < ot.length && p < nt.length && ot[p] === nt[p]) p++;
    let s = 0;
    while (s < ot.length - p && s < nt.length - p && ot[ot.length - 1 - s] === nt[nt.length - 1 - s]) s++;
    const ids = doc.visibleIds();
    const ops = [];
    for (let i = p; i < ot.length - s; i++) ops.push(doc.remove(ids[i]));
    let after = p > 0 ? ids[p - 1] : null;
    for (const ch of nt.slice(p, nt.length - s)) { const op = doc.insert(after, ch); after = op.id; ops.push(op); }
    pushOps(ops);
    curText = nt;
  }
  ed.addEventListener('compositionstart', () => { composing = true; });
  ed.addEventListener('compositionend', () => { composing = false; localEdit(ed.textContent); render(); });
  ed.addEventListener('input', () => {
    if (composing) return;
    if (ed.textContent === curText) return;
    localEdit(ed.textContent); render();
  });
  ed.addEventListener('paste', (e) => {
    if (!AUTHZ.can(myRole, 'prose')) { e.preventDefault(); setHint('只读/评论者不能修改正文。', true); return; }
    e.preventDefault();
    document.execCommand('insertText', false, (e.clipboardData || window.clipboardData).getData('text/plain'));
  });
  ed.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
      e.preventDefault();
      if (AUTHZ.can(myRole, 'prose')) document.execCommand('insertText', false, '\n');
      else setHint('只读/评论者不能修改正文。', true);
      return;
    }
    if (!AUTHZ.can(myRole, 'prose') && ed.isContentEditable &&
        (e.key.length === 1 || ['Backspace', 'Delete', 'Cut'].includes(e.key))) {
      e.preventDefault(); setHint('只读/评论者不能修改正文。', true);
    }
  });

  // ---------- 选区 ----------
  function offsetOf(node, off) {
    if (node === ed) {
      let acc = 0;
      for (let i = 0; i < off && i < ed.childNodes.length; i++) acc += ed.childNodes[i].textContent.length;
      return acc;
    }
    const w = document.createTreeWalker(ed, NodeFilter.SHOW_TEXT);
    let n, acc = 0;
    while ((n = w.nextNode())) { if (n === node) return acc + off; acc += n.textContent.length; }
    return acc;
  }
  function getCaret() {
    const sel = window.getSelection();
    if (!sel.rangeCount || !ed.contains(sel.anchorNode)) return null;
    return offsetOf(sel.anchorNode, sel.anchorOffset);
  }
  function setCaret(off) {
    if (off == null) return;
    off = Math.min(off, ed.textContent.length);
    const w = document.createTreeWalker(ed, NodeFilter.SHOW_TEXT);
    let n, acc = 0;
    while ((n = w.nextNode())) {
      const l = n.textContent.length;
      if (acc + l >= off) {
        const sel = window.getSelection();
        const r = document.createRange();
        r.setStart(n, off - acc); r.collapse(true);
        sel.removeAllRanges(); sel.addRange(r);
        return;
      }
      acc += l;
    }
  }
  function getSelRange() {
    const sel = window.getSelection();
    if (!sel.rangeCount) return null;
    const r = sel.getRangeAt(0);
    if (!ed.contains(r.startContainer) || !ed.contains(r.endContainer)) return null;
    const s = offsetOf(r.startContainer, r.startOffset);
    const e = offsetOf(r.endContainer, r.endOffset);
    if (s === e) return null;
    return [Math.min(s, e), Math.max(s, e)];
  }
  function anchorsFor(s, e) {
    const ids = doc.visibleIds();
    const st = s <= 0 ? { id: null, edge: 's' } : { id: ids[s], edge: 's' };
    const en = e >= ids.length ? { id: null, edge: 'e' } : { id: ids[e - 1], edge: 'e' };
    return [st, en];
  }

  // ---------- 渲染 ----------
  function esc(s) { return String(s == null ? '' : s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c])); }
  function segments() {
    const text = doc.text();
    const bounds = new Set([0, text.length]);
    const marks = [], coms = [];
    for (const m of doc.activeMarks()) { bounds.add(m.s); bounds.add(m.e); marks.push(m); }
    for (const c of doc.commentList()) {
      if (c.resolved) continue;
      const r = doc.resolveComment(c);
      if (r.e > r.s) { bounds.add(r.s); bounds.add(r.e); coms.push({ id: c.id, s: r.s, e: r.e, status: r.status }); }
    }
    const pts = [...bounds].sort((a, b) => a - b);
    const segs = [];
    for (let i = 0; i < pts.length - 1; i++) {
      const s = pts[i], e = pts[i + 1];
      const byKey = {};
      for (const m of marks) {
        if (m.s <= s && m.e >= e) {
          for (const k in m.attrs) {
            const prev = byKey[k];
            if (!prev || m.ts > prev.ts || (m.ts === prev.ts && m.by > prev.by)) byKey[k] = { v: m.attrs[k], ts: m.ts, by: m.by };
          }
        }
      }
      const attrs = {};
      for (const k in byKey) attrs[k] = byKey[k].v;
      const covering = coms.filter(c => c.s <= s && c.e >= e);
      segs.push({ s, e, text: text.slice(s, e), attrs, cids: covering.map(c => c.id), cstatus: covering.length ? covering[0].status : null });
    }
    return { text, segs };
  }
  function render() {
    const { text, segs } = segments();
    let html = '';
    for (const g of segs) {
      const cls = [];
      if (g.attrs.bold) cls.push('b');
      if (g.attrs.italic) cls.push('i');
      if (g.attrs.underline) cls.push('u');
      if (g.cids.length) cls.push('chl', 'cs-' + g.cstatus);
      const data = g.cids.length ? ' data-cids="' + g.cids.join(',') + '"' : '';
      html += cls.length ? '<span class="' + cls.join(' ') + '"' + data + '>' + esc(g.text) + '</span>' : esc(g.text);
    }
    if (ed.innerHTML !== html) { const caret = getCaret(); ed.innerHTML = html; setCaret(caret); }
    curText = text;
    applyGating();
  }

  const STATUS_INFO = {
    'anchored': ['已锚定', 'ok'],
    'split-insert': ['已拆分 · 插入了新内容', 'warn'],
    'split-delete': ['部分悬空 · 部分锚定文字被删除', 'warn'],
    'orphan-deleted': ['悬空 · 锚定文字已被删除', 'bad'],
    'detached-compacted': ['压缩回收 · 需显式重新挂接', 'bad'],
    'changed': ['已变更 · 锚定文字被修改', 'warn'],
    'resolved': ['已解决', 'muted'],
  };

  function renderComments() {
    const box = $('#comments');
    const list = doc.commentList().sort((a, b) => b.ts - a.ts);
    box.innerHTML = '';
    if (!list.length) { box.innerHTML = '<div class="empty">暂无评论。选中文字后点击"评论选中文字"。</div>'; return; }
    const canNote = AUTHZ.can(myRole, 'annotate');
    for (const c of list) {
      const r = doc.resolveComment(c);
      const [label, cls] = STATUS_INFO[r.status] || ['未知', 'muted'];
      const card = document.createElement('div');
      card.className = 'card';
      card.dataset.cid = c.id;
      let inner = '<div class="head"><span><span class="who">' + esc(c.by) + '</span>' +
        '<span class="badge ' + cls + '">' + label + '</span></span>' +
        '<span class="time">' + new Date(c.ts).toLocaleString() + '</span></div>';
      inner += '<div class="quote"><span class="lbl">原始锚定文字</span>' + (c.quote ? esc(c.quote) : '（空）') + '</div>';
      if (r.status === 'detached-compacted') inner += '<div class="cur">⚠ ' + esc(r.reason || '压缩回收了锚点，批注未挂到任何其他字句。') + '</div>';
      else if (r.status !== 'anchored' && r.status !== 'resolved') inner += '<div class="cur"><span class="lbl">当前覆盖文字</span>' + (r.cur ? esc(r.cur) : '（已被删除）') + '</div>';
      inner += '<div class="ctext">' + esc(c.text) + '</div><div class="ops"></div>';
      card.innerHTML = inner;
      const ops = card.querySelector('.ops');
      if (!c.resolved) {
        if (canNote) {
          const re = document.createElement('button');
          re.textContent = '重新挂接';
          re.title = '在新基线上选择新的文字范围（显式操作，不会自动挂载）';
          re.onclick = () => { reattachFor = c.id; setHint('请在文档中选中新的锚定文字…'); ed.focus(); };
          ops.appendChild(re);
          const done = document.createElement('button');
          done.textContent = '标记解决';
          done.onclick = () => pushOps([doc.updateComment(c.id, { resolved: true })]) || renderAll();
          ops.appendChild(done);
        }
      } else if (canNote) {
        const reopen = document.createElement('button');
        reopen.textContent = '重新打开';
        reopen.onclick = () => pushOps([doc.updateComment(c.id, { resolved: false })]) || renderAll();
        ops.appendChild(reopen);
      }
      box.appendChild(card);
    }
  }

  function renderRevs() {
    const box = $('#revs');
    box.innerHTML = '';
    if (!revs.length) { box.innerHTML = '<div class="empty">暂无修订记录。</div>'; return; }
    const isOwner = myRole === 'owner';
    for (const r of [...revs].sort((a, b) => b.n - a.n)) {
      const div = document.createElement('div');
      div.className = 'rev ' + (r.kind === 'baseline' ? 'baseline' : '');
      const kind = r.kind === 'restore' ? '<span class="kind-restore">恢复</span> 至 #' + r.target
        : r.kind === 'baseline' ? '<span class="kind-base">基线 g' + r.gen + '</span>'
        : r.kind === 'migrate' ? '<span class="kind-mig">迁移</span>'
        : r.kind === 'approve' ? '<span class="kind-mig">核准</span>' : '编辑';
      div.innerHTML = '<span class="n">#' + r.n + '</span><div class="body">' +
        '<div class="sum">' + esc(r.summary) + '</div>' +
        '<div class="sub">' + kind + ' · seq ' + r.seq + ' · ' + esc(r.by) + ' · ' + new Date(r.ts).toLocaleString() + '</div></div>';
      if (isOwner && r.kind !== 'baseline' && r.snapshot) {
        const btn = document.createElement('button');
        btn.textContent = '恢复此版本';
        btn.onclick = () => { if (confirm('恢复到修订 #' + r.n + '？将作为新修订合并。')) send({ t: 'restore', rev: r.n }); };
        div.appendChild(btn);
      }
      box.appendChild(div);
    }
  }

  function renderLedger() {
    const box = $('#ledger');
    const revBySeq = new Map();
    for (const r of revs) revBySeq.set(r.seq, r);
    const rows = [];
    for (const e of ledger) rows.push({ seq: e.seq, ev: e.ev || 0, kind: 'entry', e });
    for (const r of revs) rows.push({ seq: r.fromSeq || r.seq, ev: 0, kind: 'rev', r });
    rows.sort((a, b) => (b.seq - a.seq) || (b.ev - a.ev));
    box.innerHTML = '';
    if (!rows.length) { box.innerHTML = '<div class="empty">暂无记录。</div>'; return; }
    for (const row of rows.slice(0, 400)) {
      const div = document.createElement('div');
      div.className = 'ledger ' + row.kind;
      if (row.kind === 'rev') {
        const r = row.r;
        div.innerHTML = '<span class="lseq">seq ' + r.seq + '</span><span class="ltag rev">修订 #' + r.n + '</span>' +
          '<span class="lbody">' + esc(r.summary) + ' · ' + esc(r.by) + '</span>';
      } else {
        const e = row.e;
        let tag, detail;
        if (e.kind === 'evolution') {
          tag = '代次演进';
          detail = (e.act === 'upgrade-v2v3' ? 'v2→v3 惰性升级' : e.act === 'restore-baseline' ? '回退基线 g' + e.targetGen : '压缩发布') +
            ' → g' + e.gen + '（cutoff seq ' + e.cutoffSeq + '）';
        } else if (e.kind === 'space') {
          tag = e.act === 'upgrade' ? '空间升级' : '空间创建';
          detail = esc(e.targetName || e.target) + ' 成为所有者';
        } else {
          tag = { invite: '邀请', role: '角色变更', remove: '移除' }[e.act] || '成员变更';
          const who = e.targetName || e.target;
          detail = e.act === 'remove' ? '移除 ' + esc(who) + '（原 ' + (AUTHZ.LABELS[e.from] || e.from) + '）'
            : esc(who) + '：' + (AUTHZ.LABELS[e.from] || e.from || '—') + ' → ' + (AUTHZ.LABELS[e.to] || e.to);
        }
        div.innerHTML = '<span class="lseq">seq ' + e.seq + '</span><span class="ltag ' + (e.kind || 'membership') + '">' + tag +
          '</span><span class="lbody">' + detail + ' · by ' + esc(e.byName || e.by || '系统') + ' · epoch ' + e.epoch + '</span>';
        if (e.target === clientId) div.classList.add('me');
      }
      box.appendChild(div);
    }
  }

  // ---------- 成员面板 ----------
  function reqId() { return clientId + '#req#' + (crypto.randomUUID ? crypto.randomUUID() : Math.random().toString(36).slice(2)); }
  function sendMember(act, target, role, name) { send({ t: 'member', reqId: reqId(), act, target, role, name }); }
  function renderMembers() {
    const box = $('#members');
    box.innerHTML = '';
    const isOwner = myRole === 'owner';
    for (const m of members) {
      const div = document.createElement('div');
      div.className = 'member' + (m.id === clientId ? ' me' : '');
      const roleSel = isOwner && !(m.role === 'owner' && m.id === clientId)
        ? '<select class="mrole" data-id="' + esc(m.id) + '">' +
          AUTHZ.ROLES.map(r => '<option value="' + r + '"' + (r === m.role ? ' selected' : '') + '>' + AUTHZ.LABELS[r] + '</option>').join('') + '</select>'
        : '<span class="mrole-static ' + m.role + '">' + AUTHZ.LABELS[m.role] + '</span>';
      div.innerHTML = '<span class="mname">' + esc(m.name) + (m.id === clientId ? '（我）' : '') + '</span>' +
        '<span class="mid" title="' + esc(m.id) + '">' + esc(m.id.slice(0, 10)) + '…</span>' + roleSel;
      if (isOwner && !(m.role === 'owner' && m.id === clientId)) {
        const rm = document.createElement('button');
        rm.className = 'mremove'; rm.textContent = '移除';
        rm.onclick = () => sendMember('remove', m.id);
        div.appendChild(rm);
      }
      box.appendChild(div);
    }
    if (!members.length) box.innerHTML = '<div class="empty">尚未初始化。</div>';
    box.querySelectorAll('select.mrole').forEach(sel => sel.addEventListener('change', () => sendMember('role', sel.dataset.id, sel.value)));
    $('#admin').classList.toggle('hidden', !isOwner);
    $('#epochTag').textContent = 'epoch ' + epoch;
  }
  function renderPeers() {
    const box = $('#peers');
    box.innerHTML = '';
    const isOwner = myRole === 'owner';
    const onlineNonMembers = peers.filter(p => !p.member);
    if (!onlineNonMembers.length) return;
    const title = document.createElement('div');
    title.className = 'admin-title'; title.textContent = '在线未邀请';
    box.appendChild(title);
    for (const p of onlineNonMembers) {
      const div = document.createElement('div');
      div.className = 'member peer';
      div.innerHTML = '<span class="mname">' + esc(p.name) + '</span><span class="mid" title="' + esc(p.id) + '">' + esc(p.id.slice(0, 10)) + '…</span>';
      if (isOwner) for (const role of ['editor', 'commenter', 'viewer']) {
        const b = document.createElement('button');
        b.className = 'qinvite'; b.textContent = '邀为' + AUTHZ.LABELS[role];
        b.onclick = () => sendMember('invite', p.id, role, p.name);
        div.appendChild(b);
      }
      box.appendChild(div);
    }
  }

  // ---------- 隔离草稿 ----------
  function describeOps(ops) {
    const parts = [];
    for (const op of ops) {
      if (!op) continue;
      if (op.t === 'ins') parts.push('插入「' + esc(op.ch) + '」');
      else if (op.t === 'del') parts.push('删除字符 ' + esc(op.id.slice(-12)));
      else if (op.t === 'mark') parts.push('样式变更 ' + esc(JSON.stringify(op.attrs)));
      else if (op.t === 'com') parts.push((op.resolved ? '批注解决/重挂' : '批注') + '：「' + esc((op.quote || '').slice(0, 24)) + '」');
    }
    return parts;
  }
  function canResubmit(q) { return AUTHZ.can(myRole, q.kinds && q.kinds.prose ? 'prose' : 'annotate'); }
  function renderQuarantine() {
    const sec = $('#quarantineSection');
    sec.classList.toggle('hidden', !quarantine.length);
    $('#qCount').textContent = quarantine.length ? quarantine.length : '';
    const box = $('#quarantine');
    box.innerHTML = '';
    for (const q of quarantine) {
      const parts = describeOps(q.ops);
      const card = document.createElement('div');
      card.className = 'qcard';
      let html = '<div class="qhead"><span class="qrole">' + esc(AUTHZ.LABELS[q.role] || q.role) + ' 提交被拒</span>' +
        '<span class="qtime">' + new Date(q.rejectedTs).toLocaleString() + '</span></div>';
      html += '<div class="qreason">⛔ ' + esc(q.reason) + '</div>';
      if (q.transition) html += '<div class="qtr">角色变化（seq ' + q.transition.seq + '）：' + esc(AUTHZ.transitionText(q.transition) || '') + '；epoch ' + q.epoch + '</div>';
      html += '<div class="qops"><div class="qlbl">被保留的操作（共 ' + q.ops.length + ' 条，未进入共享文档）：</div><ul>' +
        parts.map(p => '<li>' + p + '</li>').join('') + '</ul></div>';
      card.innerHTML = html;
      const row = document.createElement('div'); row.className = 'qopsrow';
      const copy = document.createElement('button');
      copy.textContent = '复制操作 JSON';
      copy.onclick = async () => {
        const text = JSON.stringify(q.ops, null, 2);
        try { await navigator.clipboard.writeText(text); } catch (e) {
          const ta = document.createElement('textarea'); ta.value = text; document.body.appendChild(ta);
          ta.select(); document.execCommand('copy'); ta.remove();
        }
        setHint('已复制 ' + q.ops.length + ' 条操作的 JSON');
      };
      row.appendChild(copy);
      const view = document.createElement('button');
      view.textContent = '展开原文';
      view.onclick = () => { const pre = card.querySelector('pre.qjson'); if (pre) { pre.remove(); return; } pre = document.createElement('pre'); pre.className = 'qjson'; pre.textContent = JSON.stringify(q.ops, null, 2); card.appendChild(pre); };
      row.appendChild(view);
      const resub = document.createElement('button');
      const allowed = canResubmit(q);
      resub.className = 'qresub';
      resub.textContent = allowed ? '显式重新提交整批' : '权限不足，无法重提';
      resub.disabled = !allowed;
      resub.onclick = () => {
        if (!online || !canResubmit(q)) { setHint('离线或权限不足，不能重提。', true); return; }
        quarantine = quarantine.filter(x => x.draftId !== q.draftId);
        const b = { batchId: newBatchId(), ops: q.ops };
        pendingBatches.push(b);
        send({ t: 'ops', batchId: b.batchId, ops: b.ops });
        saveLocalSoon(); renderAll();
      };
      row.appendChild(resub);
      card.appendChild(row);
      box.appendChild(card);
    }
  }

  // ---------- 迁移冲突草稿（显式核准） ----------
  function renderConflicts() {
    const sec = $('#conflictSection');
    sec.classList.toggle('hidden', !conflictDrafts.some(d => !d.approved));
    $('#cfCount').textContent = conflictDrafts.filter(d => !d.approved).length || '';
    const box = $('#conflicts');
    box.innerHTML = '';
    for (const d of conflictDrafts) {
      if (d.approved) continue;
      const card = document.createElement('div');
      card.className = 'qcard cf';
      const typeLabel = { 'ins-after': '插入位置丢失', 'del-reclaimed': '删除目标已回收', 'mark-anchor': '样式锚点回收', 'com-anchor': '批注锚点回收' }[d.kind] || d.kind;
      card.innerHTML = '<div class="qhead"><span class="qrole">迁移冲突 · ' + esc(typeLabel) + '</span>' +
        '<span class="qtime">' + new Date(d.ts).toLocaleString() + '</span></div>' +
        '<div class="qreason">⚠ ' + esc(d.reason) + '</div>' +
        '<pre class="qjson">' + esc(JSON.stringify(d.op, null, 2)) + '</pre>';
      const row = document.createElement('div'); row.className = 'qopsrow';
      const copy = document.createElement('button');
      copy.textContent = '复制操作 JSON';
      copy.onclick = async () => { try { await navigator.clipboard.writeText(JSON.stringify(d.op, null, 2)); setHint('已复制冲突操作 JSON'); } catch (e) { /* ignore */ } };
      row.appendChild(copy);
      const approveId = 'ap-' + d.draftId;
      d.approveId = approveId;
      if (d.kind === 'del-reclaimed') {
        const btn = document.createElement('button');
        btn.className = 'qresub'; btn.textContent = '显式确认：删除意图已满足，消解此条';
        btn.onclick = () => send({ t: 'approveConflict', approveId, kind: 'del-reclaimed' });
        row.appendChild(btn);
      } else {
        const btn = document.createElement('button');
        btn.className = 'qresub';
        btn.textContent = d.kind === 'com-anchor' ? '在文档中选中新范围后点此核准批注' : '在文档中选中新位置/范围后点此核准';
        btn.disabled = !AUTHZ.can(myRole, d.kind === 'com-anchor' ? 'annotate' : 'prose');
        btn.onclick = () => {
          if (btn.disabled) { setHint('当前角色无权核准此类操作。', true); return; }
          const range = getSelRange();
          if (!range) { setHint('请先在文档里选中新的位置/范围，再点核准（系统不会替你猜挂到哪里）。', true); return; }
          approveFor = { d, range, approveId };
          submitApprove();
        };
        row.appendChild(btn);
      }
      card.appendChild(row);
      box.appendChild(card);
    }
  }
  function submitApprove() {
    const { d, range, approveId } = approveFor;
    const [s, e] = range;
    if (d.kind === 'ins-after') {
      const ids = doc.visibleIds();
      const after = s <= 0 ? { id: null, edge: 's' } : { id: ids[s - 1], edge: 'e' };
      send({ t: 'approveConflict', approveId, kind: 'ins-after', ch: d.op.ch, anchor: after });
    } else if (d.kind === 'mark-anchor') {
      send({ t: 'approveConflict', approveId, kind: 'mark-anchor', anchor: { s, e }, attrs: d.op.attrs || {} });
    } else if (d.kind === 'com-anchor') {
      send({ t: 'approveConflict', approveId, kind: 'com-anchor', anchor: { s, e }, text: d.op.text || '', quote: doc.text().slice(s, e) });
    }
    approveFor = null;
  }

  // ---------- 压缩 / 代次面板 ----------
  function renderCompaction() {
    const s = cstat; if (!s) return;
    $('#genTag').textContent = '代次 g' + s.gen;
    $('#seqRange').textContent = '保留序号区间 seq [' + s.retainedSeq[0] + ' .. ' + s.retainedSeq[1] + ']（cutoff ' + s.cutoff + '）';
    $('#logBytes').textContent = '磁盘流水 ' + Math.round(s.logBytes / 1024) + ' KB / 上限 ' + Math.round(s.logCapBytes / 1024) + ' KB';
    const wbox = $('#watermarks');
    wbox.innerHTML = '';
    for (const w of s.watermarks || []) {
      const div = document.createElement('div');
      div.className = 'wm' + (w.current ? ' current' : '') + (w.leased ? '' : ' stale');
      div.innerHTML = '<span class="wmname">' + esc(w.name) + '</span>' +
        '<span class="wmpos">g' + w.gen + ' · seq ' + w.lastSeq + (w.current ? ' · 当前' : ' · 落后') + '</span>' +
        '<span class="wmlease">' + (w.leased ? '租约有效' : '租约过期') + '</span>';
      wbox.appendChild(div);
    }
    const err = $('#compactError');
    if (s.lastCompactError) { err.classList.remove('hidden'); err.textContent = '⚠ 最近压缩失败（' + (s.lastCompactError.phase || '') + '）：' + esc(s.lastCompactError.message || ''); }
    else err.classList.add('hidden');
    const bl = $('#baselineList');
    bl.innerHTML = (s.baselines || []).map(b =>
      '<span class="bl" title="cutoff seq ' + b.cutoffSeq + '">' +
      'g' + b.gen + ' <small>' + new Date(b.ts).toLocaleTimeString() + ' · ' + b.chars + ' 字符</small>' +
      (myRole === 'owner' ? ' <button data-gen="' + b.gen + '" class="rbBtn">回退</button>' : '') + '</span>').join(' ');
    bl.querySelectorAll && bl.querySelectorAll('.rbBtn').forEach(btn => btn.addEventListener('click', () => {
      if (confirm('回退到保留的基线 g' + btn.dataset.gen + '？将产生一条新的代次演进记录。')) {
        send({ t: 'restoreBaseline', gen: +btn.dataset.gen });
      }
    }));
    $('#compactAdmin').classList.toggle('hidden', myRole !== 'owner');
  }

  // ---------- 门禁 / 状态 ----------
  function applyGating() {
    const editable = AUTHZ.can(myRole, 'prose');
    if (ed.isContentEditable !== editable) ed.contentEditable = editable ? 'true' : 'false';
    ed.classList.toggle('readonly', !editable);
    document.querySelectorAll('#toolbar [data-fmt]').forEach(b => { b.disabled = !editable; });
    $('#commentBtn').disabled = !AUTHZ.can(myRole, 'annotate');
    const badge = $('#roleBadge');
    badge.textContent = (AUTHZ.LABELS[myRole] || myRole) + (member ? '' : '（未邀请）') + ' · ' + docName;
    badge.className = 'rolebadge ' + myRole;
  }
  function setStatus() {
    const el = $('#status');
    el.className = online ? 'online' : 'offline';
    const nP = pendingBatches.reduce((a, b) => a + b.ops.length, 0);
    $('#statusText').textContent = online
      ? '已连接 g' + gen + (nP ? ' · 同步中(' + nP + ')' : '') + (mig ? ' · 迁移中' : '')
      : '离线 · 编辑已保存在本地' + (nP ? '（待同步 ' + nP + ' 条）' : '');
  }
  let hintTimer = null;
  function setHint(t, loud) {
    const el = $('#hint');
    el.textContent = t || '';
    el.classList.toggle('loud', !!loud);
    clearTimeout(hintTimer);
    if (t) hintTimer = setTimeout(() => { el.textContent = ''; el.classList.remove('loud'); }, 9000);
  }
  function renderAll() {
    render(); renderComments(); renderRevs(); renderLedger();
    renderMembers(); renderPeers(); renderQuarantine(); renderConflicts();
    renderCompaction(); applyGating(); setStatus();
  }

  // ---------- 工具栏 ----------
  function selAttrs(s, e) {
    const { segs } = segments();
    const res = { bold: true, italic: true, underline: true };
    let any = false;
    for (const g of segs) {
      if (g.e <= s || g.s >= e) continue;
      any = true;
      for (const k in res) res[k] = res[k] && !!g.attrs[k];
    }
    return any ? res : { bold: false, italic: false, underline: false };
  }
  document.querySelectorAll('#toolbar [data-fmt]').forEach(btn => btn.addEventListener('click', () => {
    if (!AUTHZ.can(myRole, 'prose')) { setHint('只有编辑或所有者可以修改样式。', true); return; }
    const range = getSelRange();
    if (!range) { setHint('请先选中一段文字'); return; }
    const key = btn.dataset.fmt;
    const cur = selAttrs(range[0], range[1]);
    const [st, en] = anchorsFor(range[0], range[1]);
    pushOps([doc.mark(st, en, { [key]: !cur[key] })]);
    renderAll();
  }));
  $('#commentBtn').addEventListener('click', () => {
    if (!AUTHZ.can(myRole, 'annotate')) { setHint('评论者或更高角色才能创建批注。', true); return; }
    const range = getSelRange();
    if (!range) { setHint('请先选中要评论的文字'); return; }
    pendingCommentRange = range;
    $('#ncQuote').textContent = doc.text().slice(range[0], range[1]);
    $('#newComment').classList.remove('hidden');
    $('#ncText').value = ''; $('#ncText').focus();
  });
  $('#ncCancel').addEventListener('click', () => { pendingCommentRange = null; $('#newComment').classList.add('hidden'); });
  $('#ncSubmit').addEventListener('click', () => {
    const text = $('#ncText').value.trim();
    if (!text || !pendingCommentRange) return;
    const [s, e] = pendingCommentRange;
    const [st, en] = anchorsFor(s, e);
    pushOps([doc.comment(st, en, text, doc.text().slice(s, e))]);
    pendingCommentRange = null; $('#newComment').classList.add('hidden'); renderAll();
  });
  ed.addEventListener('mouseup', () => {
    if (!reattachFor) return;
    if (!AUTHZ.can(myRole, 'annotate')) { reattachFor = null; setHint('评论者或更高角色才能重新挂接批注。', true); return; }
    const range = getSelRange();
    if (!range) return;
    const [s, e] = range;
    const [st, en] = anchorsFor(s, e);
    pushOps([doc.updateComment(reattachFor, { start: st, end: en, quote: doc.text().slice(s, e) })]);
    setHint('批注已显式重新挂接到：「' + (doc.text().slice(s, e).slice(0, 20)) + '」');
    reattachFor = null; renderAll();
  });
  ed.addEventListener('click', (e) => {
    const span = e.target.closest && e.target.closest('.chl');
    if (!span) return;
    const cid = (span.dataset.cids || '').split(',')[0];
    const card = document.querySelector('.card[data-cid="' + cid + '"]');
    if (card) { card.scrollIntoView({ block: 'nearest' }); card.classList.add('flash'); setTimeout(() => card.classList.remove('flash'), 1200); }
  });

  // ---------- 身份 / 所有者操作 ----------
  const nameInput = $('#myName');
  nameInput.value = myName;
  $('#myId').textContent = 'ID: ' + clientId;
  nameInput.addEventListener('change', () => {
    myName = nameInput.value.trim().slice(0, 80) || clientId;
    nameInput.value = myName;
    localStorage.setItem('cname', myName);
    if (online) send({ t: 'hello', clientId, name: myName, doc: docName, lastSeq, gen });
  });
  $('#inviteBtn').addEventListener('click', () => {
    if (myRole !== 'owner') { setHint('只有所有者可以邀请成员。', true); return; }
    sendMember('invite', $('#inviteId').value.trim(), $('#inviteRole').value);
    $('#inviteId').value = '';
  });
  $('#compactBtn').addEventListener('click', () => {
    if (myRole !== 'owner') { setHint('只有所有者可以压缩流水。', true); return; }
    send({ t: 'compact', phase: 'once', reqId: reqId() });
  });
  $('#compactStatusBtn').addEventListener('click', () => send({ t: 'compactionStatus' }));

  window.addEventListener('beforeunload', saveLocal);
  setInterval(saveLocal, 5000);
  setInterval(reportWatermark, 15000);

  renderAll();
  connect();
})();
