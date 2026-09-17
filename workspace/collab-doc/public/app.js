/* global CRDT, AUTHZ */
'use strict';
/*
 * 前端逻辑：
 * - 本地即真：编辑先应用到本地 CRDT，再以「批次」（batchId）异步同步；断网时批次留在本地
 * - 角色治理：owner / editor / commenter / viewer，UI 按角色禁用；服务端为最终授权方
 * - 原子授权冲突：断连期间被降权/移除后重连，整批会被服务端拒绝；被拒操作不进入共享状态，
 *   原样保留在可读、可复制的「隔离草稿」中，必须由用户显式重新提交（权限恢复后）
 * - 批次幂等：重试用同一 batchId；重新提交保留原 opId 但换新 batchId => 恰好生效一次
 */
(() => {
  const $ = (s) => document.querySelector(s);
  const docName = new URLSearchParams(location.search).get('doc') || 'default';
  const clientId = localStorage.getItem('cid') ||
    (crypto.randomUUID ? crypto.randomUUID() : 'c-' + Math.random().toString(36).slice(2));
  localStorage.setItem('cid', clientId);
  let myName = localStorage.getItem('cname') || clientId.slice(0, 8);
  const LS_KEY = 'collab2:' + docName;
  const LOCAL_OPS_CAP = 20000;

  const doc = new CRDT.Doc(clientId);
  let lastSeq = 0, opSeq = 0, allOps = [];
  let pendingBatches = []; // [{ batchId, ops }] 已本地应用、等待/正在确认
  let quarantine = [];     // 被服务端拒绝的批次草稿（持久化，仅显式重提）
  let revs = [], ledger = [], members = [], peers = [];
  let myRole = 'viewer', member = false, epoch = 0, initialized = false;
  let ws = null, online = false, reconnectDelay = 500;
  let curText = '';
  let reattachFor = null;
  let pendingCommentRange = null;
  let composing = false;

  // ---------- 本地持久化（离线可编辑 + 隔离草稿不丢） ----------
  function saveLocal() {
    try {
      if (allOps.length > LOCAL_OPS_CAP) { localStorage.removeItem(LS_KEY); return; }
      localStorage.setItem(LS_KEY, JSON.stringify({
        v: 2, lastSeq, opSeq, allOps, pendingBatches, quarantine,
        revs, ledger, members, epoch, myRole, member,
      }));
    } catch (e) { /* 存储满则忽略 */ }
  }
  let saveTimer = null;
  function saveLocalSoon() { clearTimeout(saveTimer); saveTimer = setTimeout(saveLocal, 300); }
  (function loadLocal() {
    try {
      const j = JSON.parse(localStorage.getItem(LS_KEY) || 'null');
      if (!j) return;
      if (j.v === 2) {
        lastSeq = j.lastSeq || 0; opSeq = j.opSeq || 0;
        allOps = j.allOps || []; pendingBatches = j.pendingBatches || []; quarantine = j.quarantine || [];
        revs = j.revs || []; ledger = j.ledger || []; members = j.members || [];
        epoch = j.epoch || 0; myRole = j.myRole || 'viewer'; member = !!j.member;
      } else if (Array.isArray(j.pending)) {
        // v1 本地缓存：旧的散列待发操作打包成一个批次
        allOps = j.allOps || []; lastSeq = j.lastSeq || 0; opSeq = j.opSeq || 0;
        if (j.pending.length) pendingBatches = [{ batchId: 'legacy-' + clientId + '-' + Date.now(), ops: j.pending }];
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
      ws.send(JSON.stringify({ t: 'hello', clientId, name: myName, doc: docName, lastSeq }));
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

  function upsertRev(rev) {
    if (!rev) return;
    const i = revs.findIndex(r => r.n === rev.n);
    if (i >= 0) revs[i] = rev; else revs.push(rev);
  }
  function upsertLedgerEntry(e) {
    if (!e || ledger.some(x => x.seq === e.seq && x.act === e.act && x.target === e.target)) return;
    ledger.push(e);
    ledger.sort((a, b) => a.seq - b.seq);
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

  function handle(msg) {
    if (msg.t === 'welcome') {
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
      // 已确认的待发批次：按 opId 剔除；剩下的按同一 batchId 幂等补发
      pendingBatches = pendingBatches.filter(b => {
        b.ops = b.ops.filter(op => !seen.has(op.opId));
        return b.ops.length > 0;
      });
      const role = msg.role || 'viewer';
      applyMyState(role, !!msg.member, msg.epoch || 0, msg.members || []);
      initialized = !!msg.initialized;
      for (const b of pendingBatches) send({ t: 'ops', batchId: b.batchId, ops: b.ops });
      if (msg.initEntry && msg.initEntry.target === clientId) {
        setHint('你是这个空间的所有者，可以邀请协作者并分配角色。');
      } else if (!msg.member) {
        setHint('你尚未被邀请加入此空间，当前为只读。把你的用户 ID 发给所有者即可受邀。');
      }
      renderAll(); saveLocalSoon();
    } else if (msg.t === 'ops') {
      for (const { seq, op } of msg.applied) {
        doc.apply(op); allOps.push(op);
        lastSeq = Math.max(lastSeq, seq);
      }
      if (msg.batchId) dropPending(msg.batchId, msg.applied);
      else dropPendingOps(msg.applied);
      upsertRev(msg.rev);
      if (msg.rev) lastSeq = Math.max(lastSeq, msg.rev.seq);
      renderAll(); saveLocalSoon();
    } else if (msg.t === 'batchAck') {
      if (msg.status === 'rejected') {
        lastSeq = Math.max(lastSeq, msg.atSeq || 0);
        quarantineBatch(msg.batchId, msg);
      } else {
        // applied / empty（含重复投递）：按批 id 与 opId 完成确认
        for (const { seq, op } of msg.applied || []) {
          doc.apply(op); allOps.push(op);
          lastSeq = Math.max(lastSeq, seq);
        }
        dropPending(msg.batchId, msg.applied || []);
        upsertRev(msg.rev);
        if (msg.rev) lastSeq = Math.max(lastSeq, msg.rev.seq);
      }
      renderAll(); saveLocalSoon();
    } else if (msg.t === 'members') {
      upsertLedgerEntry(msg.entry);
      if (msg.entry) lastSeq = Math.max(lastSeq, msg.entry.seq);
      const newMembers = msg.members || members;
      const me = newMembers.find(m => m.id === clientId);
      const newRole = me ? me.role : 'viewer';
      applyMyState(newRole, !!me, msg.epoch, newMembers);
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
    } else if (msg.t === 'presence') {
      peers = msg.peers || [];
      $('#presence').textContent = msg.count + ' 人在线';
      renderPeers();
    } else if (msg.t === 'error') {
      const loud = msg.code === 'forbidden-rollback' || msg.code === 'forbidden-membership';
      setHint(msg.message || '操作被拒绝', loud);
    }
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
    dropPendingOps(applied); // 重复重提（新 batchId）时按 opId 确认
  }

  // 整批被服务端拒绝：移出待发、从已确认操作重建本地文档、整批进入隔离草稿
  function quarantineBatch(batchId, info) {
    const i = pendingBatches.findIndex(b => b.batchId === batchId);
    let ops = null;
    if (i >= 0) { ops = pendingBatches[i].ops; pendingBatches.splice(i, 1); }
    if (quarantine.some(q => q.batchId === batchId)) return; // 重复拒绝不重复入账
    if (!ops) {
      // 极端情况：页面刚加载就收到拒绝（服务端保留了隔离引用），用空壳保留事实
      ops = info.kinds ? new Array((info.kinds.prose || 0) + (info.kinds.annotate || 0)).fill(null) : [];
    }
    // 解释相关的角色变更：取 atSeq 之前最后一条针对自己的成员记录
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

  // 从「服务端已确认操作 + 仍待确认批次」重建本地 CRDT（剔除被隔离的乐观操作）
  function rebuildLocal() {
    doc.clear();
    for (const op of allOps) doc.apply(op);
    for (const b of pendingBatches) for (const op of b.ops) doc.apply(op);
  }

  function newBatchId() { return clientId + '#' + (++opSeq) + '#b' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6); }

  // 本地产生操作：立即应用、组成一个批次入队、尝试发送
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
    while (s < ot.length - p && s < nt.length - p && s < nt.length - p && ot[ot.length - 1 - s] === nt[nt.length - 1 - s]) s++;
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
    localEdit(ed.textContent);
    render();
  });
  ed.addEventListener('paste', (e) => {
    if (!AUTHZ.can(myRole, 'prose')) { e.preventDefault(); setHint('只读/评论者不能修改正文。', true); return; }
    e.preventDefault();
    const text = (e.clipboardData || window.clipboardData).getData('text/plain');
    document.execCommand('insertText', false, text);
  });
  ed.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
      e.preventDefault();
      if (AUTHZ.can(myRole, 'prose')) document.execCommand('insertText', false, '\n');
      else setHint('只读/评论者不能修改正文。', true);
      return;
    }
    // 只读角色拦截可打印字符与删除（contenteditable=false 之外的双保险）
    if (!AUTHZ.can(myRole, 'prose') && ed.isContentEditable &&
        (e.key.length === 1 || ['Backspace', 'Delete', 'Cut'].includes(e.key))) {
      e.preventDefault();
      setHint('只读/评论者不能修改正文。', true);
    }
  });

  // ---------- 选区 <-> 偏移 ----------
  function offsetOf(node, off) {
    if (node === ed) {
      let acc = 0;
      for (let i = 0; i < off && i < ed.childNodes.length; i++) acc += ed.childNodes[i].textContent.length;
      return acc;
    }
    const w = document.createTreeWalker(ed, NodeFilter.SHOW_TEXT);
    let n, acc = 0;
    while ((n = w.nextNode())) {
      if (n === node) return acc + off;
      acc += n.textContent.length;
    }
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
    if (ed.innerHTML !== html) {
      const caret = getCaret();
      ed.innerHTML = html;
      setCaret(caret);
    }
    curText = text;
    applyGating();
  }

  const STATUS_INFO = {
    'anchored': ['已锚定', 'ok'],
    'split-insert': ['已拆分 · 锚定文字中插入了新内容', 'warn'],
    'split-delete': ['部分悬空 · 部分锚定文字被删除', 'warn'],
    'orphan-deleted': ['悬空 · 锚定文字已被删除', 'bad'],
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
      if (r.status !== 'anchored' && r.status !== 'resolved') {
        inner += '<div class="cur"><span class="lbl">当前覆盖文字</span>' + (r.cur ? esc(r.cur) : '（已被删除）') + '</div>';
      }
      inner += '<div class="ctext">' + esc(c.text) + '</div>';
      inner += '<div class="ops"></div>';
      card.innerHTML = inner;
      const ops = card.querySelector('.ops');
      if (!c.resolved) {
        if (canNote) {
          const re = document.createElement('button');
          re.textContent = '重新挂接';
          re.title = '选择新的文字范围来锚定这条评论';
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
    const list = [...revs].sort((a, b) => b.n - a.n);
    for (const r of list) {
      const div = document.createElement('div');
      div.className = 'rev';
      const kind = r.kind === 'restore'
        ? '<span class="kind-restore">恢复</span> 至 #' + r.target
        : '编辑';
      div.innerHTML = '<span class="n">#' + r.n + '</span><div class="body">' +
        '<div class="sum">' + esc(r.summary) + '</div>' +
        '<div class="sub">' + kind + ' · seq ' + r.seq + ' · ' + esc(r.by) + ' · ' + new Date(r.ts).toLocaleString() + '</div></div>';
      if (isOwner) {
        const btn = document.createElement('button');
        btn.textContent = '恢复此版本';
        btn.onclick = () => {
          if (!online) { setHint('离线状态下无法恢复版本'); return; }
          if (confirm('确定要恢复到修订 #' + r.n + ' 吗？\n恢复会作为新修订与他人修改合并，不会丢失他人内容。')) {
            send({ t: 'restore', rev: r.n });
          }
        };
        div.appendChild(btn);
      }
      box.appendChild(div);
    }
  }

  // 成员变更审计与内容修订按共享 seq 合并 => 相对顺序一目了然
  function renderLedger() {
    const box = $('#ledger');
    const revBySeq = new Map();
    for (const r of revs) revBySeq.set(r.seq, r);
    const rows = [];
    for (const e of ledger) rows.push({ seq: e.seq, kind: 'entry', e });
    for (const r of revs) {
      // 一个批次含多条 op，fromSeq 为批次首条 op 的 seq => 与成员审计按同一总序排序
      rows.push({ seq: r.fromSeq || r.seq, endSeq: r.seq, kind: 'rev', r });
    }
    rows.sort((a, b) => b.seq - a.seq);
    box.innerHTML = '';
    if (!rows.length) { box.innerHTML = '<div class="empty">暂无记录。</div>'; return; }
    for (const row of rows.slice(0, 400)) {
      const div = document.createElement('div');
      div.className = 'ledger ' + row.kind;
      if (row.kind === 'rev') {
        const r = row.r;
        div.innerHTML = '<span class="lseq">seq ' + r.seq + '</span><span class="ltag rev">修订 #' + r.n + (r.kind === 'restore' ? '（恢复→#' + r.target + '）' : '') + '</span>' +
          '<span class="lbody">' + esc(r.summary) + ' · ' + esc(r.by) + '</span>';
      } else {
        const e = row.e;
        const tag = e.kind === 'space'
          ? (e.act === 'upgrade' ? '空间升级' : '空间创建')
          : { invite: '邀请', role: '角色变更', remove: '移除' }[e.act] || '成员变更';
        const who = e.targetName || e.target;
        let detail;
        if (e.kind === 'space') detail = esc(who) + ' 成为所有者';
        else if (e.act === 'remove') detail = '移除 ' + esc(who) + '（原 ' + (AUTHZ.LABELS[e.from] || e.from) + '）';
        else detail = esc(who) + '：' + (AUTHZ.LABELS[e.from] || e.from || '—') + ' → ' + (AUTHZ.LABELS[e.to] || e.to);
        div.innerHTML = '<span class="lseq">seq ' + e.seq + '</span><span class="ltag ' + e.kind + '">' + tag +
          '</span><span class="lbody">' + detail + ' · by ' + esc(e.byName || e.by || '系统') + ' · epoch ' + e.epoch + '</span>';
        if (e.target === clientId) div.classList.add('me');
      }
      box.appendChild(div);
    }
  }

  // ---------- 成员面板 ----------
  function reqId() { return clientId + '#req#' + (crypto.randomUUID ? crypto.randomUUID() : Math.random().toString(36).slice(2)); }
  function sendMember(act, target, role, name) {
    send({ t: 'member', reqId: reqId(), act, target, role, name });
  }
  function renderMembers() {
    const box = $('#members');
    box.innerHTML = '';
    const isOwner = myRole === 'owner';
    for (const m of members) {
      const div = document.createElement('div');
      div.className = 'member' + (m.id === clientId ? ' me' : '');
      const roleSel = isOwner && !(m.role === 'owner' && m.id === clientId)
        ? '<select class="mrole" data-id="' + esc(m.id) + '">' +
          AUTHZ.ROLES.map(r => '<option value="' + r + '"' + (r === m.role ? ' selected' : '') + '>' + AUTHZ.LABELS[r] + '</option>').join('') +
          '</select>'
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
    box.querySelectorAll('select.mrole').forEach(sel => {
      sel.addEventListener('change', () => {
        sendMember('role', sel.dataset.id, sel.value);
      });
    });
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
      if (isOwner) {
        for (const role of ['editor', 'commenter', 'viewer']) {
          const b = document.createElement('button');
          b.className = 'qinvite';
          b.textContent = '邀为' + AUTHZ.LABELS[role];
          b.onclick = () => sendMember('invite', p.id, role, p.name);
          div.appendChild(b);
        }
      }
      box.appendChild(div);
    }
  }

  // ---------- 隔离草稿 ----------
  function describeOps(ops) {
    const n = { ins: 0, del: 0, mark: 0, com: 0 };
    const parts = [];
    for (const op of ops) {
      if (!op) continue;
      if (op.t === 'ins') { n.ins++; parts.push('插入「' + esc(op.ch) + '」'); }
      else if (op.t === 'del') { n.del++; parts.push('删除字符 ' + esc(op.id.slice(-12))); }
      else if (op.t === 'mark') { n.mark++; parts.push('样式变更 ' + esc(JSON.stringify(op.attrs))); }
      else if (op.t === 'com') {
        n.com++;
        parts.push((op.resolved ? '批注解决/重挂' : '批注') + '：「' + esc((op.quote || '').slice(0, 24)) + '」→ ' + esc((op.text || '').slice(0, 24)));
      }
    }
    return { counts: n, parts };
  }
  function canResubmit(q) {
    const need = q.kinds && q.kinds.prose ? 'prose' : 'annotate';
    return AUTHZ.can(myRole, need);
  }
  function renderQuarantine() {
    const sec = $('#quarantineSection');
    sec.classList.toggle('hidden', !quarantine.length);
    $('#qCount').textContent = quarantine.length ? quarantine.length : '';
    const box = $('#quarantine');
    box.innerHTML = '';
    for (const q of quarantine) {
      const { parts } = describeOps(q.ops);
      const card = document.createElement('div');
      card.className = 'qcard';
      let html = '<div class="qhead"><span class="qrole">' + esc(AUTHZ.LABELS[q.role] || q.role) + ' 提交被拒</span>' +
        '<span class="qtime">' + new Date(q.rejectedTs).toLocaleString() + '</span></div>';
      html += '<div class="qreason">⛔ ' + esc(q.reason) + '</div>';
      if (q.transition) {
        const tr = q.transition;
        const txt = AUTHZ.transitionText(tr) || '你的角色在这批操作提交前发生了变化';
        html += '<div class="qtr">角色变化（seq ' + (tr.seq != null ? tr.seq : '?') + '）：' + esc(txt) + '；拒绝时授权纪元 epoch ' + q.epoch + '</div>';
      }
      html += '<div class="qops"><div class="qlbl">被保留的操作（共 ' + q.ops.length + ' 条，未进入共享文档）：</div><ul>' +
        parts.map(p => '<li>' + p + '</li>').join('') + '</ul></div>';
      card.innerHTML = html;
      const opsRow = document.createElement('div');
      opsRow.className = 'qopsrow';
      const copy = document.createElement('button');
      copy.textContent = '复制操作 JSON';
      copy.onclick = async () => {
        const text = JSON.stringify(q.ops, null, 2);
        try { await navigator.clipboard.writeText(text); setHint('已复制 ' + q.ops.length + ' 条操作的 JSON'); }
        catch (e) {
          const ta = document.createElement('textarea'); ta.value = text; document.body.appendChild(ta);
          ta.select(); document.execCommand('copy'); ta.remove();
          setHint('已复制 ' + q.ops.length + ' 条操作的 JSON');
        }
      };
      opsRow.appendChild(copy);
      const view = document.createElement('button');
      view.textContent = '展开原文';
      view.onclick = () => {
        let pre = card.querySelector('pre.qjson');
        if (pre) { pre.remove(); return; }
        pre = document.createElement('pre');
        pre.className = 'qjson';
        pre.textContent = JSON.stringify(q.ops, null, 2);
        card.appendChild(pre);
      };
      opsRow.appendChild(view);
      const resub = document.createElement('button');
      const allowed = canResubmit(q);
      resub.className = 'qresub';
      resub.textContent = allowed ? '显式重新提交整批' : '权限不足，无法重提（需' + (q.kinds.prose ? '编辑' : '评论者') + '）';
      resub.disabled = !allowed;
      resub.onclick = () => {
        if (!online) { setHint('离线状态下不能重新提交，请先恢复连接。'); return; }
        if (!canResubmit(q)) { setHint('当前角色仍不足以提交这批操作。'); return; }
        // 显式重提：保留原 opId（服务端按 opId 幂等），换新 batchId（作为一次新的授权尝试）
        quarantine = quarantine.filter(x => x.draftId !== q.draftId);
        const b = { batchId: newBatchId(), ops: q.ops };
        pendingBatches.push(b);
        send({ t: 'ops', batchId: b.batchId, ops: b.ops });
        resub.disabled = true;
        setHint('隔离批次已重新提交，等待服务端确认…');
        saveLocalSoon(); renderAll();
      };
      opsRow.appendChild(resub);
      card.appendChild(opsRow);
      box.appendChild(card);
    }
  }

  // ---------- 角色门禁 ----------
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
      ? '已连接' + (nP ? ' · 同步中(' + nP + ')' : '')
      : '离线 · 编辑已保存在本地' + (nP ? '（待同步 ' + nP + ' 条）' : '');
  }
  let hintTimer = null;
  function setHint(t, loud) {
    const el = $('#hint');
    el.textContent = t || '';
    el.classList.toggle('loud', !!loud);
    clearTimeout(hintTimer);
    if (t) hintTimer = setTimeout(() => { el.textContent = ''; el.classList.remove('loud'); }, 8000);
  }
  function renderAll() {
    render(); renderComments(); renderRevs(); renderLedger();
    renderMembers(); renderPeers(); renderQuarantine();
    applyGating(); setStatus();
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
  document.querySelectorAll('#toolbar [data-fmt]').forEach(btn => {
    btn.addEventListener('click', () => {
      if (!AUTHZ.can(myRole, 'prose')) { setHint('只有编辑或所有者可以修改样式。', true); return; }
      const range = getSelRange();
      if (!range) { setHint('请先选中一段文字'); return; }
      const key = btn.dataset.fmt;
      const cur = selAttrs(range[0], range[1]);
      const [st, en] = anchorsFor(range[0], range[1]);
      const attrs = {}; attrs[key] = !cur[key];
      pushOps([doc.mark(st, en, attrs)]);
      renderAll();
    });
  });

  $('#commentBtn').addEventListener('click', () => {
    if (!AUTHZ.can(myRole, 'annotate')) { setHint('评论者或更高角色才能创建批注。', true); return; }
    const range = getSelRange();
    if (!range) { setHint('请先选中要评论的文字'); return; }
    pendingCommentRange = range;
    $('#ncQuote').textContent = doc.text().slice(range[0], range[1]);
    $('#newComment').classList.remove('hidden');
    $('#ncText').value = '';
    $('#ncText').focus();
  });
  $('#ncCancel').addEventListener('click', () => {
    pendingCommentRange = null;
    $('#newComment').classList.add('hidden');
  });
  $('#ncSubmit').addEventListener('click', () => {
    const text = $('#ncText').value.trim();
    if (!text || !pendingCommentRange) return;
    const [s, e] = pendingCommentRange;
    const [st, en] = anchorsFor(s, e);
    const quote = doc.text().slice(s, e);
    pushOps([doc.comment(st, en, text, quote)]);
    pendingCommentRange = null;
    $('#newComment').classList.add('hidden');
    renderAll();
  });

  ed.addEventListener('mouseup', () => {
    if (!reattachFor) return;
    if (!AUTHZ.can(myRole, 'annotate')) { reattachFor = null; setHint('评论者或更高角色才能重新挂接批注。', true); return; }
    const range = getSelRange();
    if (!range) return;
    const [s, e] = range;
    const [st, en] = anchorsFor(s, e);
    const quote = doc.text().slice(s, e);
    pushOps([doc.updateComment(reattachFor, { start: st, end: en, quote })]);
    setHint('批注已重新挂接到：「' + (quote.length > 20 ? quote.slice(0, 20) + '…' : quote) + '」');
    reattachFor = null;
    renderAll();
  });

  ed.addEventListener('click', (e) => {
    const span = e.target.closest && e.target.closest('.chl');
    if (!span) return;
    const cid = (span.dataset.cids || '').split(',')[0];
    const card = document.querySelector('.card[data-cid="' + cid + '"]');
    if (card) {
      card.scrollIntoView({ block: 'nearest', behavior: 'smooth' });
      card.classList.add('flash');
      setTimeout(() => card.classList.remove('flash'), 1200);
    }
  });

  // ---------- 身份与所有者操作 ----------
  const nameInput = $('#myName');
  nameInput.value = myName;
  $('#myId').textContent = 'ID: ' + clientId;
  nameInput.addEventListener('change', () => {
    myName = nameInput.value.trim().slice(0, 80) || clientId;
    nameInput.value = myName;
    localStorage.setItem('cname', myName);
    if (online) send({ t: 'hello', clientId, name: myName, doc: docName, lastSeq });
  });
  $('#inviteBtn').addEventListener('click', () => {
    if (myRole !== 'owner') { setHint('只有所有者可以邀请成员。', true); return; }
    const id = $('#inviteId').value.trim();
    const role = $('#inviteRole').value;
    if (!id) { setHint('请填写要邀请的用户 ID'); return; }
    sendMember('invite', id, role);
    $('#inviteId').value = '';
    setHint('已发送邀请请求（重复提交会自动幂等）');
  });

  window.addEventListener('beforeunload', saveLocal);
  setInterval(saveLocal, 5000);

  renderAll();
  connect();
})();
