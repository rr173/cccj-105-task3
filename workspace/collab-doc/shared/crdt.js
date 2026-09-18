'use strict';
/*
 * 共享 CRDT 核心（浏览器与 Node 通用，零依赖）。
 *
 * 文本：RGA（Replicated Growable Array）
 *   - 每个字符有全局唯一 id "actor:counter"，记录插入位置（after = 左邻字符 id）。
 *   - 同一位置并发插入按 id 降序排列（先比较 counter，再比较 actor），结果与到达顺序无关。
 *   - 删除 = 打墓碑标记。因此任何操作都是可交换、可重放的：
 *     较晚同步的客户端永远不会覆盖别人已确认的内容，只会合并进来。
 *
 * 锚点：{ id: 字符id|null, edge: 's'|'e' }
 *   - null + 's' = 文档开头；null + 'e' = 文档末尾。
 *   - 锚点指向字符而非偏移量，因此并发编辑后评论/格式仍能落到正确的文字上；
 *     字符被删除后锚点"粘"在其墓碑位置，可解释地进入悬空状态。
 *
 * 格式：mark = { id, start, end, attrs, ts, by, deleted }，按 id 做 LWW 合并；
 *   渲染时对每个属性键在覆盖该段的 marks 中取 (ts, by) 最大者，支持"加粗再取消"。
 *
 * 评论：comment = { id, start, end, text, quote, ts, by, resolved }，按 id 做 LWW 合并。
 *   quote 记录创建时锚定的原文，用于解释悬空原因。
 */
(function (root, factory) {
  const mod = factory();
  if (typeof module !== 'undefined' && module.exports) module.exports = mod;
  else root.CRDT = mod;
})(typeof self !== 'undefined' ? self : this, function () {

  const ROOT = ''; // 文档头部的虚拟父节点 id

  function splitId(id) {
    const i = id.lastIndexOf(':');
    return [id.slice(0, i), Number(id.slice(i + 1))];
  }
  function cmpId(a, b) {
    const A = splitId(a), B = splitId(b);
    return (A[1] - B[1]) || (A[0] < B[0] ? -1 : A[0] > B[0] ? 1 : 0);
  }
  function cmpLww(tsA, byA, tsB, byB) {
    return (tsA - tsB) || (byA < byB ? -1 : byA > byB ? 1 : 0);
  }
  // sub 是否为 str 的子序列（用于判断"被插入拆分"还是"被部分删除"）
  function isSubseq(sub, str) {
    if (!sub) return true;
    let i = 0;
    for (const ch of str) {
      if (ch === sub[i]) i++;
      if (i === sub.length) return true;
    }
    return false;
  }

  class Doc {
    constructor(actor) {
      this.actor = actor || 'anon';
      this.counter = 0;
      this.chars = new Map();    // id -> { id, after, ch, tomb, by }
      this.kids = new Map();     // parentId -> [childId, ...]（按 id 降序）
      this.marks = new Map();    // markId -> mark
      this.comments = new Map(); // commentId -> comment
      this.waiting = [];         // 因果依赖未满足的暂存操作
    }

    _nextId() { return this.actor + ':' + (++this.counter); }
    _kidsOf(p) { let k = this.kids.get(p); if (!k) { k = []; this.kids.set(p, k); } return k; }

    // 清空本地状态（本地乐观操作被服务端隔离后，需从已确认操作重建文档）
    clear() {
      this.chars.clear(); this.kids.clear();
      this.marks.clear(); this.comments.clear();
      this.waiting.length = 0;
      return this;
    }

    // ---------- 本地操作：应用到本地并返回可广播的 op ----------
    insert(afterId, ch) {
      const op = { t: 'ins', id: this._nextId(), after: afterId || ROOT, ch, by: this.actor };
      this.apply(op);
      return op;
    }
    remove(id) {
      const op = { t: 'del', id, by: this.actor };
      this.apply(op);
      return op;
    }
    mark(start, end, attrs) {
      const op = { t: 'mark', id: this._nextId(), start, end, attrs, ts: Date.now(), by: this.actor, deleted: false };
      this.apply(op);
      return op;
    }
    comment(start, end, text, quote) {
      const op = { t: 'com', id: this._nextId(), start, end, text, quote, ts: Date.now(), by: this.actor, resolved: false };
      this.apply(op);
      return op;
    }
    // 评论的后续修改（重新挂接 / 解决 / 编辑内容）整体走 LWW
    updateComment(id, patch) {
      const c = this.comments.get(id);
      if (!c) return null;
      const op = Object.assign({}, c, patch, { t: 'com', id, ts: Date.now(), by: this.actor });
      this.apply(op);
      return op;
    }

    // ---------- 操作应用（幂等、可交换） ----------
    apply(op) {
      switch (op.t) {
        case 'ins': return this._applyIns(op);
        case 'del': return this._applyDel(op);
        case 'mark': return this._applyMark(op);
        case 'com': return this._applyCom(op);
      }
      return false;
    }
    _applyIns(op) {
      if (this.chars.has(op.id)) return true; // 幂等
      if (op.after !== ROOT && !this.chars.has(op.after)) { this.waiting.push(op); return false; }
      this.chars.set(op.id, { id: op.id, after: op.after, ch: op.ch, tomb: false, by: op.by });
      const sibs = this._kidsOf(op.after);
      let i = 0;
      while (i < sibs.length && cmpId(sibs[i], op.id) > 0) i++;
      sibs.splice(i, 0, op.id);
      this._drain();
      return true;
    }
    _applyDel(op) {
      const c = this.chars.get(op.id);
      if (!c) { this.waiting.push(op); return false; }
      c.tomb = true;
      return true;
    }
    _applyMark(op) {
      const m = this.marks.get(op.id);
      if (!m || cmpLww(op.ts, op.by, m.ts, m.by) > 0) {
        this.marks.set(op.id, { id: op.id, start: op.start, end: op.end, attrs: op.attrs || {}, ts: op.ts, by: op.by, deleted: !!op.deleted });
      }
      return true;
    }
    _applyCom(op) {
      const c = this.comments.get(op.id);
      if (!c || cmpLww(op.ts, op.by, c.ts, c.by) > 0) {
        this.comments.set(op.id, {
          id: op.id, start: op.start, end: op.end,
          text: String(op.text || ''), quote: String(op.quote || ''),
          ts: op.ts, by: op.by, resolved: !!op.resolved,
          detached: !!op.detached, detachReason: op.detachReason || null,
        });
      }
      return true;
    }
    _drain() {
      let moved = true;
      while (moved) {
        moved = false;
        for (let i = 0; i < this.waiting.length; i++) {
          const op = this.waiting[i];
          const ready = op.t === 'ins'
            ? (this.chars.has(op.id) || op.after === ROOT || this.chars.has(op.after))
            : this.chars.has(op.id);
          if (ready) { this.waiting.splice(i, 1); this.apply(op); moved = true; break; }
        }
      }
    }

    // ---------- 序列与位置 ----------
    // 含墓碑的全序列（RGA 顺序：父节点的孩子紧跟在父节点之后）
    seq() {
      const out = [];
      const walk = (p) => {
        const k = this.kids.get(p);
        if (!k) return;
        for (const id of k) { out.push(this.chars.get(id)); walk(id); }
      };
      walk(ROOT);
      return out;
    }
    text() { return this.seq().filter(c => !c.tomb).map(c => c.ch).join(''); }
    visibleIds() { return this.seq().filter(c => !c.tomb).map(c => c.id); }

    // 锚点 -> 可见文本偏移。被删除的锚点字符"粘"在其墓碑位置。
    posOf(anchor) {
      if (!anchor || anchor.id == null) return anchor && anchor.edge === 'e' ? this.text().length : 0;
      const s = this.seq();
      let vis = 0;
      for (const c of s) {
        if (c.id === anchor.id) return c.tomb ? vis : (anchor.edge === 'e' ? vis + 1 : vis);
        if (!c.tomb) vis++;
      }
      return vis; // 锚点字符尚未到达：暂时放到末尾，等操作补齐后自然修正
    }
    range(a, b) {
      let s = this.posOf(a), e = this.posOf(b);
      if (s > e) { const t = s; s = e; e = t; }
      return [s, e];
    }

    // ---------- 评论状态解析（可解释的悬空） ----------
    resolveComment(c) {
      // 压缩迁移后锚点被显式判定死亡：保持 detached，不悄悄重算到其他字句
      if (c.detached) return { status: 'detached-compacted', cur: '', s: 0, e: 0, reason: c.detachReason };
      const [s, e] = this.range(c.start, c.end);
      const cur = this.text().slice(s, e);
      const quote = c.quote || '';
      let status;
      if (c.resolved) status = 'resolved';
      else if (cur === quote) status = 'anchored';          // 锚定文字完好
      else if (cur.length === 0) status = 'orphan-deleted'; // 悬空：锚定文字已被删除
      else if (isSubseq(quote, cur)) status = 'split-insert'; // 被拆分：中间插入了新内容
      else if (isSubseq(cur, quote)) status = 'split-delete'; // 部分悬空：部分锚定文字被删除
      else status = 'changed';                              // 锚定文字被修改
      return { status, cur, s, e };
    }

    // ---------- 格式 ----------
    activeMarks() {
      const out = [];
      for (const m of this.marks.values()) {
        if (m.deleted) continue;
        const [s, e] = this.range(m.start, m.end);
        if (e > s) out.push({ id: m.id, s, e, attrs: m.attrs, ts: m.ts, by: m.by });
      }
      return out;
    }
    commentList() { return [...this.comments.values()]; }
  }

  return { Doc, ROOT, cmpId, isSubseq };
});
