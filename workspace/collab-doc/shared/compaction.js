'use strict';
/*
 * 共享的「有界流水压缩 / 基线代次 / 快照迁移换算」核心（浏览器与 Node 通用，零依赖）。
 *
 * 代次（generation）
 *   - 每次压缩产生一个新基线代次 g（从 1 起单调递增），基线只可通过原子切换成为权威态。
 *   - 基线内容：cutoff seq、存活字符（线性重排为单链）、样式标记（按偏移换算后重建）、
 *     批注（逐锚点换算，无法换算的锚点进入显式 detached，绝不悄悄重挂）、
 *     成员表 / epoch / 账本（治理视图在压缩前后逐项相等）。
 *
 * id 换算
 *   - 压缩把存活字符重新编号为规范 id（"g<n>#<i>"），产出 forwardMap: oldId -> newId。
 *   - 已回收墓碑没有 forward 映射；按 RGA 全序给出「后继映射」fallback（successorOf）：
 *     · ins 的 after 是「插入位置」，后继映射保留插入意图（仍落在删除点之后/附近）；
 *     · del / mark / com 指向的是「具体字符」，墓碑被回收即锚点死亡，必须产出冲突草稿，
 *       绝不允许挂到另一段字句上。
 *   - 跨代次换算 composeMaps 逐代穿链；任一代断链即返回 null（显式冲突）。
 *
 * 迁移批次（落后镜像端重连）
 *   - translateBatch 把积压批次确定性地投射到新基线：可换算的操作保留意图（只换引用），
 *     不可换算的操作整条进入 conflicts[]，冲突说明包含 op、原因、被回收锚点。
 *   - 批次内自己新生成的 id 用 localMap 解析（同一批次里「插入后引用」不产生假冲突）。
 */
(function (root, factory) {
  const mod = factory();
  if (typeof module !== 'undefined' && module.exports) module.exports = mod;
  else root.COMPACT = mod;
})(typeof self !== 'undefined' ? self : this, function () {

  const ROOT = '';

  // ---------- id 工具 ----------
  function splitId(id) {
    const i = String(id).lastIndexOf(':');
    if (i < 0) return ['', 0];
    return [String(id).slice(0, i), Number(String(id).slice(i + 1))];
  }
  // 与 RGA 一致的 id 比较（counter 优先，再比 actor）
  function cmpId(a, b) {
    const A = splitId(a), B = splitId(b);
    return (A[1] - B[1]) || (A[0] < B[0] ? -1 : A[0] > B[0] ? 1 : 0);
  }

  // ---------- 基线构建 ----------
  // 输入 cutoff 时刻的 CRDT Doc；输出可独立重建投影的基线。
  //   chars: [{id,ch,by}]  仅存活字符，按可见顺序线性排列（基线单链）
  //   marks: 存活样式标记，锚点换算为偏移区间（投影等价），重建时挂到新字符
  //   comments: 批注（含已解决），锚点 id 经 forward 换算；死掉的锚点置 null 并记 detached
  //   forward: oldId -> newId（仅存活字符）
  //   succ:    oldId -> 后继存活 newId（墓碑/被回收字符的插入位置 fallback）
  function buildBaseline(doc, gen, cutoffSeq, opts) {
    opts = opts || {};
    // 规范 id 用零起始计数器：g1:0 是 ROOT 的唯一（最小）孩子，之后的开始插入
    // counter≥1 必然排在它之前，线性单链不破坏 RGA 的「在文档开头插入」语义。
    const prefix = 'g' + gen + ':';
    const all = doc.seq();                 // 含墓碑的 RGA 全序
    const live = all.filter(c => !c.tomb);
    const chars = [];
    const oldIndex = new Map();           // oldId -> 在 all 中的位置
    for (let i = 0; i < all.length; i++) oldIndex.set(all[i].id, i);
    live.forEach((c, i) => {
      const nid = prefix + i;
      // oldId 直接存在基线字符上：前向换算「旧 id -> 该字符」无需额外映射表（不产生隐藏副本）
      chars.push({ id: nid, o: c.id, ch: c.ch, by: c.by });
    });

    // succ 只记录「被回收墓碑」的后继存活字符；活字符的前向映射由基线本身给出。
    // 这是迁移「仍存在后继映射的字符引用」所必需且唯一的额外信息，体积随墓碑数而非活文档增长。
    const succ = new Map();
    for (let i = 0; i < all.length; i++) {
      if (!all[i].tomb) continue; // 活字符不需要 succ
      let hit = null;
      for (let j = i + 1; j < all.length; j++) {
        if (!all[j].tomb) { hit = all[j].id; break; }
      }
      const tombId = all[i].id;
      // 存「墓碑旧 id -> 后继存活字符的旧 id」；换算时先解析旧 id 再走前向
      succ.set(tombId, hit); // 可能为 null（无后继 => 文档末尾语义）
    }
    // 由基线本身派生的前向映射（不单独持久化，避免与基线重复的隐藏副本）
    const forward = new Map();
    for (const c of chars) forward.set(c.o, c.id);

    // 锚点 -> 存活 newId（要求指向具体存活字符；null 锚点保留）
    const anchorTo = (anchor) => {
      if (!anchor || anchor.id == null) return { anchor: { id: null, edge: anchor ? anchor.edge : 's' } };
      if (forward.has(anchor.id)) return { anchor: { id: forward.get(anchor.id), edge: anchor.edge } };
      return { dead: true }; // 指向已回收墓碑 => 具体锚点死亡
    };

    // ---- 样式标记：投影必须不变。存活（渲染非空）的标记用偏移区间重挂 ----
    const marks = [];
    for (const m of doc.marks.values()) {
      if (m.deleted) continue;
      // 复刻 doc.range / posOf 的可见投影
      const posOfAnchor = (a) => {
        if (!a || a.id == null) return a && a.edge === 'e' ? live.length : 0;
        const idx = oldIndex.get(a.id);
        if (idx == null) return null;
        let vis = 0;
        for (let k = 0; k < idx; k++) if (!all[k].tomb) vis++;
        if (all[idx].tomb) return vis;
        return a.edge === 'e' ? vis + 1 : vis;
      };
      const s = posOfAnchor(m.start), e = posOfAnchor(m.end);
      if (s == null || e == null || e <= s) continue; // 锚点已被回收/退化空区间 => 无投影可保留，丢弃不影响视图
      marks.push({
        id: m.id, s, e, attrs: m.attrs || {}, ts: m.ts, by: m.by, deleted: false,
      });
    }

    // ---- 批注：逐锚点换算；具体锚点死亡 => 显式 detached（带原 quote），绝不重挂 ----
    const comments = [];
    for (const c of doc.comments.values()) {
      const a = anchorTo(c.start), b = anchorTo(c.end);
      const out = {
        id: c.id, text: c.text, quote: c.quote, ts: c.ts, by: c.by, resolved: !!c.resolved,
        start: null, end: null, detached: false,
      };
      if (!a.dead && !b.dead) { out.start = a.anchor; out.end = b.anchor; }
      else {
        out.detached = true;
        out.detachReason = '压缩回收了批注锚定的字符墓碑（基线代次 ' + gen + '，cutoff seq ' + cutoffSeq + '），批注不会被悄悄挂到其他字句；请显式重新挂接。';
      }
      comments.push(out);
    }

    return {
      gen, cutoffSeq,
      prefix,
      chars,
      marks,
      comments,
      forward,
      succ, // 仅墓碑 oldId -> 后继存活字符 oldId（可为 null）
    };
  }

  // 跨代次 forward 链穿链：id 在 fromGen 命名空间 => 目标代次 id；断链返回 null。
  // 前向穿链：id 在 fromGen 命名空间 => toGen 命名空间 id；任一代断链返回 null。
  // mapsByGen[g] 是 g-1 -> g 的映射（仅活字符，由基线 chars[].o 派生）。
  function composeMaps(id, fromGen, toGen, mapsByGen) {
    let cur = id, g = fromGen;
    while (g < toGen) {
      const m = mapsByGen[g + 1];
      if (!m || !m.has(cur)) return null;
      cur = m.get(cur);
      g++;
    }
    return cur;
  }
  // 插入位置穿链：活字符走前向；被回收墓碑则在「该代」用 succ 找到后继（旧 id），
  // 再从该后继继续穿链。这样保留「插在该位置之后」的意图，不影响其他字句。
  function composeAfter(id, fromGen, toGen, mapsByGen, succByGen) {
    if (id === ROOT) return ROOT;
    let cur = id, g = fromGen;
    while (g < toGen) {
      const m = mapsByGen[g + 1];
      if (m && m.has(cur)) { cur = m.get(cur); g++; continue; }
      const succ = succByGen[g + 1]; // 墓碑旧 id -> 后继活字符旧 id（null=无后继）
      if (succ && succ.has(cur)) {
        const nx = succ.get(cur);
        if (nx == null) return ROOT; // 无后继 => 文档开头锚点（之后顺序决定）
        cur = nx; g++;               // 落到后继活字符的新 id，继续穿后续代
        continue;
      }
      return null;
    }
    return cur;
  }

  // ---------- 迁移批次换算 ----------
  // ctx: {
  //   fromGen, toGen, mapsByGen, succByGen,
  //   liveIds: Set(newId) 目标代次存活字符,
  // }
  // 返回 { ops: 可投射操作（已换算）, conflicts: [{op, reason, anchor, kind}], obsolete: [op] }
  function translateBatch(rawOps, ctx) {
    const ops = [], conflicts = [], obsolete = [];
    const localMap = new Map(); // 本批次内自己新生成的 id（目标命名空间）

    const mapChar = (oldId) => {
      if (oldId === ROOT) return ROOT;
      if (localMap.has(oldId)) return localMap.get(oldId);
      return composeMaps(oldId, ctx.fromGen, ctx.toGen, ctx.mapsByGen);
    };
    const mapAfter = (oldId) => {
      if (oldId === ROOT) return ROOT;
      if (localMap.has(oldId)) return localMap.get(oldId);
      return composeAfter(oldId, ctx.fromGen, ctx.toGen, ctx.mapsByGen, ctx.succByGen);
    };
    const mapAnchor = (a) => {
      if (!a || a.id == null) return { anchor: { id: null, edge: a ? a.edge : 's' } };
      const nid = mapChar(a.id);
      if (nid == null) return { dead: true, anchor: a };
      // 具体锚点必须仍指向「同一字符」：它在目标基线必须存在（含墓碑）。
      // liveIds 只含存活；墓碑目标在迁移时无法验证其语义 => 要求它存活，否则按锚点死亡处理。
      if (!ctx.liveIds.has(nid)) return { dead: true, anchor: a };
      return { anchor: { id: nid, edge: a.edge } };
    };
    const fail = (op, kind, reason, anchor) => conflicts.push({ op, kind, reason, anchor: anchor || null });

    for (const op of rawOps || []) {
      if (op.t === 'ins') {
        // 本地引用（引用本批次刚插入的字符）优先
        let after = op.after === ROOT ? ROOT : localMap.get(op.after);
        if (after === undefined) after = mapAfter(op.after);
        if (after === null) { fail(op, 'ins-after', '插入位置锚点所指字符的墓碑已被回收，且无后继可保留插入意图。', { id: op.after }); continue; }
        const nop = Object.assign({}, op, { after });
        // 本操作的新 id 在目标命名空间原样可用（actor:counter 与基线 g# 前缀不冲突）
        if (op.id) localMap.set(op.id, op.id);
        ops.push(nop);
      } else if (op.t === 'del') {
        if (localMap.has(op.id)) { obsolete.push(op); continue; } // 删除本批次刚插入的（基线无此字符）
        const nid = mapChar(op.id);
        if (nid == null) {
          fail(op, 'del-reclaimed', '要删除的字符已随早前删除被压缩回收（删除意图在新基线已成立）；该操作不会悄悄挂到其他字句，请确认后消解。', { id: op.id });
          continue;
        }
        if (!ctx.liveIds.has(nid)) {
          fail(op, 'del-reclaimed', '要删除的字符在新基线中已是墓碑；删除意图已满足，请确认后消解。', { id: op.id });
          continue;
        }
        ops.push(Object.assign({}, op, { id: nid }));
      } else if (op.t === 'mark') {
        const a = mapAnchor(op.start), b = mapAnchor(op.end);
        if (a.dead || b.dead) {
          fail(op, 'mark-anchor', '样式标记锚定的字符墓碑已被回收，无法在不改动样式边界的前提下迁移；请在新基线重新选择范围。', a.dead ? op.start : op.end);
          continue;
        }
        ops.push(Object.assign({}, op, { start: a.anchor, end: b.anchor }));
      } else if (op.t === 'com') {
        const a = mapAnchor(op.start), b = mapAnchor(op.end);
        if (a.dead || b.dead) {
          fail(op, 'com-anchor', '批注锚定的字符墓碑已被回收；批注不会被悄悄挂到其他字句，请在新基线显式重新挂接。', a.dead ? op.start : op.end);
          continue;
        }
        ops.push(Object.assign({}, op, { start: a.anchor, end: b.anchor }));
      } else {
        fail(op, 'unknown', '无法识别的操作类型。', null);
      }
    }
    return { ops, conflicts, obsolete };
  }

  // 把基线 chars 还原为可 apply 的操作序列（重建端用）。
  // 线性单链 => 依次 after=前一个 newId。
  function baselineToOps(b) {
    const out = [];
    let after = ROOT;
    for (const c of b.chars) {
      out.push({ t: 'ins', id: c.id, after, ch: c.ch, by: c.by, baseline: b.gen });
      after = c.id;
    }
    for (const m of b.marks) {
      const ids = b.chars.map(x => x.id);
      const anc = (pos, edge) => {
        if (!ids.length) return { id: null, edge };
        if (edge === 's') return pos <= 0 ? { id: null, edge: 's' } : { id: ids[Math.min(pos, ids.length) - 1], edge: 's' };
        return pos >= ids.length ? { id: null, edge: 'e' } : { id: ids[Math.max(pos - 1, 0)], edge: 'e' };
      };
      out.push({
        t: 'mark', id: m.id, start: anc(m.s, 's'), end: anc(m.e, 'e'),
        attrs: m.attrs, ts: m.ts, by: m.by, deleted: false, baseline: b.gen,
      });
    }
    for (const c of b.comments) {
      out.push({
        t: 'com', id: c.id,
        start: c.start || { id: null, edge: 's' }, end: c.end || { id: null, edge: 'e' },
        text: c.text, quote: c.quote, ts: c.ts, by: c.by, resolved: c.resolved,
        detached: !!c.detached, detachReason: c.detachReason || null, baseline: b.gen,
      });
    }
    return out;
  }

  // 基线分片（迁移分片）：chars 按块切，marks/comments/meta 放最后一片。
  // 每片带 { gen, shard, shards, ... }，重复/乱序投递可按 (gen,shard) 幂等拼装。
  function shardBaseline(b, shardSize) {
    shardSize = shardSize || 400;
    const charChunks = [];
    for (let i = 0; i < b.chars.length; i += shardSize) charChunks.push(b.chars.slice(i, i + shardSize));
    const total = charChunks.length + 1;
    const shards = charChunks.map((chunk, i) => ({
      gen: b.gen, shard: i, shards: total, kind: 'chars', chars: chunk,
    }));
    shards.push({
      gen: b.gen, shard: total - 1, shards: total, kind: 'tail',
      cutoffSeq: b.cutoffSeq, marks: b.marks, comments: b.comments,
    });
    return shards;
  }
  function assembleShards(received) {
    const byGen = new Map();
    for (const s of received) {
      let g = byGen.get(s.gen);
      if (!g) { g = { gen: s.gen, total: s.shards, pieces: new Map() }; byGen.set(s.gen, g); }
      g.pieces.set(s.shard, s); // 幂等：同片覆盖无副作用
    }
    const complete = [];
    for (const g of byGen.values()) {
      if (g.pieces.size < g.total) continue;
      const chars = [], tail = [];
      for (let i = 0; i < g.total; i++) {
        const p = g.pieces.get(i);
        if (!p) { chars.length = 0; break; }
        if (p.kind === 'chars') for (const c of p.chars) chars.push(c);
        else tail.push(p);
      }
      const t = tail[0];
      if (t) complete.push({ gen: g.gen, cutoffSeq: t.cutoffSeq, chars, marks: t.marks, comments: t.comments });
    }
    return complete; // 已完整的代次（通常 0 或 1 个）
  }

  return {
    ROOT, cmpId,
    buildBaseline, composeMaps, composeAfter,
    translateBatch, baselineToOps, shardBaseline, assembleShards,
  };
});
