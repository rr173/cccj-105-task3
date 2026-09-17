'use strict';
/*
 * 共享的空间成员治理规则（浏览器与 Node 通用，零依赖）。
 *
 * 四种角色（权限为包含关系，等级递减）：
 *   owner     所有者：邀请成员、变更角色、移除成员、回滚修订、编辑正文/样式、管理批注
 *   editor    编辑：  修改正文与样式（ins/del/mark）、管理批注
 *   commenter 评论者：创建 / 解决 / 重新挂接批注（com），不能改正文
 *   viewer    只读：  仅可阅读
 *
 * 未被邀请 / 已被移除的访客等效于只读 viewer（可以阅读，不能写入），
 * 但 members 表中没有其成员记录，所有者可在成员面板中邀请。
 *
 * 授权以「授权纪元 epoch」为版本：每次成员变更都会让 epoch 单调 +1。
 * 服务端对每个到达的操作批次按当前 epoch 原子授权——批次中任一操作越权，
 * 整批拒绝，绝不发布其中任何一部分。
 */
(function (root, factory) {
  const mod = factory();
  if (typeof module !== 'undefined' && module.exports) module.exports = mod;
  else root.AUTHZ = mod;
})(typeof self !== 'undefined' ? self : this, function () {

  const ROLES = ['owner', 'editor', 'commenter', 'viewer'];
  const RANK = { owner: 4, editor: 3, commenter: 2, viewer: 1, null: 0 };
  const LABELS = {
    owner: '所有者', editor: '编辑', commenter: '评论者', viewer: '只读访客',
    unknown: '未邀请访客',
  };

  function isValidRole(r) { return ROLES.indexOf(r) >= 0; }
  // 未登录/被移除者按只读处理
  function effectiveRole(role) { return isValidRole(role) ? role : 'viewer'; }
  function rank(role) { return RANK[effectiveRole(role)]; }

  // 细粒度动作
  function can(role, action) {
    const r = rank(role);
    switch (action) {
      case 'read': return true;
      case 'annotate': return r >= RANK.commenter;   // 批注：创建/解决/重新挂接
      case 'prose': return r >= RANK.editor;         // 正文与样式
      case 'invite': return role === 'owner';        // 邀请 / 改角色 / 移除
      case 'rollback': return role === 'owner';      // 仅所有者可回滚检查点
      default: return false;
    }
  }

  // op.t -> 所需动作。ins/del/mark 改正文样式；com 为批注。
  function opAction(op) {
    if (!op) return null;
    if (op.t === 'ins' || op.t === 'del' || op.t === 'mark') return 'prose';
    if (op.t === 'com') return 'annotate';
    return null;
  }
  function canOp(role, op) {
    const a = opAction(op);
    return a ? can(role, a) : false;
  }

  // 原子批次授权：只要批次中有一个操作越权，整批拒绝。
  // 返回 { ok, reason, need, role, kinds }。
  function authorizeBatch(role, ops) {
    const eff = effectiveRole(role);
    let prose = 0, annotate = 0, invalid = 0;
    for (const op of ops || []) {
      const a = opAction(op);
      if (a === 'prose') prose++;
      else if (a === 'annotate') annotate++;
      else invalid++;
    }
    const kinds = {};
    if (prose) kinds.prose = prose;
    if (annotate) kinds.annotate = annotate;
    if (invalid) kinds.invalid = invalid;
    if (prose && !can(eff, 'prose')) {
      return {
        ok: false, role: eff, need: 'editor', kinds,
        reason: proseKindReason(eff, annotate > 0),
      };
    }
    if (annotate && !can(eff, 'annotate')) {
      return {
        ok: false, role: eff, need: 'commenter', kinds,
        reason: '当前角色（' + LABELS[eff] + '）无权创建或修改批注，需要评论者或更高角色。',
      };
    }
    return { ok: true, role: eff, kinds };
  }
  function proseKindReason(role, alsoAnnotate) {
    if (role === 'commenter') {
      return '评论者只能管理批注，不能修改正文或样式' + (alsoAnnotate ? '。本批次同时包含正文操作与批注操作，整批拒绝' : '') + '。';
    }
    return '只读访客不能修改文档，需要编辑或更高角色。';
  }

  // 角色变化的人类可读说明（用于隔离区解释）
  function transitionText(tr) {
    if (!tr) return null;
    const parts = [];
    const act = tr.act;
    if (act === 'remove') parts.push('你已被 ' + tr.by + ' 移出该空间（' + LABELS[tr.from || 'editor'] + ' → 移除）');
    else if (act === 'role') parts.push('你的角色已被 ' + tr.by + ' 从「' + LABELS[tr.from] + '」变更为「' + LABELS[tr.to] + '」');
    else if (act === 'invite') parts.push('你被 ' + tr.by + ' 邀请为「' + LABELS[tr.to] + '」');
    else if (act === 'init' || act === 'upgrade' || act === 'create') parts.push('空间初始化，你是所有者');
    return parts.length ? parts[0] : null;
  }

  return {
    ROLES, RANK, LABELS,
    isValidRole, effectiveRole, rank, can, canOp, opAction,
    authorizeBatch, transitionText,
  };
});
