theory DG_LTR_Sound
  imports DG_Soundness "Voblint_CFG.LTR_Abstract"
begin

section \<open>Trace-native D/G collecting soundness\<close>

text \<open>
  The D/G post-solution endpoint is stated over the stack-faithful local-trace collector
  \<^const>\<open>ltr_collect\<close>.  Its entry, edge, and combine closure obligations feed
  \<open>ltr_collect_semantic_postfix\<close>; matched returns are supplied by \<^const>\<open>valid_ltr\<close>.
\<close>


locale sound_dg_spec_ltr = sound_dg_spec S gammaDG is_global
  for S :: "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
begin

theorem dg_postfix_collect_sound_ltr:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect is_global g S0 v \<subseteq> dg_gamma sigma v"
proof (rule ltr_collect_semantic_postfix)
  show "S0 \<subseteq> dg_gamma sigma (cfg_entry g)"
    by (rule dg_postfix_gamma_entry[OF pf sound0])
next
  fix u a w s s'
  assume e: "(u, a, w) \<in> intra g" and su: "s \<in> dg_gamma sigma u"
    and st: "edge_step a s = Some s'"
  have "s' \<in> edge_collect a (dg_gamma sigma u)"
    using su st by (auto simp: edge_collect_def)
  then show "s' \<in> dg_gamma sigma w"
    by (rule dg_postfix_gamma_edge[OF pf e])
next
  fix u dst pars args p cont s
  assume "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and "s \<in> dg_gamma sigma u"
  then show "call_enter is_global (CallEdge dst pars args) s \<in> dg_gamma sigma (FunctionEntry p)"
    by (rule dg_postfix_gamma_call[OF pf])
next
  fix cl dst pars args p cont s t
  assume "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and "s \<in> dg_gamma sigma cl" and "t \<in> dg_gamma sigma (FunctionResult p)"
  then show "combine_collect is_global dst s t \<in> dg_gamma sigma cont"
    by (rule dg_postfix_gamma_combine[OF pf])
qed

corollary dg_post_solution_collect_sound_ltr:
  assumes pp:
      "part_post_solution (dg_gen g bot0 s0d s0g) x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_enter:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (FunctionEntry p, ()) \<in> vars"
    and cover_combine:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (k, ()) \<in> vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect is_global g S0 v \<subseteq> dg_gamma sigma v"
proof -
  have pf: "dg_postfix g s0d s0g sigma"
    by (rule dg_post_solution_postfix
          [OF pp cover_entry cover_edge cover_enter cover_combine finI finC])
  show ?thesis by (rule dg_postfix_collect_sound_ltr[OF pf sound0])
qed

end
locale sound_dg_spec_ltr_for = sound_dg_spec S gammaDG gs
  for S :: "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
begin

theorem dg_postfix_collect_sound_ltr_for:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect gs g S0 v \<subseteq> dg_gamma sigma v"
proof (rule ltr_collect_semantic_postfix)
  show "S0 \<subseteq> dg_gamma sigma (cfg_entry g)"
    by (rule dg_postfix_gamma_entry[OF pf sound0])
next
  fix u a w s s'
  assume e: "(u, a, w) \<in> intra g" and su: "s \<in> dg_gamma sigma u"
    and st: "edge_step a s = Some s'"
  have "s' \<in> edge_collect a (dg_gamma sigma u)"
    using su st by (auto simp: edge_collect_def)
  then show "s' \<in> dg_gamma sigma w"
    by (rule dg_postfix_gamma_edge[OF pf e])
next
  fix u dst pars args p cont s
  assume "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and "s \<in> dg_gamma sigma u"
  then show "call_enter gs (CallEdge dst pars args) s \<in> dg_gamma sigma (FunctionEntry p)"
    by (rule dg_postfix_gamma_call[OF pf])
next
  fix cl dst pars args p cont s t
  assume "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and "s \<in> dg_gamma sigma cl" and "t \<in> dg_gamma sigma (FunctionResult p)"
  then show "combine_collect gs dst s t \<in> dg_gamma sigma cont"
    by (rule dg_postfix_gamma_combine[OF pf])
qed

corollary dg_post_solution_collect_sound_ltr_for:
  assumes pp:
      "part_post_solution (dg_gen g bot0 s0d s0g) x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_enter:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (FunctionEntry p, ()) \<in> vars"
    and cover_combine:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (k, ()) \<in> vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect gs g S0 v \<subseteq> dg_gamma sigma v"
proof -
  have pf: "dg_postfix g s0d s0g sigma"
    by (rule dg_post_solution_postfix
          [OF pp cover_entry cover_edge cover_enter cover_combine finI finC])
  show ?thesis by (rule dg_postfix_collect_sound_ltr_for[OF pf sound0])
qed

end



locale sound_dg_hooks_ltr =
  sound_dg_hooks gammaDG gs edge_tree combine_tree enter_tree
  for gammaDG :: "'D::bounded_semilattice_sup_bot \<Rightarrow>
      'G::bounded_semilattice_sup_bot \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and edge_tree :: "pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
    and combine_tree :: "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
    and enter_tree :: "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
begin

theorem hook_postfix_collect_sound_ltr:
  assumes pf: "hook_postfix g s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect gs g S0 v \<subseteq> dg_hook_gamma gammaDG sigma v"
proof (rule ltr_collect_semantic_postfix)
  show "S0 \<subseteq> dg_hook_gamma gammaDG sigma (cfg_entry g)"
  proof -
    have d_le: "s0d \<le> dg_hook_D sigma (cfg_entry g)"
      by (rule hook_postfix_entryD[OF pf])
    have g_le: "s0g \<le> dg_hook_G sigma"
      by (rule hook_postfix_entryG[OF pf])
    have "gammaDG s0d s0g \<subseteq>
        dg_hook_gamma gammaDG sigma (cfg_entry g)"
      unfolding dg_hook_gamma_def
      by (rule gammaDG_mono[OF d_le g_le])
    then show ?thesis using sound0 by blast
  qed
next
  fix u a w s s'
  assume edge: "(u, a, w) \<in> intra g"
    and sin: "s \<in> dg_hook_gamma gammaDG sigma u"
    and step: "edge_step a s = Some s'"
  have "s' \<in> edge_collect a (dg_hook_gamma gammaDG sigma u)"
    using sin step by (auto simp: edge_collect_def)
  then show "s' \<in> dg_hook_gamma gammaDG sigma w"
    by (rule set_mp[OF hook_postfix_edge[OF pf edge]])
next
  fix u dst fs args p cont s
  assume call:
      "(u, CallEdge dst fs args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> dg_hook_gamma gammaDG sigma u"
  then show "call_enter gs (CallEdge dst fs args) s \<in>
      dg_hook_gamma gammaDG sigma (FunctionEntry p)"
    by (rule hook_postfix_enter[OF pf])
next
  fix caller dst fs args p cont s t
  assume call:
      "(caller, CallEdge dst fs args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
    and tin: "t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p)"
  then show "combine_collect gs dst s t \<in>
      dg_hook_gamma gammaDG sigma cont"
    by (rule hook_postfix_combine[OF pf])
qed

corollary hook_post_solution_collect_sound_ltr:
  assumes pp:
      "part_post_solution (hook_gen g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_enter:
      "\<And>caller dst fs args p k.
        (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
        \<Longrightarrow> (FunctionEntry p, ()) \<in> vars"
    and cover_combine:
      "\<And>caller dst fs args p k.
        (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
        \<Longrightarrow> (k, ()) \<in> vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect gs g S0 v \<subseteq> dg_hook_gamma gammaDG sigma v"
proof -
  have pf: "hook_postfix g s0d s0g sigma"
    by (rule hook_post_solution_postfix
      [OF pp cover_entry cover_edge cover_enter cover_combine finI finC])
  show ?thesis
    by (rule hook_postfix_collect_sound_ltr[OF pf sound0])
qed

end


end


