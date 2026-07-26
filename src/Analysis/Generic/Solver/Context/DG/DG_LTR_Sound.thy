theory DG_LTR_Sound
  imports DG_Soundness "Voblint_CFG.LTR_Abstract"
begin

section \<open>Trace-native D/G collecting soundness\<close>

text \<open>
  The D/G post-solution endpoint is stated over the stack-faithful local-trace collector
  \<^const>\<open>ltr_collect\<close>.  Its entry, edge, and combine closure obligations feed
  \<open>ltr_collect_semantic_postfix\<close>; matched returns are supplied by \<^const>\<open>valid_ltr\<close>.
\<close>


context sound_dg_spec
begin

theorem dg_postfix_collect_sound_ltr:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect g S0 v \<subseteq> dg_gamma sigma v"
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
  then show "call_enter (CallEdge dst pars args) s \<in> dg_gamma sigma (FunctionEntry p)"
    by (rule dg_postfix_gamma_call[OF pf])
next
  fix cl dst pars args p cont s t
  assume "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and "s \<in> dg_gamma sigma cl" and "t \<in> dg_gamma sigma (FunctionResult p)"
  then show "combine_collect dst s t \<in> dg_gamma sigma cont"
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
  shows "ltr_collect g S0 v \<subseteq> dg_gamma sigma v"
proof -
  have pf: "dg_postfix g s0d s0g sigma"
    by (rule dg_post_solution_postfix
          [OF pp cover_entry cover_edge cover_enter cover_combine finI finC])
  show ?thesis by (rule dg_postfix_collect_sound_ltr[OF pf sound0])
qed

end

end
