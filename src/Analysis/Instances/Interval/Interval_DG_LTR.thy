theory Interval_DG_LTR
  imports Interval_DG "Voblint_Analysis.DG_LTR_Sound"
begin

section \<open>Trace-native interval D/G endpoint\<close>

text \<open>
  The interval D/G post-solution endpoint restated over the stack-faithful \<open>ltr_collect\<close>.
  Identical premises to \<open>ivl_dg_post_solution_collect_sound\<close> --- only the concluding semantics
  differs, delegating to the generic trace-native \<open>dg_post_solution_collect_sound_ltr\<close>.  The
  \<open>cfg_collect\<close> endpoint stays available for compatibility.

  A separate leaf: it imports the trace stack (\<open>ltr.Call\<close> shadows the bare \<open>Call\<close> constructor),
  which must not leak into the wide interval consumers.
\<close>

theorem ivl_dg_post_solution_collect_sound_ltr:
  assumes pp: "part_post_solution (ivl_dg_generator g bot0 s0d s0g) x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_combine: "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines g \<Longrightarrow> (w, ()) \<in> vars"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and sound0: "S0 \<subseteq> \<lbrakk>s0d \<squnion> s0g\<rbrakk>"
  shows "ltr_collect g S0 v \<subseteq> ivl_dg_gamma sigma v"
proof -
  have pf: "ivl_dg.dg_postfix g s0d s0g sigma"
    by (rule ivl_dg.dg_post_solution_postfix
          [OF pp[unfolded ivl_dg_generator_def] cover_entry cover_edge cover_combine finE finC])
  show ?thesis
    unfolding ivl_dg_gamma_def
  proof (rule ltr_collect_semantic_postfix)
    show "S0 \<subseteq> ivl_dg.dg_gamma sigma (cfg_entry g)"
      by (rule ivl_dg.dg_postfix_gamma_entry[OF pf sound0[folded gamma_unit_def]])
  next
    fix u a w s
    assume e: "(u, a, w) \<in> edges g" and si: "s \<in> edge_collect a (ivl_dg.dg_gamma sigma u)"
    show "s \<in> ivl_dg.dg_gamma sigma w"
      by (rule ivl_dg.dg_postfix_gamma_edge[OF pf e si])
  next
    fix cc ex w dst s t
    assume c: "(cc, ex, w, dst) \<in> combines g" and sc: "s \<in> ivl_dg.dg_gamma sigma cc"
      and tc: "t \<in> ivl_dg.dg_gamma sigma ex"
    show "combine_collect dst s t \<in> ivl_dg.dg_gamma sigma w"
      by (rule ivl_dg.dg_postfix_gamma_combine[OF pf c sc tc])
  qed
qed

end
