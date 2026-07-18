theory Sign_DG_LTR
  imports Sign_DG "Voblint_Analysis.DG_LTR_Sound"
begin

section \<open>Trace-native sign D/G endpoint\<close>

text \<open>
  The sign D/G post-solution endpoint restated over the stack-faithful @{const ltr_collect}.
  Identical premises to @{thm [source] sign_dg_post_solution_collect_sound}; only the concluding
  semantics differs, discharged through the free-standing @{thm [source] ltr_collect_semantic_postfix}
  and the sign interpretation's closure obligations.  The @{const cfg_collect} endpoint stays
  available for compatibility.

  Kept in a separate leaf so the trace stack (@{const ltr.Call} shadows the bare \<open>Call\<close>
  constructor) does not reach the wide sign consumers.
\<close>

theorem sign_dg_post_solution_collect_sound_ltr:
  assumes pp: "part_post_solution (sign_dg_generator g bot0 s0d s0g) x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_combine: "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines g \<Longrightarrow> (w, ()) \<in> vars"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and sound0: "S0 \<subseteq> \<lbrakk>s0d \<squnion> s0g\<rbrakk>"
  shows "ltr_collect g S0 v \<subseteq> sign_dg_gamma sigma v"
proof -
  have pf: "sign_dg.dg_postfix g s0d s0g sigma"
    by (rule sign_dg.dg_post_solution_postfix
          [OF pp[unfolded sign_dg_generator_def] cover_entry cover_edge cover_combine finE finC])
  show ?thesis
    unfolding sign_dg_gamma_def
  proof (rule ltr_collect_semantic_postfix)
    show "S0 \<subseteq> sign_dg.dg_gamma sigma (cfg_entry g)"
      by (rule sign_dg.dg_postfix_gamma_entry[OF pf sound0[folded gamma_unit_def]])
  next
    fix u a w s
    assume e: "(u, a, w) \<in> edges g" and si: "s \<in> edge_collect a (sign_dg.dg_gamma sigma u)"
    show "s \<in> sign_dg.dg_gamma sigma w"
      by (rule sign_dg.dg_postfix_gamma_edge[OF pf e si])
  next
    fix cc ex w dst s t
    assume c: "(cc, ex, w, dst) \<in> combines g" and sc: "s \<in> sign_dg.dg_gamma sigma cc"
      and tc: "t \<in> sign_dg.dg_gamma sigma ex"
    show "combine_collect dst s t \<in> sign_dg.dg_gamma sigma w"
      by (rule sign_dg.dg_postfix_gamma_combine[OF pf c sc tc])
  qed
qed

end
