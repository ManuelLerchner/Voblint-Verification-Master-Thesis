section \<open>IP interval flagship over the stack-faithful semantics\<close>

theory Example_Interval_DG_IP_Flagship_LTR
  imports
    Example_Interval_DG_IP_Flagship
    "Voblint_Analysis.Interval_DG_LTR"
    "Voblint_Formalization.Source_Activation_Sound"
begin

text \<open>
  The interprocedural interval flagship's soundness restated against the stack-faithful local-trace
  collecting @{const ltr_collect}, over the same computed D/G solution @{const twice_sol}.  It
  reuses the post-solution hypotheses of @{thm [source] twice_collect_sound} unchanged and delegates
  to @{thm [source] ivl_dg_post_solution_collect_sound_ltr}.  It does NOT route through
  \<open>ltr_collect_le_cfg_collect\<close>: soundness comes from @{const valid_ltr}'s matched return rule, so
  each of the two calls into @{term \<open>twice_cfg\<close>} recovers its own caller rather than pairing every
  caller with every callee exit.  The broad @{thm [source] twice_collect_sound} stays available for
  compatibility.

  A separate leaf, so the trace stack (@{const ltr.Call} shadows the bare \<open>Call\<close> constructor of
  @{theory Voblint_Examples.Example_Interval_DG_IP_Flagship}) stays out of the wide example.
\<close>

theorem twice_collect_sound_ltr:
  "ltr_collect twice_cfg cinit_stores v
     \<subseteq> ivl_dg_gamma (fun_of_dg_st \<circ> snd twice_sol) v"
  by (rule ivl_dg_post_solution_collect_sound_ltr
        [OF twice_pp_abs[folded ivl_dg_generator_def]
            twice_cover_entry twice_cover_edge twice_cover_combine
            twice_finE twice_finC twice_sound0])

text \<open>
  \<^bold>\<open>The source-level capstone over the trace semantics.\<close>  A real IMP2 run of @{term \<open>twice_main\<close>}
  --- including the two calls into @{term \<open>twice\<close>} and the return assignments --- bounded through
  @{const ltr_collect} instead of @{const cfg_collect}: the monovariant source bridge
  @{thm [source] source_reaches_ltr_collect} lands the reached store in the stack-faithful collecting,
  and @{thm [source] twice_collect_sound_ltr} closes it into the computed interval.  No
  @{const cfg_collect} appears in the chain.
\<close>
theorem twice_source_run_sound_ltr:
  assumes run: "psteps twice_pi (twice_main, s, []) src'"
      and init: "s \<in> cinit_stores"
  shows "\<exists>v t stk. concrete_program_match twice_pi twice_procs twice_main src' (v, t, stk)
                   \<and> t \<in> ivl_dg_gamma (fun_of_dg_st \<circ> snd twice_sol) v"
proof -
  obtain residual t frs where src': "src' = (residual, t, frs)" by (cases src')
  have sc: "source_com twice_main" by (simp add: twice_main_def twice_program_def)
  obtain v stk where m: "concrete_program_match twice_pi twice_procs twice_main src' (v, t, stk)"
      and coll0: "t \<in> ltr_collect (compile_prog twice_pi twice_procs twice_main) cinit_stores v"
    using source_reaches_ltr_collect[OF twice_wf sc init run[unfolded src']]
    unfolding src' by blast
  have coll: "t \<in> ltr_collect twice_cfg cinit_stores v"
    using coll0 by (simp add: twice_cfg_def)
  have "t \<in> ivl_dg_gamma (fun_of_dg_st \<circ> snd twice_sol) v"
    using coll twice_collect_sound_ltr by blast
  then show ?thesis using m by blast
qed

end
