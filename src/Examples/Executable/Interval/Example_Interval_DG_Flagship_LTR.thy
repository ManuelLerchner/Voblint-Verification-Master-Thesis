section \<open>Interval flagship over the stack-faithful semantics\<close>

theory Example_Interval_DG_Flagship_LTR
  imports
    Example_Interval_DG_Flagship
    "Voblint_Analysis.Interval_DG_LTR"
    "Voblint_Formalization.Source_Activation_Sound"
begin

text \<open>
  The flagship's end-to-end soundness restated against the stack-faithful local-trace collecting
  @{const ltr_collect}, over the same solver-computed D/G solution @{const flagship_sol}.  It reuses
  the post-solution hypotheses of @{thm [source] flagship_collect_sound} unchanged and delegates to
  @{thm [source] ivl_dg_post_solution_collect_sound_ltr}, so the discovered loop invariant now bounds
  the trace semantics directly.  It does NOT go through \<open>ltr_collect_le_cfg_collect\<close>; the broad
  @{thm [source] flagship_collect_sound} remains available for compatibility.

  A separate leaf keeps the trace stack (@{const ltr.Call} shadows the bare \<open>Call\<close> constructor)
  out of the wide flagship theory.
\<close>

theorem flagship_collect_sound_ltr:
  "ltr_collect flagship_cfg cinit_stores v
     \<subseteq> ivl_dg_gamma (fun_of_dg_st \<circ> snd flagship_sol) v"
  by (rule ivl_dg_post_solution_collect_sound_ltr
        [OF flagship_pp_abs[folded ivl_dg_generator_def]
            flagship_cover_entry flagship_cover_edge flagship_cover_combine
            flagship_finE flagship_finC flagship_sound0])

text \<open>
  \<^bold>\<open>The source-level capstone over the trace semantics.\<close>  The same real IMP2 source run, now
  bounded through @{const ltr_collect} rather than @{const cfg_collect}: the monovariant source
  bridge @{thm [source] source_reaches_ltr_collect} lands the reached store in the stack-faithful
  collecting of the compiled program, and @{thm [source] flagship_collect_sound_ltr} closes it into
  the solver-computed interval.  No @{const cfg_collect} appears in the chain.
\<close>
theorem flagship_source_run_sound_ltr:
  assumes run: "psteps Map.empty (flagship_prog, s, []) src'"
      and init: "s \<in> cinit_stores"
  shows "\<exists>v t stk. concrete_program_match Map.empty [] flagship_prog src' (v, t, stk)
                   \<and> t \<in> ivl_dg_gamma (fun_of_dg_st \<circ> snd flagship_sol) v"
proof -
  obtain residual t frs where src': "src' = (residual, t, frs)" by (cases src')
  have sc: "source_com flagship_prog" by (simp add: flagship_prog_def)
  obtain v stk where m: "concrete_program_match Map.empty [] flagship_prog src' (v, t, stk)"
      and coll0: "t \<in> ltr_collect (compile_prog Map.empty [] flagship_prog) cinit_stores v"
    using source_reaches_ltr_collect[OF flagship_wf sc init run[unfolded src']]
    unfolding src' by blast
  have coll: "t \<in> ltr_collect flagship_cfg cinit_stores v"
    using coll0 by (simp add: flagship_cfg_def)
  have "t \<in> ivl_dg_gamma (fun_of_dg_st \<circ> snd flagship_sol) v"
    using coll flagship_collect_sound_ltr by blast
  then show ?thesis using m by blast
qed

end
