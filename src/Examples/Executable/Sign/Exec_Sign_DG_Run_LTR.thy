section \<open>Sign D/G run over the stack-faithful semantics\<close>

theory Exec_Sign_DG_Run_LTR
  imports
    Exec_Sign_DG_Run
    "Voblint_Analysis.Sign_DG"
begin

text \<open>
  The sign D/G run's soundness restated against the stack-faithful local-trace collecting
  @{const ltr_collect}, over the same solver-computed solution @{const dgEx_sol}.  It reuses the
  post-solution hypotheses of @{thm [source] dgEx_collect_sound} unchanged and delegates to
  @{thm [source] sign_dg_post_solution_collect_sound}, directly on the trace semantics.


  A separate leaf: the trace stack (@{const ltr.Call} shadows the bare \<open>Call\<close> constructor) must
  not reach the wide example.
\<close>

theorem dgEx_collect_sound_ltr:
  "ltr_collect gEx cinit_stores v \<subseteq> sign_dg_gamma (fun_of_dg_st \<circ> snd dgEx_sol) v"
  by (rule sign_dg_post_solution_collect_sound
        [OF dgEx_pp_abs[folded sign_dg_generator_def]
            dgEx_cover_entry dgEx_cover_edge dgEx_cover_combine gEx_finE gEx_finC dgEx_sound0])

end
