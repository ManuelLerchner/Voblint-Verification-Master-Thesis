(* src/Analyses/Shared/Result/DG_Live_Unknowns.thy *)
corollary entry_state_policy_of_terminates:
  assumes wf: "wf_program_compile_input p" and solves: "terminates (declared_global p) p"
  shows "\<forall>t \<in> \<T>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub>.
           \<exists>c. activation_context_rel (declared_global p) (admitted_contexts (declared_global p) p)
                 root_ctx (prog_cfg p) t c"
    and "\<A>\<^bsub>declared_global p,admitted_contexts (declared_global p) p,
           root_ctx,prog_cfg p,cinit_stores (declared_global p)\<^esub> v ctx
           \<subseteq> pgam p (reader (declared_global p) p (Inl (v, ctx))) (gsol p)"
