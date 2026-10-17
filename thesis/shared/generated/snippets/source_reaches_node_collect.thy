(* src/Program_Model/Compile/Source_To_Trace.thy *)
theorem source_reaches_node_collect:
  assumes wf: "wf_program_compile_input p"
    and s0: "s0 \<in> S"
    and run:
      "\<kappa>,(elab_ptable p ds) \<turnstile> (main_body (elab_ptable p ds), s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "\<exists>v stk. elab_ptable p ds, elab_cfg p ds, prog_main_name
                    \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> \<C>\<^bsub>\<kappa>,elab_cfg p ds,S\<^esub> v"
