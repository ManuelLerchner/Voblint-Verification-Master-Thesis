(* src/Analyses/Shared/Result/Source_Activation_Sound.thy *)
theorem source_reaches_ltr_collect:
  assumes wf: "wf_compile_input \<G> Pi ps"
    and s0: "s0 \<in> S"
    and run: "\<G>, Pi \<turnstile> (main_body Pi, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "\<exists>v stk. Pi, compile_prog Pi ps \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> \<C>\<^bsub>\<G>,compile_prog Pi ps,S\<^esub> v"
