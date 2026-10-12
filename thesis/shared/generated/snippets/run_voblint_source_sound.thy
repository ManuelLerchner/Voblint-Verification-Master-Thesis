(* src/Executable_Surface/CLI/Analysis_Certified.thy *)
theorem run_voblint_source_sound:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and E_def: "\<Pi>\<^sub>e \<equiv> elab_pt (prog_table p) (prog_procs p)"
      and g_def: "g \<equiv> prog_cfg p"
  assumes s0: "s0 \<in> cinit_stores \<G>"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint config p = Analysed res"
  shows "\<exists>c stk. erase c = residual
               \<and> \<G>, \<Pi>\<^sub>e \<turnstile> (main_body \<Pi>\<^sub>e, s0, []) \<rightarrow>\<^sub>p\<^sup>* (c, s, frs)
               \<and> \<Pi>\<^sub>e, g, prog_main_name \<turnstile> (c, s, frs) \<approx> (point c, s, stk)
               \<and> \<Pi>, g, prog_main_name \<turnstile> (residual, s, frs) \<approx> (point c, s, stk)
               \<and> s \<in> \<C>\<^bsub>\<G>,g,cinit_stores \<G>\<^esub> (point c)
               \<and> s \<in> \<R>\<^bsub>res\<^esub> (point c)
               \<and> s \<in> \<V>\<^bsub>res\<^esub> (point c)"
