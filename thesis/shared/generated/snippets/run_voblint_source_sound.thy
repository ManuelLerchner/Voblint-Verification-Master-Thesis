(* src/Executable_Surface/CLI/Analysis_Certified.thy *)
theorem run_voblint_source_sound:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
  assumes s0: "s0 \<in> cinit_stores \<G>"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint config p = Analysed res"
  shows "\<exists>v stk. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> \<C>\<^bsub>\<G>,g,cinit_stores \<G>\<^esub> v
                 \<and> s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>
                 \<and> s \<in> \<V>\<^bsub>res\<^esub> v"
