(* src/Executable_Surface/CLI/Analysis_Certified.thy *)
theorem run_voblint_spine:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
      and S_def: "S \<equiv> cinit_stores (declared_global p)"
  assumes s0: "s0 \<in> S"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint config p = Analysed res"
      and has_ctx: "\<And>t. t \<in> \<T>\<^bsub>\<G>,g,S\<^esub> \<Longrightarrow> \<exists>c. activation_context_rel \<G> adm c\<^sub>0 g t c"
      and buckets: "\<And>v. (\<Union>c'. \<A>\<^bsub>\<G>,adm,c\<^sub>0,g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v"
  shows "\<exists>v stk t c. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> activation_trace_repr \<G> g S (v, s, stk) t
           \<and> activation_context_rel \<G> adm c\<^sub>0 g t c
           \<and> s \<in> \<A>\<^bsub>\<G>,adm,c\<^sub>0,g,S\<^esub> v c
           \<and> (\<Union>c'. \<A>\<^bsub>\<G>,adm,c\<^sub>0,g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v
           \<and> \<C>\<^bsub>\<G>,g,S\<^esub> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>
           \<and> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> \<V>\<^bsub>res\<^esub> v"
