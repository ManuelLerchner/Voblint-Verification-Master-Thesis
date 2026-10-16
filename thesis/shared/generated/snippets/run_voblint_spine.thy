(* src/Executable_Surface/CLI/Run_Voblint.thy *)
theorem run_voblint_spine:
  fixes p :: imp_prog and ds :: kind_decls and adm c\<^sub>0
  defines "g \<equiv> elab_cfg p ds" and "S \<equiv> init_stores (kenv_of ds)"
  assumes run: "run_voblint conf ds p = Analysed res"
    and s0: "s0 \<in> S"
    and exec:
      "(kenv_of ds),(elab_ptable p ds) \<turnstile> (main_body (elab_ptable p ds), s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
    and has_ctx: "\<And>t. t \<in> \<T>\<^bsub>kenv_of ds,g,S\<^esub>
                   \<Longrightarrow> \<exists>c. activation_context_rel (kenv_of ds) adm c\<^sub>0 g t c"
    and buckets: "\<And>v. (\<Union>c'. \<A>\<^bsub>kenv_of ds,adm,c\<^sub>0,g,S\<^esub> v c')
                   = reaching ds p v"
  shows "\<exists>v stk t c. elab_ptable p ds, g, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> activation_trace_repr (kenv_of ds) g S (v, s, stk) t
           \<and> activation_context_rel (kenv_of ds) adm c\<^sub>0 g t c
           \<and> s \<in> \<A>\<^bsub>kenv_of ds,adm,c\<^sub>0,g,S\<^esub> v c
           \<and> (\<Union>c'. \<A>\<^bsub>kenv_of ds,adm,c\<^sub>0,g,S\<^esub> v c') = reaching ds p v
           \<and> (\<exists>d. Lifted d \<in> report_states_at res v
                  \<and> s \<in> mcp.act_gamma ds (activation_of (conf_analyses conf)) d)
           \<and> (\<forall>c. PROVED res v c \<longrightarrow> truthy (eval c s))
           \<and> (\<forall>c. REFUTED res v c \<longrightarrow> \<not> truthy (eval c s))"
