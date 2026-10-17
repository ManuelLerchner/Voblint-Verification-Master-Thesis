(* src/Executable_Surface/CLI/Run_Voblint.thy *)
theorem run_voblint_source_sound:
  assumes run: "run_voblint conf ds p = Analysed res"
    and s0: "s0 \<in> init_stores (kenv_of ds)"
    and exec:
      "(kenv_of ds),(elab_ptable p ds) \<turnstile> (main_body (elab_ptable p ds), s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "\<exists>v stk. elab_ptable p ds, elab_cfg p ds, prog_main_name
                    \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> s \<in> reaching ds p v
           \<and> (\<exists>d. Lifted d \<in> report_states_at res v
                  \<and> s \<in> mcp.act_gamma ds (activation_of (conf_analyses conf)) d)
           \<and> \<not> DEAD res v
           \<and> (\<forall>c. PROVED res v c \<longrightarrow> truthy (eval c s))
           \<and> (\<forall>c. REFUTED res v c \<longrightarrow> \<not> truthy (eval c s))
           \<and> (SAFE res v \<longrightarrow> (\<forall>ob \<in> obligations_at ds p v. s \<Turnstile> ob))"
