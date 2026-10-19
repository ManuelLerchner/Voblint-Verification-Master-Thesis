(* src/Executable_Surface/CLI/Run_Voblint.thy *)
theorem run_voblint_check_sound:
  assumes run: "run_voblint conf ds p = Analysed res"
    and s0: "s0 \<in> init_stores (kenv_of ds)"
    and exec:
      "(kenv_of ds),(elab_ptable p ds) \<turnstile> (main_body (elab_ptable p ds), s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
    and chk: "next_check residual = Some (l, e)"
  shows "\<exists>c \<in> set (report_checks res). check_label c = l \<and> check_exp c = e
           \<and> s \<in> reaching ds p (check_point c)
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (eval e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (eval e s))"
