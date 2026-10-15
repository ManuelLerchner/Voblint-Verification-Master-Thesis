(* src/Executable_Surface/CLI/Run_Voblint.thy *)
theorem run_voblint_arithmetic_safe:
  assumes run: "run_voblint conf ds p = Analysed res"
    and absent: "SAFE res v"
    and s: "s \<in> reaching ds p v"
  shows run_voblint_arithmetic_safe_intra:
      "(v, a, w) \<in> intra (elab_cfg p ds) \<Longrightarrow> e \<in> set (edge_expressions a)
         \<Longrightarrow> ob \<in> set (arith_obligations e) \<Longrightarrow> s \<Turnstile> ob"
    and run_voblint_arithmetic_safe_call:
      "(v, ca, ce, k) \<in> calls (elab_cfg p ds) \<Longrightarrow> e \<in> set (ce_args ca)
         \<Longrightarrow> ob \<in> set (arith_obligations e) \<Longrightarrow> s \<Turnstile> ob"
    and run_voblint_arithmetic_safe_return:
      "(u, ca, ce, k) \<in> calls (elab_cfg p ds) \<Longrightarrow> ce_dst ca = Some x
         \<Longrightarrow> (v, EA_Ret (Some e) (callee_of_entry ce), w) \<in> intra (elab_cfg p ds)
         \<Longrightarrow> \<not> ik_widens (exp_kind e) (kenv_of ds x)
         \<Longrightarrow> eval e s \<in> ik_range (kenv_of ds x)"
