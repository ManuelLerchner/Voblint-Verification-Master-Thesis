(* src/Executable_Surface/CLI/Analysis_Certified.thy *)
theorem run_voblint_arithmetic_refuted:
  assumes "run_voblint config p = Analysed res"
    and "d \<in> set (report_diagnostics res)" and "diagnostic_verdict d = Check_Refuted"
    and "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> (diagnostic_point d)"
  shows "\<lbrakk>arithmetic_divisor (diagnostic_obligation d)\<rbrakk>\<^sub>e s = 0"
