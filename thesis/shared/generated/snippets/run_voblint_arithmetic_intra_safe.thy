(* src/Executable_Surface/CLI/Analysis_Certified.thy *)
corollary run_voblint_arithmetic_intra_safe:
  assumes "run_voblint config p = Analysed res"
    and "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
    and "\<forall>d \<in> set (report_diagnostics res). diagnostic_point d \<noteq> v"
    and "(v, action, w) \<in> intra (prog_cfg p)"
    and "e \<in> set (edge_expressions action)"
    and "divisor \<in> expression_divisors e"
  shows "\<lbrakk>divisor\<rbrakk>\<^sub>e s \<noteq> 0"
