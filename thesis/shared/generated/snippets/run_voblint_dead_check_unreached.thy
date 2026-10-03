(* src/Executable_Surface/CLI/Analysis_Certified.thy *)
corollary run_voblint_dead_check_unreached:
  assumes "run_voblint config p = Analysed res"
    and "chk \<in> set (report_checks res)" and "check_verdict chk = Dead"
  shows "\<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> (check_point chk) = {}"
