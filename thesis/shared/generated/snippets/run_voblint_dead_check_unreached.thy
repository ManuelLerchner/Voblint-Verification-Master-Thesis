(* src/Executable_Surface/CLI/Analysis_Certified.thy *)
corollary run_voblint_dead_check_unreached:
  assumes terminates: "config_terminates D rule ctx p"
      and ans: "run_voblint D rule ctx p = Analysed res"
      and listed: "chk \<in> set (res_checks res)"
      and dead: "check_verdict chk = Dead"
  shows "\<C>\<^bsub>declared_global p,prog_cfg p,
            cinit_stores (declared_global p)\<^esub> (check_point chk) = {}"
