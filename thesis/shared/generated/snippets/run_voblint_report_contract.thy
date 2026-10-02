(* src/Executable_Surface/CLI/Analysis_Certified.thy *)
theorem run_voblint_report_contract:
  assumes "run_voblint config p = Analysed res"
  shows "report_config res = config" "report_cfg res = prog_cfg p"
    and "well_formed_report res" "sound_report p res"
