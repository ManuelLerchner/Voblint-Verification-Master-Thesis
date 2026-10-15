(* src/Executable_Surface/CLI/Run_Voblint.thy *)
theorem run_voblint_report_contract:
  assumes "run_voblint conf ds p = Analysed res"
  shows "valid_activation (conf_analyses conf)" and "wf_program_compile_input_exec p"
    and "report_config res = conf" and "report_cfg res = elab_cfg p ds"
