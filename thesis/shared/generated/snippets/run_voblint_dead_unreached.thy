(* src/Executable_Surface/CLI/Run_Voblint.thy *)
corollary run_voblint_dead_unreached:
  "run_voblint conf ds p = Analysed res \<Longrightarrow> DEAD res v \<Longrightarrow> reaching ds p v = {}"
