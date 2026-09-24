(* src/Abstract_Interpreter/Exec/State/Exec_St_Base.thy *)
quotient_type 'a resolved_st_q =
  "('a::bot) resolved_st" / "eq_resolved_st"
  morphisms rep_resolved_st Abs_resolved_st
  by (rule equivp_eq_resolved_st)
