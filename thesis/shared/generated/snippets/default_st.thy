(* src/Abstract_Interpreter/Exec/State/Default_St_Base.thy *)
quotient_type ('k, 'a) gdefault_st =
  "('k, 'a::bot) gdefault_st_rep" / "eq_default_st_rep"
  morphisms rep_default_st Abs_default_st
  by (rule equivp_eq_default_st_rep)
