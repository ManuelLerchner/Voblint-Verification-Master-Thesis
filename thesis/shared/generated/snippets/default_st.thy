(* src/Abstract_Interpreter/Exec/State/Default_St_Base.thy *)
quotient_type 'a default_st =
  "('a::bot) default_st_rep" / "eq_default_st_rep"
  morphisms rep_default_st Abs_default_st
  by (rule equivp_eq_default_st_rep)
