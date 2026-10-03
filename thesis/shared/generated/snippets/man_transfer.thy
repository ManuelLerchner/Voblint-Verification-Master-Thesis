(* src/Abstract_Interpreter/Framework/Spec/DG_Manager.thy *)
type_synonym ('x,'k,'v,'dl,'dg) man_transfer =
  "('x,'k,'v,'dl,'dg) man \<Rightarrow> ('x,'k,('dl,'dg) dg_state,'dl) strategy_program"
