(* src/Abstract_Interpreter/Framework/Spec/DG_Manager.thy *)
type_synonym ('e,'x,'k,'v,'dl,'dg) gman_transfer =
  "('e,'x,'k,'v,'dl,'dg) gman \<Rightarrow> ('x,'k,('dl,'dg) dg_state,'dl) strategy_program"
