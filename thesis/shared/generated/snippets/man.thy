(* src/Abstract_Interpreter/Framework/Spec/DG_Manager.thy *)
record ('x,'k,'v,'dl,'dg) man =
  man_local :: 'dl
  man_global :: "'v \<Rightarrow> ('x,'k,('dl,'dg) dg_state,'dg) strategy_program"
  man_sideg :: "'v \<Rightarrow> 'dg \<Rightarrow> ('x,'k,('dl,'dg) dg_state,unit) strategy_program"
  man_ask :: "query \<Rightarrow> ('x,'k,('dl,'dg) dg_state,answer) strategy_program"
