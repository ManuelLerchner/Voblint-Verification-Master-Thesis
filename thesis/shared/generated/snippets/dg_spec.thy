(* src/Abstract_Interpreter/Framework/Spec/DG_Spec.thy *)
record ('x,'k,'v,'dl,'dg) dg_spec =
  dgs_skip           :: "('x,'k,'v,'dl,'dg) man_transfer" ("skip\<^sup>\<sharp>")
  dgs_assign         :: "vname \<Rightarrow> exp \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("assign\<^sup>\<sharp>")
  dgs_special        :: "special_call \<Rightarrow> vname \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("special\<^sup>\<sharp>")
  dgs_branch         :: "exp \<Rightarrow> bool \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("branch\<^sup>\<sharp>")
  dgs_body           :: "pname \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("body\<^sup>\<sharp>")
  dgs_return         :: "exp option \<Rightarrow> pname \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("return\<^sup>\<sharp>")
  dgs_enter          :: "call_info \<Rightarrow> ('x,'k,'v,'dl,'dg) man_enter_transfer" ("enter\<^sup>\<sharp>")
  dgs_event          :: "analysis_event \<Rightarrow> ('x,'k,'v,'dl,'dg) man_transfer" ("event\<^sup>\<sharp>")
  dgs_combine_env    :: "call_info \<Rightarrow> ('x,'k,'v,'dl,'dg) man_combine_transfer" ("combine'_env\<^sup>\<sharp>")
  dgs_combine_assign :: "call_info \<Rightarrow> ('x,'k,'v,'dl,'dg) man_combine_transfer" ("combine'_assign\<^sup>\<sharp>")
  dgs_query          :: "('x,'k,'v,'dl,'dg) man_query"
