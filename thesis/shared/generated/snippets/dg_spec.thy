(* src/Abstract_Interpreter/Framework/Spec/DG_Spec.thy *)
record ('vr,'e,'x,'k,'v,'dl,'dg) gdg_spec =
  dgs_skip           :: "('e,'x,'k,'v,'dl,'dg) gman_transfer" ("skip\<^sup>\<sharp>")
  dgs_assign         :: "'vr \<Rightarrow> 'e \<Rightarrow> ('e,'x,'k,'v,'dl,'dg) gman_transfer" ("assign\<^sup>\<sharp>")
  dgs_special        :: "'e gspecial_call \<Rightarrow> 'vr \<Rightarrow> ('e,'x,'k,'v,'dl,'dg) gman_transfer" ("special\<^sup>\<sharp>")
  dgs_branch         :: "'e \<Rightarrow> bool \<Rightarrow> ('e,'x,'k,'v,'dl,'dg) gman_transfer" ("branch\<^sup>\<sharp>")
  dgs_body           :: "pname \<Rightarrow> ('e,'x,'k,'v,'dl,'dg) gman_transfer" ("body\<^sup>\<sharp>")
  dgs_return         :: "'e option \<Rightarrow> pname \<Rightarrow> ('e,'x,'k,'v,'dl,'dg) gman_transfer" ("return\<^sup>\<sharp>")
  dgs_enter          :: "('vr,'e) gcall_info \<Rightarrow> ('e,'x,'k,'v,'dl,'dg) gman_enter_transfer"
    ("enter\<^sup>\<sharp>")
  dgs_event          :: "'e ganalysis_event \<Rightarrow> ('e,'x,'k,'v,'dl,'dg) gman_transfer" ("event\<^sup>\<sharp>")
  dgs_combine_env    :: "('vr,'e) gcall_info \<Rightarrow> ('e,'x,'k,'v,'dl,'dg) gman_combine_transfer"
    ("combine'_env\<^sup>\<sharp>")
  dgs_combine_assign :: "('vr,'e) gcall_info \<Rightarrow> ('e,'x,'k,'v,'dl,'dg) gman_combine_transfer"
    ("combine'_assign\<^sup>\<sharp>")
  dgs_query          :: "('e,'x,'k,'v,'dl,'dg) gman_query"
