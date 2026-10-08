(* src/Abstract_Interpreter/Framework/Checks/Contextual_Check_Report.thy *)
fun classify_point ::
  "(exp \<Rightarrow> 'a \<Rightarrow> check_result) \<Rightarrow> exp \<Rightarrow> 'a lifted \<Rightarrow> contextual_verdict"
where
  "classify_point classify c Bot = Dead"
| "classify_point classify c (Lifted st) = Decided (classify c st)"
