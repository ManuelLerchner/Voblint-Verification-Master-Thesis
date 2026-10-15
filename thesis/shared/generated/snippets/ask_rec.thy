(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
fun ask_rec :: "('e gchannel \<Rightarrow> 's \<Rightarrow> 'e gchannel) \<Rightarrow> nat \<Rightarrow> 'e gquery set \<Rightarrow> 's \<Rightarrow> 'e gchannel" where
  "ask_rec H 0 asked x q =
     Code.abort (STR ''query recursion exceeded query_depth'') (\<lambda>_. \<top>)"
| "ask_rec H (Suc n) asked x q =
     (if q \<in> asked then \<top> else H (ask_rec H n (insert q asked) x) x q)"
