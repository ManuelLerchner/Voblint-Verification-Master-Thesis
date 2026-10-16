(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
fun ask_rec :: "(channel \<Rightarrow> 's \<Rightarrow> channel) \<Rightarrow> nat \<Rightarrow> query set \<Rightarrow> 's \<Rightarrow> channel" where
  "ask_rec H 0 asked x q =
     Code.abort (STR ''query recursion exceeded query_depth'') (\<lambda>_. \<top>)"
| "ask_rec H (Suc n) asked x q =
     (if q \<in> asked then \<top> else H (ask_rec H n (insert q asked) x) x q)"
