(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
definition mcp_gamma :: "('s \<Rightarrow> ('vr \<Rightarrow> int) set) list \<Rightarrow> 's \<Rightarrow> ('vr \<Rightarrow> int) set" where
  "mcp_gamma \<Gamma> x = (\<Inter>\<gamma>\<^sub>i \<in> set \<Gamma>. \<gamma>\<^sub>i x)"
