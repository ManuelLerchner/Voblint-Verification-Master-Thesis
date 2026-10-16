(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
definition mcp_gamma :: "('s \<Rightarrow> store set) list \<Rightarrow> 's \<Rightarrow> store set" where
  "mcp_gamma \<Gamma> x = (\<Inter>\<gamma>\<^sub>i \<in> set \<Gamma>. \<gamma>\<^sub>i x)"
