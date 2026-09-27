(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
theorem mcp_combine_sound:
  assumes sound: "\<forall>(g, c) \<in> set gcs. mcp_component_sound \<G> g c"
    and indep: "mcp_independent gcs" and ne: "gcs \<noteq> []"
  shows "mcp_component_sound \<G> (mcp_gamma (map fst gcs)) (mcp_combine (map snd gcs))"
