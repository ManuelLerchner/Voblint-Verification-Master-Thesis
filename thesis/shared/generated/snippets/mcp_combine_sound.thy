(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
theorem mcp_combine_sound:
  assumes sound: "\<forall>(\<gamma>\<^sub>i, c\<^sub>i) \<in> set comps. sound_local_spec \<G> \<gamma>\<^sub>i c\<^sub>i"
    and indep: "mcp_independent comps" and ne: "comps \<noteq> []"
  shows "sound_local_spec \<G> (mcp_gamma (map fst comps)) (mcp_combine (map snd comps))"
