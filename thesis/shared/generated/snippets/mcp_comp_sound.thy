(* src/Executable_Surface/CLI/MCP_Analyses.thy *)
theorem mcp_comp_sound:
  assumes "distinct as" and "as \<noteq> []"
  shows "sound_local_spec (declared_global p)
           (mcp_gamma (map (part_gamma (declared_global p)) as))
           (mcp_comp as (declared_global p) p)"
