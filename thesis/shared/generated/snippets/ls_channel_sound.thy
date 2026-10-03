(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
lemma ls_channel_sound:
  assumes "sound_local_spec \<G> gm c" and "s \<in> gm x"
  shows "eval_query.oracle_holds (ls_channel c x) s"
