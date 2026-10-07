(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
lemma ls_channel_sound:
  assumes "sound_local_spec \<G> \<gamma>\<^sub>c c" and "s \<in> \<gamma>\<^sub>c x"
  shows "eval_query.channel_holds (ls_channel c x) s"
