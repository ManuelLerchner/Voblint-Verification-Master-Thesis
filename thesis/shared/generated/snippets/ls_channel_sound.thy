(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
lemma ls_channel_sound:
  assumes "gsound_local_spec \<gamma>\<^sub>c c" and "s \<in> \<gamma>\<^sub>c x"
  shows "geval_query.channel_holds ev (ls_channel c x) s"
