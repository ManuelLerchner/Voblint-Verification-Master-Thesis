(* src/Abstract_Interpreter/Framework/Context/Routed_Context.thy *)
theorem activation_collect_dg_sound:
  fixes S0 :: "('vr \<Rightarrow> int) set" and c\<^sub>0 :: 'c
  assumes entry_cov: "(cfg_entry g, c\<^sub>0) \<in> vars"
    and init_sound: "S0 \<subseteq> \<gamma>\<^sub>D\<^sub>G d\<^sub>0 e\<^sub>0"
    and init_env_le: "e\<^sub>0 \<le> genv global_of sigma"
  shows "gactivation_collect adm c\<^sub>0 g S0 v c \<subseteq> cover v c"
