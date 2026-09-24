(* src/Abstract_Interpreter/Framework/Context/Routed_Context.thy *)
lemma activation_collect_dg_sound:
  fixes S0 :: "store set" and startcontext :: 'c
  assumes entry_cov: "(cfg_entry g, startcontext) \<in> vars"
    and s0_sound: "S0 \<subseteq> \<gamma>\<^sub>D\<^sub>G s0d s0g"
  shows "\<A>\<^bsub>\<G>,R,startcontext,g,S0\<^esub> v ctx
           \<subseteq> \<gamma>\<^sub>M (sg (Inl (v, ctx)))"
