(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
definition sound_local_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('s::order \<Rightarrow> store set) \<Rightarrow> 's local_spec \<Rightarrow> bool" where
  "sound_local_spec \<G> gm c \<longleftrightarrow>
     (\<forall>x y. x \<le> y \<longrightarrow> gm x \<subseteq> gm y)
     \<and> (\<forall>ch a x. edge_collect a (gm x \<inter> Collect (eval_query.channel_holds ch))
                  \<subseteq> gm (ls_step c ch a x))
     \<and> (\<forall>ch s ci p. s \<in> gm (fst p) \<longrightarrow> eval_query.channel_holds ch s \<longrightarrow>
          (\<exists>q \<in> set (ls_enter c ch ci p). s \<in> gm (fst q)
             \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                 \<in> gm (snd q)))
     \<and> (\<forall>ch ch' s t ci x de. s \<in> gm x \<longrightarrow> eval_query.channel_holds ch s \<longrightarrow>
          t \<in> gm de \<longrightarrow> eval_query.channel_holds ch' t \<longrightarrow>
          combine_collect \<G> (ci_dst ci) s t \<in> gm (ls_combine c ch ch' ci x de))
     \<and> (\<forall>ch s x q. s \<in> gm x \<longrightarrow> eval_query.channel_holds ch s \<longrightarrow>
          eval_holds q (ls_query c ch x q) s)"
