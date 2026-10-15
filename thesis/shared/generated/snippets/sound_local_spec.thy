(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
definition gsound_local_spec ::
  "('s::order \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> ('vr,'e,'s) glocal_spec \<Rightarrow> bool" where
  "gsound_local_spec gm c \<longleftrightarrow>
     (\<forall>x y. x \<le> y \<longrightarrow> gm x \<subseteq> gm y)
     \<and> (\<forall>ch a x. gedge_collect a (gm x \<inter> Collect (geval_query.channel_holds ev ch))
                  \<subseteq> gm (ls_step c ch a x))
     \<and> (\<forall>ch s ci p. s \<in> gm (fst p) \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow>
          (\<exists>q \<in> set (ls_enter c ch ci p). s \<in> gm (fst q)
             \<and> gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                 \<in> gm (snd q)))
     \<and> (\<forall>ch ch' s t ci x de. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow>
          t \<in> gm de \<longrightarrow> geval_query.channel_holds ev ch' t \<longrightarrow>
          gcombine_collect (ci_dst ci) s t \<in> gm (ls_combine c ch ch' ci x de))
     \<and> (\<forall>ch s x q. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow>
          geval_holds ev q (ls_query c ch x q) s)"
