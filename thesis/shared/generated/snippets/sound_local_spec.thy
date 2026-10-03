(* src/Abstract_Interpreter/Framework/Cooperation/MCP_Spec.thy *)
definition sound_local_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('s::order \<Rightarrow> store set) \<Rightarrow> 's local_spec \<Rightarrow> bool" where
  "sound_local_spec \<G> gm c \<longleftrightarrow>
     (\<forall>x y. x \<le> y \<longrightarrow> gm x \<subseteq> gm y)
     \<and> (\<forall>A a x. edge_collect a (gm x \<inter> Collect (eval_query.oracle_holds A))
                  \<subseteq> gm (ls_step c A a x))
     \<and> (\<forall>A s ci p. s \<in> gm (fst p) \<longrightarrow> eval_query.oracle_holds A s \<longrightarrow>
          (\<exists>q \<in> set (ls_enter c A ci p). s \<in> gm (fst q)
             \<and> call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                 \<in> gm (snd q)))
     \<and> (\<forall>A B s t ci x de. s \<in> gm x \<longrightarrow> eval_query.oracle_holds A s \<longrightarrow>
          t \<in> gm de \<longrightarrow> eval_query.oracle_holds B t \<longrightarrow>
          combine_collect \<G> (ci_dst ci) s t \<in> gm (ls_combine c A B ci x de))
     \<and> (\<forall>A s x q. s \<in> gm x \<longrightarrow> eval_query.oracle_holds A s \<longrightarrow>
          eval_holds q (ls_query c A x q) s)"
