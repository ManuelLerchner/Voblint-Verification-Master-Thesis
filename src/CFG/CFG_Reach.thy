theory CFG_Reach
  imports
    CFG_Path
    "Timed_Automata.Graphs"
begin

(*
  CFG_Reach -- Reachability adjunct for CFGs.

  Projects the labelled CFG edge set down to a relation
    cfg_step :: pp => pp => bool
  (forget labels) and interprets Graph_Defs on it.  This gives us reaches,
  reaches1, reaches_trans, steps, and the associated induction principles
  for free.  See ~/git/goblint-formalization-kb/wiki/research/graph-library-evaluation.md
  for the rationale.

  cfg_reach.reaches g u v  iff  (EX es. cfg_path g u es v)   (cfg_reach_iff_cfg_path)

  Note: this file does NOT discharge td_cfg_in_reach (the TD-solver-internal
  reach claim in Pipeline.thy); that lives in the solver layer, not the CFG layer.
*)

definition cfg_step :: "cfg \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> bool" where
  "cfg_step g u v \<longleftrightarrow> (\<exists>a. (u, a, v) \<in> edges g)"

interpretation cfg_reach: Graph_Defs "cfg_step g" for g .

lemma cfg_step_iff_edge:
  "cfg_step g u v \<longleftrightarrow> (\<exists>a. (u, a, v) \<in> edges g)"
  unfolding cfg_step_def by simp

lemma cfg_path_imp_reaches:
  "cfg_path g u es v \<Longrightarrow> cfg_reach.reaches g u v"
proof (induction rule: cfg_path.induct)
  case (empty g v)
  show ?case by simp
next
  case (step u a w g es v)
  have "cfg_step g u w" using step.hyps(1) unfolding cfg_step_def by blast
  with step.IH show ?case
    by (meson rtranclp.rtrancl_into_rtrancl rtranclp_trans converse_rtranclp_into_rtranclp)
qed

lemma reaches_imp_cfg_path:
  "cfg_reach.reaches g u v \<Longrightarrow> \<exists>es. cfg_path g u es v"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  show ?case using cfg_path.empty by blast
next
  case (rtrancl_into_rtrancl a b c)
  from rtrancl_into_rtrancl.IH obtain es where p: "cfg_path g a es b" by blast
  from rtrancl_into_rtrancl.hyps(2) obtain act where e: "(b, act, c) \<in> edges g"
    unfolding cfg_step_def by blast
  have step_path: "cfg_path g b [(act, c)] c"
    by (rule cfg_path.step[OF e cfg_path.empty])
  show ?case
    using cfg_path_append[OF p step_path] by blast
qed

theorem cfg_reach_iff_cfg_path:
  "cfg_reach.reaches g u v \<longleftrightarrow> (\<exists>es. cfg_path g u es v)"
  using cfg_path_imp_reaches reaches_imp_cfg_path by blast

(* Notation alignment: cfg_reaches in CFG_Path uses the same existential. *)
lemma cfg_reaches_iff_reach:
  "g \<turnstile> u \<rightarrow>* v \<longleftrightarrow> cfg_reach.reaches g u v"
  using cfg_reach_iff_cfg_path by simp

end
