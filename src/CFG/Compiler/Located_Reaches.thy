theory Located_Reaches
  imports Control_Simulation
begin

lemma edge_step_mem_edge_collect:
  assumes "edge_step a s = Some t"
  shows "t \<in> edge_collect a {s}"
  using assms by (cases a) (auto split: if_splits)

lemma cfg_collect_edge_step:
  assumes edge: "(u, a, v) \<in> edges g"
      and step: "edge_step a s = Some t"
      and source: "s \<in> cfg_collect g S u"
  shows "t \<in> cfg_collect g S v"
proof (rule cfg_collect_edge[OF edge])
  have "t \<in> edge_collect a {s}"
    by (rule edge_step_mem_edge_collect[OF step])
  moreover have "{s} \<subseteq> cfg_collect g S u"
    using source by simp
  ultimately show "t \<in> edge_collect a (cfg_collect g S u)"
    using edge_collect_mono by blast
qed

fun stack_sound :: "cfg \<Rightarrow> store set \<Rightarrow> cframe list \<Rightarrow> bool" where
  "stack_sound g S [] = True"
| "stack_sound g S ((call, ret, s) # stk) =
     (s \<in> cfg_collect g S call \<and> stack_sound g S stk)"

definition located_sound :: "cfg \<Rightarrow> store set \<Rightarrow> cconf \<Rightarrow> bool" where
  "located_sound g S cf \<longleftrightarrow>
     (case cf of (v, s, stk) \<Rightarrow>
        s \<in> cfg_collect g S v \<and> stack_sound g S stk)"

lemma located_sound_entry:
  assumes "s \<in> S"
  shows "located_sound g S (cfg_entry g, s, [])"
  unfolding located_sound_def
  using assms cfg_collect_entry by auto

lemma cstep_preserves_located_sound:
  assumes "located_sound g S cf"
      and "cstep g cf cf'"
  shows "located_sound g S cf'"
proof -
  from assms(2) show ?thesis
  proof cases
    case Intra
    then show ?thesis
      using assms(1)
      unfolding located_sound_def
      by (auto intro: cfg_collect_edge_step)
  next
    case Call
    then show ?thesis
      using assms(1)
      unfolding located_sound_def
      by (auto intro: cfg_collect_edge_step)
  next
    case (ReturnNone call ex ret r t s stk)
    have src_mem: "s \<in> cfg_collect g S call"
      and ex_mem: "t \<in> cfg_collect g S ex"
      and tail_sound: "stack_sound g S stk"
      using assms(1) ReturnNone unfolding located_sound_def by auto
    have combine_mem:
        "IMP2_Globals.combine_states s t \<in> combine_collect None r s t"
      unfolding combine_collect_def by simp
    have combine: "(call, ex, ret, None, r) \<in> combines g"
      using ReturnNone by simp
    have ret_mem:
        "IMP2_Globals.combine_states s t \<in> cfg_collect g S ret"
      by (rule cfg_collect_combine[OF combine refl src_mem ex_mem combine_mem])
    show ?thesis
      using ReturnNone tail_sound ret_mem
      unfolding located_sound_def by auto
  next
    case (ReturnSome call ex ret x e t s stk)
    have src_mem: "s \<in> cfg_collect g S call"
      and ex_mem: "t \<in> cfg_collect g S ex"
      and tail_sound: "stack_sound g S stk"
      using assms(1) ReturnSome unfolding located_sound_def by auto
    have combine_mem:
        "(IMP2_Globals.combine_states s t)(x := IMP2_Expr.aval e t)
          \<in> combine_collect (Some x) (Some e) s t"
      unfolding combine_collect_def by simp
    have combine: "(call, ex, ret, Some x, Some e) \<in> combines g"
      using ReturnSome by simp
    have ret_mem:
        "(IMP2_Globals.combine_states s t)(x := IMP2_Expr.aval e t)
          \<in> cfg_collect g S ret"
      by (rule cfg_collect_combine[OF combine refl src_mem ex_mem combine_mem])
    show ?thesis
      using ReturnSome tail_sound ret_mem
      unfolding located_sound_def by auto
  qed
qed

lemma csteps_preserve_located_sound:
  assumes "located_sound g S cf"
      and "star (cstep g) cf cf'"
  shows "located_sound g S cf'"
proof -
  from assms(2) assms(1) show ?thesis
  proof (induction rule: star.induct)
    case (refl a)
    then show ?case .
  next
    case (step a b c)
    have "located_sound g S b"
      by (rule cstep_preserves_located_sound[OF step.prems step.hyps(1)])
    then show ?case
      by (rule step.IH)
  qed
qed

lemma cstep_imp_cfg_reaches:
  assumes "cstep g cf cf'"
  shows "cfg_reaches g (fst cf) (fst cf')"
  using assms
proof cases
  case Intra
  then show ?thesis
    by (auto intro: cfg_reaches_edge)
next
  case Call
  then show ?thesis
    by (auto intro: cfg_reaches_edge)
next
  case (ReturnNone call ex ret r t s stk)
  have combine: "(call, ex, ret, None, r) \<in> combines g"
    using ReturnNone by simp
  have reach_ct:
      "cfg_reaches g (combine_exit_node (call, ex, ret, None, r))
         (combine_return_node (call, ex, ret, None, r))"
    using combine by (rule cfg_reaches_combine_exit)
  have reach: "cfg_reaches g ex ret"
    using reach_ct by (simp add: combine_exit_node_def combine_return_node_def)
  then show ?thesis
    using ReturnNone by simp
next
  case (ReturnSome call ex ret x e t s stk)
  have combine: "(call, ex, ret, Some x, Some e) \<in> combines g"
    using ReturnSome by simp
  have reach_ct:
      "cfg_reaches g (combine_exit_node (call, ex, ret, Some x, Some e))
         (combine_return_node (call, ex, ret, Some x, Some e))"
    using combine by (rule cfg_reaches_combine_exit)
  have reach: "cfg_reaches g ex ret"
    using reach_ct by (simp add: combine_exit_node_def combine_return_node_def)
  then show ?thesis
    using ReturnSome by simp
qed

lemma csteps_imp_cfg_reaches:
  assumes "star (cstep g) cf cf'"
  shows "cfg_reaches g (fst cf) (fst cf')"
  using assms
proof (induction rule: star.induct)
  case (refl cf)
  show ?case
    by (rule cfg_reaches_refl)
next
  case (step cf mid dst)
  have first: "cfg_reaches g (fst cf) (fst mid)"
    by (rule cstep_imp_cfg_reaches[OF step.hyps(1)])
  show ?case
    using first step.IH by (rule cfg_reaches_trans)
qed

subsection \<open>Arbitrary-query pruning\<close>

lemma cfg_collect_prune_to_query:
  "cfg_collect g S v \<subseteq> cfg_collect (prune_to g v) S v"
proof
  fix t
  assume "t \<in> cfg_collect g S v"
  then have witness: "cfg_witness g S v t"
    by (simp add: cfg_collect_eq_paths cfg_collect_paths_def)
  have "cfg_witness (prune_to g v) S v t"
    using cfg_witness_prune_to[OF witness] cfg_reaches_refl by blast
  then show "t \<in> cfg_collect (prune_to g v) S v"
    by (simp add: cfg_collect_eq_paths cfg_collect_paths_def)
qed

end
