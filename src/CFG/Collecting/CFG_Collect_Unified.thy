theory CFG_Collect_Unified
  imports CFG_Collect
begin

section \<open>Unified collecting locale\<close>

text \<open>
  One collecting locale parameterised by a combine_at hook.  The collecting
  semantics is recovered as an interpretation:

    cfg:  combine_at = collect_combine_pp     recovers cfg_collect

  The lfp skeleton (mono, unfold, post-fixpoint, entry, per-edge step, generic
  lfp lower bound) is proved ONCE in the locale.  The trace overlay reuses the
  same skeleton; see CFG_Collect_Trace.
\<close>

locale collecting =
  fixes combine_at :: "cfg \<Rightarrow> cenv \<Rightarrow> pp \<Rightarrow> store set"
  assumes combine_at_mono:
    "\<rho> \<le> rho' \<Longrightarrow> combine_at g \<rho> v \<subseteq> combine_at g rho' v"
begin

definition F :: "cfg \<Rightarrow> store set \<Rightarrow> cenv \<Rightarrow> cenv" where
  "F g S \<rho> v =
     (if v = cfg_entry g then S else {})
     \<union> collect_pp g \<rho> v
     \<union> combine_at g \<rho> v"

definition collect :: "cfg \<Rightarrow> store set \<Rightarrow> cenv" where
  "collect g S = lfp (F g S)"

lemma F_mono: "mono (F g S)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  show "F g S rho1 \<le> F g S rho2"
  proof (rule le_funI)
    fix v
    show "F g S rho1 v \<subseteq> F g S rho2 v"
      unfolding F_def
      using monoD[OF collect_pp_mono[of g v] le] combine_at_mono[OF le]
      by (auto dest: subsetD)
  qed
qed

lemma collect_unfold: "collect g S = F g S (collect g S)"
  unfolding collect_def by (simp add: F_mono def_lfp_unfold)

lemma collect_post: "F g S (collect g S) v \<subseteq> collect g S v"
proof -
  have "collect g S v = F g S (collect g S) v" by (metis collect_unfold)
  thus ?thesis by simp
qed

lemma collect_entry: "S \<subseteq> collect g S (cfg_entry g)"
proof -
  have "S \<subseteq> F g S (collect g S) (cfg_entry g)"
    unfolding F_def by auto
  thus ?thesis using collect_post[of g S "cfg_entry g"] by blast
qed

lemma collect_lowerbound: "F g S W \<le> W \<Longrightarrow> collect g S \<le> W"
  unfolding collect_def using F_mono lfp_lowerbound by blast

lemma collect_step:
  assumes e: "(u, a, v) \<in> edges g"
  shows "edge_collect a (collect g S u) \<subseteq> collect g S v"
proof -
  have "edge_collect a (collect g S u) \<subseteq> collect_pp g (collect g S) v"
    unfolding collect_pp_def using e by auto
  also have "\<dots> \<subseteq> F g S (collect g S) v" unfolding F_def by auto
  also have "\<dots> \<subseteq> collect g S v" using collect_post by simp
  finally show ?thesis .
qed

end

subsection \<open>Interprocedural interpretation\<close>

interpretation cfg: collecting collect_combine_pp
  by unfold_locales (metis collect_combine_pp_mono monoD)

lemma cfg_F_eq: "cfg.F g S \<rho> v = cfg_collect_F g S \<rho> v"
  by (simp add: cfg.F_def cfg_collect_F_def)

lemma cfg_collect_eq: "cfg.collect g S = cfg_collect g S"
proof -
  have "cfg.F g S = cfg_collect_F g S"
    by (rule ext)+ (rule cfg_F_eq)
  thus ?thesis by (simp add: cfg.collect_def cfg_collect_def)
qed

end
