theory CFG_Collect_Unified
  imports CFG_Collect_IP CFG_Collect_Core
begin

(*
  U1 (unified-analysis migration): one collecting locale parameterised by a
  combine_at hook.  The intra-procedural and interprocedural collecting
  semantics are recovered as interpretations:

    intra:  combine_at = (\<lambda>g rho v. {})        recovers cfg_collect
    ip:     combine_at = collect_combine_pp     recovers cfg_collect_ip

  The lfp skeleton (mono, unfold, post-fixpoint, entry, per-edge step, generic
  lfp lower bound) is proved ONCE in the locale.  The trace overlay (U4 / M3.5)
  reuses the same skeleton; see CFG_Collect_Trace.
*)

locale collecting =
  fixes combine_at :: "cfg \<Rightarrow> cenv \<Rightarrow> pp \<Rightarrow> store set"
  assumes combine_at_mono:
    "rho \<le> rho' \<Longrightarrow> combine_at g rho v \<subseteq> combine_at g rho' v"
begin

definition F :: "cfg \<Rightarrow> store set \<Rightarrow> cenv \<Rightarrow> cenv" where
  "F g S rho v =
     (if v = cfg_entry g then S else {})
     \<union> collect_pp g rho v
     \<union> combine_at g rho v"

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

(* -- Intra-procedural interpretation -------------------------------------- *)

interpretation intra: collecting "\<lambda>g rho v. {}"
  by unfold_locales simp

lemma intra_F_eq: "intra.F g S rho v = cfg_collect_F g S rho v"
  by (simp add: intra.F_def cfg_collect_F_def)

lemma intra_collect_eq: "intra.collect g S = cfg_collect g S"
proof -
  have "intra.F g S = cfg_collect_F g S"
    by (rule ext)+ (rule intra_F_eq)
  thus ?thesis by (simp add: intra.collect_def cfg_collect_def)
qed

(* -- Interprocedural interpretation --------------------------------------- *)

interpretation ip: collecting collect_combine_pp
  by unfold_locales (metis collect_combine_pp_mono monoD)

lemma ip_F_eq: "ip.F g S rho v = cfg_collect_ip_F g S rho v"
  by (simp add: ip.F_def cfg_collect_ip_F_def)

lemma ip_collect_eq: "ip.collect g S = cfg_collect_ip g S"
proof -
  have "ip.F g S = cfg_collect_ip_F g S"
    by (rule ext)+ (rule ip_F_eq)
  thus ?thesis by (simp add: ip.collect_def cfg_collect_ip_def)
qed

end
