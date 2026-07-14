theory Exec_Ivl_Cmp_Shared
  imports Exec_Ivl_Run Voblint_Analysis.Exec_Bridge Exec_Ivl_Cmp_Seed_Sound
    Voblint_Analysis.Seed_EnterMono_Lift
begin

section \<open>Shared executable support for the interval seeded-clean cone\<close>

definition ivl_etf_clean_st :: "(unit, ivl st) effectful_st_transfer" where
  "ivl_etf_clean_st = \<lparr>
    etf_st_nop        = clean_edge_tree_st (ivl_tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. clean_edge_tree_st (ivl_tf_st (EA_Assign x e))),
    etf_st_assume     = (\<lambda>b. clean_edge_tree_st (ivl_tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. clean_edge_tree_st (ivl_tf_st (EA_AssumeNot b))),
    etf_st_enter      = clean_edge_tree_st (ivl_tf_st EA_Enter),
    etf_st_combine    = unit_combine_tree_st
  \<rparr>"

definition ivl_ec :: "ivl st \<Rightarrow> ivl st \<Rightarrow> ivl st" where
  "ivl_ec ctx sc = restrict_global_st sc"

definition ivl_combine_rread ::
  "pp \<Rightarrow> pp \<Rightarrow> ivl st \<Rightarrow> (pp \<times> ivl st, ivl st, ivl st) strategy_tree"
where
  "ivl_combine_rread cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG ctx (\<lambda>g.
       let callee = ivl_ec ctx sc in
       Side callee (restrict_global_st sc)
         (QueryL (ex, callee) (\<lambda>se.
           let res = restrict_local_st sc \<squnion> restrict_global_st (se \<squnion> g) in
           Side ctx (restrict_global_st res)
             (Answer (restrict_local_st res))))))"

subsection \<open>Point-digest support for interval routing\<close>

definition ivl_of_int :: "Int.int \<Rightarrow> ivl" where
  "ivl_of_int n = Ivl (Fin n) (Fin n)"

definition point_ivl :: "ivl \<Rightarrow> bool" where
  "point_ivl a = (\<exists>k. a = Ivl (Fin k) (Fin k))"

lemma point_ivl_gamma_exact:
  assumes "point_ivl a" and "v \<in> gamma_ivl a"
  shows "ivl_of_int v = a"
  using assms unfolding point_ivl_def ivl_of_int_def by auto

lemma non_point_ivl_splits:
  "0 \<in> gamma_ivl (Ivl (Fin 0) (Fin 10)) \<and> 10 \<in> gamma_ivl (Ivl (Fin 0) (Fin 10))
   \<and> ivl_of_int 0 \<noteq> ivl_of_int 10 \<and> \<not> point_ivl (Ivl (Fin 0) (Fin 10))"
  by (simp add: point_ivl_def ivl_of_int_def)

interpretation ivl_pd: point_digest ivl_of_int point_ivl
  by unfold_locales (simp add: point_ivl_gamma_exact)

end
