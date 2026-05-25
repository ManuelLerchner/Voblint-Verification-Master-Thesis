theory CFG_Collecting_Core
  imports CFG_Edges_Collect
begin

(* cfg_edges_collect and path-to-lfp bridge lemmas (pre-compound). *)

(* Path-based collecting environment. *)
definition cfg_edges_collect :: "cfg => store set => pp => store set" where
  "cfg_edges_collect g S v =
     (\<Union>es\<in>{es. cfg_path g (cfg_entry g) es v}. edges_collect es S)"

(* One CFG step extends path-based collecting. *)
lemma cfg_edges_collect_step:
  assumes e: "(u, a, v) : edges g"
  shows "edge_collect a (cfg_edges_collect g S u) \<subseteq> cfg_edges_collect g S v"
proof
  fix x
  assume x: "x \<in> edge_collect a (cfg_edges_collect g S u)"
  then obtain es where es: "cfg_path g (cfg_entry g) es u"
    and x: "x \<in> edge_collect a (edges_collect es S)"
    unfolding cfg_edges_collect_def
    by (smt (verit, ccfv_threshold) UN_iff edge_collect_member mem_Collect_eq)
  then obtain s where s: "s \<in> edges_collect es S"
    and x: "x \<in> edge_collect a {s}"
    using edge_collect_member by metis 

  have p: "cfg_path g u [(a, v)] v"
    by (rule cfg_path.step[OF e cfg_path.empty])
  have es': "cfg_path g (cfg_entry g) (es @ [(a, v)]) v"
    by (rule cfg_path_append[OF es p])
  have "x \<in> edges_collect (es @ [(a, v)]) S"
    using x s unfolding edges_collect_append edges_collect.simps
    using edge_collect_member by blast 
 
  then show "x \<in> cfg_edges_collect g S v"
    unfolding cfg_edges_collect_def using es' by auto
qed

lemma cfg_edges_collect_entry:
  "S \<subseteq> cfg_edges_collect g S (cfg_entry g)"
  unfolding cfg_edges_collect_def by(auto)
 
(*
  Post-fixpoint: cfg_edges_collect satisfies cfg_collect_F.
  Proof via edges_collect_append + cfg_path_append; one line per edge action.
*)
lemma cfg_edges_collect_post:
  "cfg_collect_F g S (cfg_edges_collect g S) v \<subseteq> cfg_edges_collect g S v"
  unfolding cfg_collect_F_def
  apply auto
  using cfg_edges_collect_entry apply blast
  using cfg_edges_collect_step collect_pp_def apply fastforce
  using cfg_edges_collect_step collect_pp_def by fastforce

 
lemma cfg_collect_le_edges_collect:
  "cfg_collect g S v \<subseteq> cfg_edges_collect g S v"
proof -
  have pf: "cfg_collect_F g S (cfg_edges_collect g S) \<le> cfg_edges_collect g S"
    unfolding le_fun_def using cfg_edges_collect_post by simp
  have "lfp (cfg_collect_F g S) \<le> cfg_edges_collect g S"
    using pf cfg_collect_F_mono lfp_lowerbound by blast
  then show ?thesis
    unfolding cfg_collect_def le_fun_def by simp
qed

end
