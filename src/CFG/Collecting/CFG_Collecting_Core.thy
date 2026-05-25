theory CFG_Collecting_Core
  imports CFG_Edges_Collect
begin

(* cfg_edges_collect and path-to-lfp bridge lemmas (pre-compound). *)

(* Path-based collecting environment. *)
definition cfg_edges_collect :: "cfg => store set => pp => store set" where
  "cfg_edges_collect g S v =
     (\<Union>es\<in>{es. g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v}. edges_collect es S)"

(* One CFG step extends path-based collecting. *)
lemma cfg_edges_collect_step:
  assumes e: "(u, a, v) : edges g"
  shows "edge_collect a (cfg_edges_collect g S u) \<subseteq> cfg_edges_collect g S v"
proof
  fix x
  assume x: "x \<in> edge_collect a (cfg_edges_collect g S u)"
  then obtain es where es: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> u"
    and x: "x \<in> edge_collect a (edges_collect es S)"
    unfolding cfg_edges_collect_def
    by (smt (verit, ccfv_threshold) UN_iff edge_collect_member mem_Collect_eq)
  then obtain s where s: "s \<in> edges_collect es S"
    and x: "x \<in> edge_collect a {s}"
    using edge_collect_member by blast

  have p: "g \<turnstile> u \<longrightarrow>\<^bsub>[(a, v)]\<^esub> v"
    by (simp add: cfg_path.step e empty)
  have es': "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>(es @ [(a, v)])\<^esub> v"
    using es p by blast
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
proof -
  have entry: "(if v = cfg_entry g then S else {}) \<subseteq> cfg_edges_collect g S v"
    using cfg_edges_collect_entry by auto
  have step: "collect_pp g (cfg_edges_collect g S) v \<subseteq> cfg_edges_collect g S v"
    unfolding collect_pp_def using cfg_edges_collect_step by blast
  from entry step show ?thesis
    unfolding cfg_collect_F_def by blast
qed

 
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
