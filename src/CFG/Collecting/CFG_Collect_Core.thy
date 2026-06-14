theory CFG_Collect_Core
  imports CFG_Collect_Edges
begin

(* cfg_collect_paths and path-to-lfp bridge lemmas (pre-compound). *)

(* Path-based collecting environment. *)
definition cfg_collect_paths :: "cfg => store set => pp => store set" where
  "cfg_collect_paths g S v =
     (\<Union>es\<in>{es. g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v}. edges_collect es S)"

(* One CFG step extends path-based collecting. *)
lemma cfg_collect_paths_step:
  assumes e: "(u, a, v) : edges g"
  shows "edge_collect a (cfg_collect_paths g S u) \<subseteq> cfg_collect_paths g S v"
proof
  fix x
  assume x: "x \<in> edge_collect a (cfg_collect_paths g S u)"
  then obtain es where es: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> u"
    and x: "x \<in> edge_collect a (edges_collect es S)"
    unfolding cfg_collect_paths_def
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
 
  then show "x \<in> cfg_collect_paths g S v"
    unfolding cfg_collect_paths_def using es' by auto
qed

lemma cfg_collect_paths_entry:
  "S \<subseteq> cfg_collect_paths g S (cfg_entry g)"
  unfolding cfg_collect_paths_def by(auto)
 
(*
  Post-fixpoint: cfg_collect_paths satisfies cfg_collect_F.
  Proof via edges_collect_append + cfg_path_append; one line per edge action.
*)
lemma cfg_collect_paths_post:
  "cfg_collect_F g S (cfg_collect_paths g S) v \<subseteq> cfg_collect_paths g S v"
proof -
  have entry: "(if v = cfg_entry g then S else {}) \<subseteq> cfg_collect_paths g S v"
    using cfg_collect_paths_entry by auto
  have step: "collect_pp g (cfg_collect_paths g S) v \<subseteq> cfg_collect_paths g S v"
    unfolding collect_pp_def using cfg_collect_paths_step by blast
  from entry step show ?thesis
    unfolding cfg_collect_F_def by blast
qed


(* Soundness: The fixed-point collecting semantics (lfp) is a 
   sound over-approximation of the path-based semantics. 
   Every state inferred by the fixpoint is reachable via some path.
*)
theorem cfg_collect_le_paths:
  "cfg_collect g S v \<subseteq> cfg_collect_paths g S v"
proof -
  have pf: "cfg_collect_F g S (cfg_collect_paths g S) \<le> cfg_collect_paths g S"
    unfolding le_fun_def using cfg_collect_paths_post by simp
  have "lfp (cfg_collect_F g S) \<le> cfg_collect_paths g S"
    using pf cfg_collect_F_mono lfp_lowerbound by blast
  then show ?thesis
    unfolding cfg_collect_def le_fun_def by simp
qed


(*
 "cfg_collect g S v" never claims a state is reachable unless it truly is (Soundness),
  and if it finds a "suspect" state, there is an exact evidence trail (Witness) that leads to it.
*)
theorem cfg_collect_witness:
  assumes "s \<in> cfg_collect g S v"
  obtains es where "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v" and "s \<in> edges_collect es S"
proof -
  (* Use soundness theorem to move from LFP to Path-based set *)
  have "s \<in> cfg_collect_paths g S v"
    using assms cfg_collect_le_paths by blast
    
  have "s \<in> (\<Union>es\<in>{es. g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v}. edges_collect es S)"
    using `s \<in> cfg_collect_paths g S v` unfolding cfg_collect_paths_def by simp
    
  then obtain es where "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v" and "s \<in> edges_collect es S"
    by auto
    
  then show ?thesis using that by auto 
qed

end
