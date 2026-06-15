theory CFG_Collect_Core
  imports CFG_Collect_Edges
begin

section \<open>Path-based collecting\<close>

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
 
end
