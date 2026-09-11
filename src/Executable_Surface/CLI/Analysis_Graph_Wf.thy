theory Analysis_Graph_Wf
  imports Analysis_Graph_Build
begin

section \<open>Every built graph is well-formed\<close>

text \<open>
  A renderer outside Isabelle reads an exported graph and trusts its shape:
  that no node is listed twice, and that an edge never names an endpoint the
  node list does not contain. This theory is where that trust is earned ---
  \<^const>\<open>analysis_graph_wf\<close> holds of \<^const>\<open>build_analysis_graph\<close> for every
  configuration, CFG and solution, so no caller has to check it and no
  consumer has to handle the malformed case.

  Nodes are drawn from \<^const>\<open>remdups\<close> of the solved domain, so they are
  distinct, and the three node constructors keep the groups apart. Every emitted
  edge is guarded on both endpoints being covered keys, so it names only nodes in
  that list. Distinctness of the edges is the one part that is not free: a
  rendered edge records the call action's destination variable but not its
  formals or arguments, so two call edges out of one call site could collapse
  onto the same edge. \<open>calls_source_unique\<close> rules that out, and it is what
  \<^const>\<open>compile_prog\<close> already guarantees.
\<close>


text \<open>A compiled program satisfies the side condition outright: the compiler allocates
  each call at its own freshly claimed statement index.\<close>

lemma calls_source_unique_compile_prog:
  "calls_source_unique (compile_prog \<Pi> ps)"
  unfolding calls_source_unique_def
  using compile_prog_calls_source_unique by blast

lemma in_set_map_filter_conv:
  "y \<in> set (List.map_filter f xs) \<longleftrightarrow> (\<exists>x\<in>set xs. f x = Some y)"
  by (induction xs) (auto split: option.splits)

lemma distinct_map_filterI [intro]:
  assumes dist: "distinct xs"
      and uniq: "\<And>x1 x2 y. x1 \<in> set xs \<Longrightarrow> x2 \<in> set xs
                    \<Longrightarrow> f x1 = Some y \<Longrightarrow> f x2 = Some y \<Longrightarrow> x1 = x2"
  shows "distinct (List.map_filter f xs)"
  unfolding List.map_filter_def distinct_map
proof (intro conjI)
  show "distinct (filter (\<lambda>x. f x \<noteq> None) xs)" using dist by simp
next
  show "inj_on (the \<circ> f) (set (filter (\<lambda>x. f x \<noteq> None) xs))"
  proof (rule inj_onI)
    fix x1 x2
    assume m: "x1 \<in> set (filter (\<lambda>x. f x \<noteq> None) xs)"
              "x2 \<in> set (filter (\<lambda>x. f x \<noteq> None) xs)"
       and eq: "(the \<circ> f) x1 = (the \<circ> f) x2"
    from m have "f x1 = Some (the (f x1))" and "f x2 = Some (the (f x2))" by auto
    with eq show "x1 = x2" using uniq m by auto
  qed
qed

lemma distinct_cfg_intra_list [simp]: "distinct (cfg_intra_list g)"
  unfolding cfg_intra_list_code by (rule distinct_sorted_list_of_set)

lemma distinct_cfg_calls_list [simp]: "distinct (cfg_calls_list g)"
  unfolding cfg_calls_list_code by (rule distinct_sorted_list_of_set)

text \<open>One call site carries one call edge, so a rendered edge that mentions only part of
  the call action still determines the tuple it came from.\<close>

lemma calls_source_uniqueD [dest]:
  assumes uniq: "calls_source_unique g" and fin: "finite (calls g)"
      and m1: "y1 \<in> set (cfg_calls_list g)" and m2: "y2 \<in> set (cfg_calls_list g)"
      and src: "fst y1 = fst y2"
  shows "y1 = y2"
proof -
  obtain ca1 ce1 af1 where y1: "y1 = (fst y1, ca1, ce1, af1)" by (cases y1) auto
  obtain ca2 ce2 af2 where y2: "y2 = (fst y2, ca2, ce2, af2)" by (cases y2) auto
  have "(fst y1, ca1, ce1, af1) \<in> calls g" using m1 fin y1 by simp
  moreover have "(fst y1, ca2, ce2, af2) \<in> calls g" using m2 fin y2 src by simp
  ultimately have "ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
    using uniq unfolding calls_source_unique_def by blast
  then show ?thesis using y1 y2 src by simp
qed

lemma distinct_analysis_intra_edges:
  assumes cov: "distinct covered"
  shows "distinct (analysis_intra_edges g covered)"
  unfolding analysis_intra_edges_def
  by (rule distinct_map_filterI)
     (use cov in \<open>auto simp: List.distinct_product split: if_splits prod.splits\<close>)

lemma distinct_analysis_enter_edges:
  assumes cov: "distinct covered" and uniq: "calls_source_unique g" and fin: "finite (calls g)"
  shows "distinct (analysis_enter_edges cfg g covered sol)"
  unfolding analysis_enter_edges_def
  by (rule distinct_map_filterI)
     (use cov calls_source_uniqueD[OF uniq fin] in
        \<open>auto simp: List.distinct_product split: if_splits prod.splits option.splits\<close>)

lemma distinct_analysis_combine_edges:
  assumes cov: "distinct covered" and uniq: "calls_source_unique g" and fin: "finite (calls g)"
  shows "distinct (analysis_combine_edges cfg g covered sol)"
  unfolding analysis_combine_edges_def
  by (rule distinct_map_filterI)
     (use cov calls_source_uniqueD[OF uniq fin] in
        \<open>auto simp: List.distinct_product
              split: if_splits prod.splits option.splits cfg_node.splits\<close>)

lemma distinct_analysis_call_to_return_edges:
  assumes cov: "distinct covered" and uniq: "calls_source_unique g" and fin: "finite (calls g)"
  shows "distinct (analysis_call_to_return_edges cfg g covered)"
  unfolding analysis_call_to_return_edges_def
  by (rule distinct_map_filterI)
     (use cov calls_source_uniqueD[OF uniq fin] in
        \<open>auto simp: List.distinct_product
              split: if_splits prod.splits cfg_node.splits\<close>)

text \<open>Both endpoints of every emitted edge are covered keys, and each group carries its
  own edge-kind constructor, so the groups cannot collide with one another.\<close>

lemma analysis_intra_edges_local:
  "e \<in> set (analysis_intra_edges g covered)
     \<Longrightarrow> fst e \<in> set (covered_local_nodes covered)
       \<and> snd (snd e) \<in> set (covered_local_nodes covered)"
  unfolding analysis_intra_edges_def covered_local_nodes_def in_set_map_filter_conv
  by (force simp: prod.case_eq_if split: if_splits)

lemma analysis_enter_edges_local:
  "e \<in> set (analysis_enter_edges cfg g covered sol)
     \<Longrightarrow> fst e \<in> set (covered_local_nodes covered)
       \<and> snd (snd e) \<in> set (covered_local_nodes covered)"
  unfolding analysis_enter_edges_def covered_local_nodes_def in_set_map_filter_conv
  by (force simp: prod.case_eq_if split: if_splits option.splits)

lemma analysis_combine_edges_local:
  "e \<in> set (analysis_combine_edges cfg g covered sol)
     \<Longrightarrow> fst e \<in> set (covered_local_nodes covered)
       \<and> snd (snd e) \<in> set (covered_local_nodes covered)"
  unfolding analysis_combine_edges_def covered_local_nodes_def in_set_map_filter_conv
  by (force simp: prod.case_eq_if split: if_splits option.splits cfg_node.splits)

lemma analysis_call_to_return_edges_local:
  "e \<in> set (analysis_call_to_return_edges cfg g covered)
     \<Longrightarrow> fst e \<in> set (covered_local_nodes covered)
       \<and> snd (snd e) \<in> set (covered_local_nodes covered)"
  unfolding analysis_call_to_return_edges_def covered_local_nodes_def in_set_map_filter_conv
  by (force simp: prod.case_eq_if split: if_splits cfg_node.splits)

lemma analysis_intra_edges_kind:
  "e \<in> set (analysis_intra_edges g covered) \<Longrightarrow> \<exists>a. fst (snd e) = IntraEdge a"
  unfolding analysis_intra_edges_def in_set_map_filter_conv
  by (force simp: prod.case_eq_if split: if_splits)

lemma analysis_enter_edges_kind:
  "e \<in> set (analysis_enter_edges cfg g covered sol)
     \<Longrightarrow> \<exists>p ca. fst (snd e) = EnterEdge p ca"
  unfolding analysis_enter_edges_def in_set_map_filter_conv
  by (force simp: prod.case_eq_if split: if_splits option.splits)

lemma analysis_combine_edges_kind:
  "e \<in> set (analysis_combine_edges cfg g covered sol)
     \<Longrightarrow> \<exists>call dst ret. fst (snd e) = CombineEdge call dst ret"
  unfolding analysis_combine_edges_def in_set_map_filter_conv
  by (force simp: prod.case_eq_if split: if_splits option.splits cfg_node.splits)

lemma analysis_call_to_return_edges_kind:
  "e \<in> set (analysis_call_to_return_edges cfg g covered)
     \<Longrightarrow> \<exists>p. fst (snd e) = CallToReturnEdge p"
  unfolding analysis_call_to_return_edges_def in_set_map_filter_conv
  by (force simp: prod.case_eq_if split: if_splits cfg_node.splits)

lemma set_analysis_local_domain [simp]:
  "pc \<in> set (analysis_local_domain dl) \<longleftrightarrow> Inl pc \<in> set dl"
  by (induction dl rule: analysis_local_domain.induct) auto

lemma distinct_analysis_local_domain:
  "distinct dl \<Longrightarrow> distinct (analysis_local_domain dl)"
  by (induction dl rule: analysis_local_domain.induct) auto

lemma set_analysis_global_domain [simp]:
  "k \<in> set (analysis_global_domain dl) \<longleftrightarrow> Inr k \<in> set dl"
  by (induction dl rule: analysis_global_domain.induct) auto

lemma distinct_analysis_global_domain:
  "distinct dl \<Longrightarrow> distinct (analysis_global_domain dl)"
  by (induction dl rule: analysis_global_domain.induct) auto

lemma distinct_covered_local_nodes:
  "distinct covered \<Longrightarrow> distinct (covered_local_nodes covered)"
  unfolding covered_local_nodes_def
  by (simp add: distinct_map inj_on_def prod_eq_iff)

theorem build_analysis_graph_wf:
  assumes uniq: "calls_source_unique g" and fin: "finite (calls g)"
  shows "analysis_graph_wf (build_analysis_graph cfg g domain sol)"
proof -
  let ?covered = "analysis_local_domain (remdups domain)"
  let ?keys = "analysis_global_domain (remdups domain)"
  let ?locals = "covered_local_nodes ?covered"
  let ?globals = "analysis_global_nodes cfg sol ?keys"
  let ?ns = "?locals @ ?globals @ analysis_source_nodes cfg"
  let ?es = "analysis_intra_edges g ?covered
             @ analysis_enter_edges cfg g ?covered sol
             @ analysis_combine_edges cfg g ?covered sol
             @ analysis_call_to_return_edges cfg g ?covered"
  have cov: "distinct ?covered" by (rule distinct_analysis_local_domain) simp
  have kys: "distinct ?keys" by (rule distinct_analysis_global_domain) simp
  have dl: "distinct ?locals" by (rule distinct_covered_local_nodes[OF cov])
  have dg: "distinct ?globals"
    using kys unfolding analysis_global_nodes_def by (simp add: distinct_map inj_on_def)
  have dns: "distinct ?ns"
    using dl dg
    unfolding covered_local_nodes_def analysis_global_nodes_def analysis_source_nodes_def
    by (auto split: option.splits)
  have dcl: "distinct (analysis_context_clusters cfg ?covered
                        @ analysis_global_cluster ?ns @ analysis_source_cluster ?ns)"
    unfolding analysis_context_clusters_def analysis_global_cluster_def
              analysis_source_cluster_def
    by auto
  have des: "distinct ?es"
    using distinct_analysis_intra_edges[OF cov]
          distinct_analysis_enter_edges[OF cov uniq fin]
          distinct_analysis_combine_edges[OF cov uniq fin]
          distinct_analysis_call_to_return_edges[OF cov uniq fin]
    by (auto dest!: analysis_intra_edges_kind analysis_enter_edges_kind
                    analysis_combine_edges_kind analysis_call_to_return_edges_kind)
  have ends: "list_all (\<lambda>e. case e of (src, _, dst) \<Rightarrow> src \<in> set ?ns \<and> dst \<in> set ?ns) ?es"
    by (auto simp: list_all_iff prod.case_eq_if
             dest!: analysis_intra_edges_local analysis_enter_edges_local
                    analysis_combine_edges_local analysis_call_to_return_edges_local)
  show ?thesis
    unfolding analysis_graph_wf_def build_analysis_graph_def
              build_analysis_graph_parts_def Let_def
    using dns dcl des ends by simp
qed

end
