theory CFG_Exit_Reachable
  imports CFG_Compound_Paths
begin

(*
  Every node of a compiled fragment edge-reaches the fragment exit.

  Discharges the intraprocedural well-formedness condition the exit-rooted
  single-solve assumes (EXIT_ROOTED_SOLVE_MIGRATION.md, Step 1): in the paper
  every program point formally reaches the return/exit node.  Proved here by
  structural induction over `compile`.
*)

definition frag_node ::
  "pp \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action \<times> pp) set \<Rightarrow> pp \<Rightarrow> bool" where
  "frag_node en ex E v \<longleftrightarrow>
     v = en \<or> v = ex \<or> (\<exists>a w. (v, a, w) \<in> E) \<or> (\<exists>u a. (u, a, v) \<in> E)"

lemma frag_node_src: "(v, a, w) \<in> E \<Longrightarrow> frag_node en ex E v"
  by (auto simp: frag_node_def)

lemma frag_node_dst: "(u, a, v) \<in> E \<Longrightarrow> frag_node en ex E v"
  by (auto simp: frag_node_def)

lemma frag_node_en: "frag_node en ex E en"
  by (simp add: frag_node_def)

lemma frag_node_ex: "frag_node en ex E ex"
  by (simp add: frag_node_def)

(* A single edge of the target edge set is a one-step path. *)
lemma mk_cfg_edge_path:
  "(u, a, w) \<in> E \<Longrightarrow> mk_cfg en ex E \<turnstile> u \<longrightarrow>\<^bsub>[(a, w)]\<^esub> w"
  by (auto intro: cfg_path.step cfg_path.empty)

lemma compile_frag_node_reach_exit:
  "compile c n = (n', en, ex, E) \<Longrightarrow> frag_node en ex E v
     \<Longrightarrow> \<exists>es. mk_cfg en ex E \<turnstile> v \<longrightarrow>\<^bsub>es\<^esub> ex"
proof (induction c arbitrary: n n' en ex E v)
  case SKIP
  then have e: "en = n" "ex = n + 1" "E = {(n, EA_Nop, n + 1)}"
    by auto
  from SKIP(2) have "v = n \<or> v = n + 1"
    using e by (auto simp: frag_node_def)
  then show ?case
  proof
    assume "v = n"
    then show ?thesis using e mk_cfg_edge_path[of n EA_Nop "n + 1" E en ex] by auto
  next
    assume "v = n + 1"
    then show ?thesis using e by (auto intro: cfg_path.empty)
  qed
next
  case (Assign x a)
  then have e: "en = n" "ex = n + 1" "E = {(n, EA_Assign x a, n + 1)}"
    by auto
  from Assign(2) have "v = n \<or> v = n + 1"
    using e by (auto simp: frag_node_def)
  then show ?case
  proof
    assume "v = n"
    then show ?thesis
      using e mk_cfg_edge_path[of n "EA_Assign x a" "n + 1" E en ex] by auto
  next
    assume "v = n + 1"
    then show ?thesis using e by (auto intro: cfg_path.empty)
  qed
next
  case (Seq c1 c2)
  obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
        c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and en: "en = en1" and ex: "ex = ex2"
    and Edef: "E = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    using Seq.prems(1) by (auto split: prod.splits)
  define g where "g = mk_cfg en ex E"
  have eg: "edges g = E" by (simp add: g_def)
  have subE1: "E1 \<subseteq> E" and subE2: "E2 \<subseteq> E"
    and brE: "(ex1, EA_Nop, en2) \<in> E" using Edef by auto
  have B: "\<And>w. frag_node en2 ex2 E2 w \<Longrightarrow> \<exists>es. g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> ex"
  proof -
    fix w assume "frag_node en2 ex2 E2 w"
    from Seq.IH(2)[OF c2 this] obtain es2 where
      p2: "mk_cfg en2 ex2 E2 \<turnstile> w \<longrightarrow>\<^bsub>es2\<^esub> ex2" by blast
    have s2: "edges (mk_cfg en2 ex2 E2) \<subseteq> edges g" using subE2 eg by simp
    have "g \<turnstile> w \<longrightarrow>\<^bsub>es2\<^esub> ex2" using cfg_path_mono_edges[OF p2 s2] .
    then show "\<exists>es. g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> ex" using ex by auto
  qed
  have A: "\<And>w. frag_node en1 ex1 E1 w \<Longrightarrow> \<exists>es. g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> ex"
  proof -
    fix w assume "frag_node en1 ex1 E1 w"
    from Seq.IH(1)[OF c1 this] obtain es1 where
      p1: "mk_cfg en1 ex1 E1 \<turnstile> w \<longrightarrow>\<^bsub>es1\<^esub> ex1" by blast
    have s1: "edges (mk_cfg en1 ex1 E1) \<subseteq> edges g" using subE1 eg by simp
    have g1: "g \<turnstile> w \<longrightarrow>\<^bsub>es1\<^esub> ex1" using cfg_path_mono_edges[OF p1 s1] .
    have gb: "g \<turnstile> ex1 \<longrightarrow>\<^bsub>[(EA_Nop, en2)]\<^esub> en2"
      unfolding g_def by (rule mk_cfg_edge_path[OF brE])
    from B[OF frag_node_en] obtain es2 where
      g2: "g \<turnstile> en2 \<longrightarrow>\<^bsub>es2\<^esub> ex" by blast
    from cfg_path_append[OF cfg_path_append[OF g1 gb] g2]
    show "\<exists>es. g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> ex" by blast
  qed
  have cls: "frag_node en1 ex1 E1 v \<or> frag_node en2 ex2 E2 v \<or> v = ex"
    using Seq.prems(2) Edef en ex by (auto simp: frag_node_def)
  show ?case unfolding g_def[symmetric]
    using cls A B by (auto intro: cfg_path.empty simp: ex)
next
  case (If b c1 c2)
  obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
        c1: "compile c1 (n + 1) = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and en: "en = n" and ex: "ex = n2"
    and Edef: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
                   \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    using If.prems(1) by (auto split: prod.splits)
  define g where "g = mk_cfg en ex E"
  have eg: "edges g = E" by (simp add: g_def)
  have subE1: "E1 \<subseteq> E" and subE2: "E2 \<subseteq> E" using Edef by auto
  have ea: "(n, EA_Assume b, en1) \<in> E" and t1: "(ex1, EA_Nop, n2) \<in> E"
    and t2: "(ex2, EA_Nop, n2) \<in> E" using Edef by auto
  have A1: "\<And>w. frag_node en1 ex1 E1 w \<Longrightarrow> \<exists>es. g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> ex"
  proof -
    fix w assume "frag_node en1 ex1 E1 w"
    from If.IH(1)[OF c1 this] obtain es1 where
      p1: "mk_cfg en1 ex1 E1 \<turnstile> w \<longrightarrow>\<^bsub>es1\<^esub> ex1" by blast
    have "edges (mk_cfg en1 ex1 E1) \<subseteq> edges g" using subE1 eg by simp
    from cfg_path_mono_edges[OF p1 this] have g1: "g \<turnstile> w \<longrightarrow>\<^bsub>es1\<^esub> ex1" .
    have "g \<turnstile> ex1 \<longrightarrow>\<^bsub>[(EA_Nop, n2)]\<^esub> n2"
      unfolding g_def by (rule mk_cfg_edge_path[OF t1])
    from cfg_path_append[OF g1 this] show "\<exists>es. g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> ex" using ex by auto
  qed
  have A2: "\<And>w. frag_node en2 ex2 E2 w \<Longrightarrow> \<exists>es. g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> ex"
  proof -
    fix w assume "frag_node en2 ex2 E2 w"
    from If.IH(2)[OF c2 this] obtain es2 where
      p2: "mk_cfg en2 ex2 E2 \<turnstile> w \<longrightarrow>\<^bsub>es2\<^esub> ex2" by blast
    have "edges (mk_cfg en2 ex2 E2) \<subseteq> edges g" using subE2 eg by simp
    from cfg_path_mono_edges[OF p2 this] have g2: "g \<turnstile> w \<longrightarrow>\<^bsub>es2\<^esub> ex2" .
    have "g \<turnstile> ex2 \<longrightarrow>\<^bsub>[(EA_Nop, n2)]\<^esub> n2"
      unfolding g_def by (rule mk_cfg_edge_path[OF t2])
    from cfg_path_append[OF g2 this] show "\<exists>es. g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> ex" using ex by auto
  qed
  have entry: "\<exists>es. g \<turnstile> n \<longrightarrow>\<^bsub>es\<^esub> ex"
  proof -
    have e1: "g \<turnstile> n \<longrightarrow>\<^bsub>[(EA_Assume b, en1)]\<^esub> en1"
      unfolding g_def by (rule mk_cfg_edge_path[OF ea])
    from A1[OF frag_node_en] obtain es1 where "g \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex" by blast
    from cfg_path_append[OF e1 this] show ?thesis by blast
  qed
  have cls: "v = n \<or> frag_node en1 ex1 E1 v \<or> frag_node en2 ex2 E2 v \<or> v = ex"
    using If.prems(2) Edef en ex by (auto simp: frag_node_def)
  show ?case unfolding g_def[symmetric]
  proof -
    from cls show "\<exists>es. g \<turnstile> v \<longrightarrow>\<^bsub>es\<^esub> ex"
    proof (elim disjE)
      assume "v = n" with entry show ?thesis by auto
    next
      assume "frag_node en1 ex1 E1 v" from A1[OF this] show ?thesis .
    next
      assume "frag_node en2 ex2 E2 v" from A2[OF this] show ?thesis .
    next
      assume "v = ex" then show ?thesis by (auto intro: cfg_path.empty)
    qed
  qed
next
  case (While b c)
  obtain n1 en1 ex1 E1 where
        c0: "compile c (n + 1) = (n1, en1, ex1, E1)"
    and en: "en = n" and ex: "ex = n1"
    and Edef: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, n1)} \<union> E1
                   \<union> {(ex1, EA_Nop, n)}"
    using While.prems(1) by (auto split: prod.splits)
  define g where "g = mk_cfg en ex E"
  have eg: "edges g = E" by (simp add: g_def)
  have subE1: "E1 \<subseteq> E" using Edef by auto
  have ehx: "(n, EA_AssumeNot b, n1) \<in> E" and eb: "(ex1, EA_Nop, n) \<in> E"
    using Edef by auto
  have A1: "\<And>w. frag_node en1 ex1 E1 w \<Longrightarrow> \<exists>es. g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> ex"
  proof -
    fix w assume "frag_node en1 ex1 E1 w"
    from While.IH[OF c0 this] obtain es1 where
      p1: "mk_cfg en1 ex1 E1 \<turnstile> w \<longrightarrow>\<^bsub>es1\<^esub> ex1" by blast
    have "edges (mk_cfg en1 ex1 E1) \<subseteq> edges g" using subE1 eg by simp
    from cfg_path_mono_edges[OF p1 this] have g1: "g \<turnstile> w \<longrightarrow>\<^bsub>es1\<^esub> ex1" .
    have gb: "g \<turnstile> ex1 \<longrightarrow>\<^bsub>[(EA_Nop, n)]\<^esub> n"
      unfolding g_def by (rule mk_cfg_edge_path[OF eb])
    have gx: "g \<turnstile> n \<longrightarrow>\<^bsub>[(EA_AssumeNot b, n1)]\<^esub> n1"
      unfolding g_def by (rule mk_cfg_edge_path[OF ehx])
    from cfg_path_append[OF cfg_path_append[OF g1 gb] gx]
    show "\<exists>es. g \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> ex" using ex by auto
  qed
  have entry: "\<exists>es. g \<turnstile> n \<longrightarrow>\<^bsub>es\<^esub> ex"
  proof -
    have "g \<turnstile> n \<longrightarrow>\<^bsub>[(EA_AssumeNot b, n1)]\<^esub> n1"
      unfolding g_def by (rule mk_cfg_edge_path[OF ehx])
    then show ?thesis using ex by auto
  qed
  have cls: "v = n \<or> frag_node en1 ex1 E1 v \<or> v = ex"
    using While.prems(2) Edef en ex by (auto simp: frag_node_def)
  show ?case unfolding g_def[symmetric]
  proof -
    from cls show "\<exists>es. g \<turnstile> v \<longrightarrow>\<^bsub>es\<^esub> ex"
    proof (elim disjE)
      assume "v = n" with entry show ?thesis by auto
    next
      assume "frag_node en1 ex1 E1 v" from A1[OF this] show ?thesis .
    next
      assume "v = ex" then show ?thesis by (auto intro: cfg_path.empty)
    qed
  qed
qed

(* Top-level: every node of `to_cfg c` reaches the exit. *)
theorem to_cfg_node_reach_exit:
  assumes "frag_node (cfg_entry (to_cfg c)) (cfg_exit (to_cfg c)) (edges (to_cfg c)) v"
  shows "\<exists>es. (to_cfg c) \<turnstile> v \<longrightarrow>\<^bsub>es\<^esub> (cfg_exit (to_cfg c))"
proof -
  obtain n' en ex E where
        cc: "compile c 0 = (n', en, ex, E)"
    and ent: "cfg_entry (to_cfg c) = en"
    and exi: "cfg_exit (to_cfg c) = ex"
    and ed: "edges (to_cfg c) = E"
    by (rule to_cfg_compile)
  have fn: "frag_node en ex E v" using assms ent exi ed by simp
  from compile_frag_node_reach_exit[OF cc fn] obtain es where
    "mk_cfg en ex E \<turnstile> v \<longrightarrow>\<^bsub>es\<^esub> ex" by blast
  then have "(to_cfg c) \<turnstile> v \<longrightarrow>\<^bsub>es\<^esub> ex" using to_cfg_mk[OF cc] by simp
  then show ?thesis using exi by auto
qed

(* The entry node reaches the exit (mirrors the standing entry_reachable hypothesis). *)
corollary to_cfg_entry_reach_exit:
  "\<exists>es. (to_cfg c) \<turnstile> (cfg_entry (to_cfg c)) \<longrightarrow>\<^bsub>es\<^esub> (cfg_exit (to_cfg c))"
  by (rule to_cfg_node_reach_exit) (rule frag_node_en)

(* Every edge target reaches the exit. *)
corollary to_cfg_edge_target_reach_exit:
  assumes "(u, a, w) \<in> edges (to_cfg c)"
  shows "\<exists>es. (to_cfg c) \<turnstile> w \<longrightarrow>\<^bsub>es\<^esub> (cfg_exit (to_cfg c))"
  by (rule to_cfg_node_reach_exit) (rule frag_node_dst[OF assms])

end
