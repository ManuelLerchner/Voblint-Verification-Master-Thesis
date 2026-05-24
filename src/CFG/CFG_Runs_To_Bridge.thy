theory CFG_Runs_To_Bridge
  imports CFG_Path_Bridge
begin

(* runs_to exit sugar and small-step biconditional bridge. *)

(* ── Exit projection (source-level sugar) ─────────────────────────────────────────── *)

text \<open>
  \<open>runs_to c s t\<close> abbreviates exit membership in \<open>cfg_collect\<close>
  (\<open>runs_to_def\<close>).  Not an inductive operational semantics.
\<close>

definition runs_to :: "com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "runs_to c s t \<longleftrightarrow> t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"

lemma runs_toD[elim]:
  "runs_to c s t \<Longrightarrow> t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  unfolding runs_to_def by simp

lemma cfg_collect_exit_runs_to[intro]:
  "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c)) \<Longrightarrow> runs_to c s t"
  unfolding runs_to_def by simp

lemma runs_to_small_step:
  "runs_to c s t \<Longrightarrow> (c, s) \<rightarrow>* (SKIP, t)"
proof -
  assume rt: "runs_to c s t"
  then have t_in: "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
    by (simp add: runs_to_def)  
  let ?g = "to_cfg c"
  let ?v = "cfg_exit ?g"
  from cfg_collect_eq_cfg_edges_collect[of ?g "{s}" ?v] t_in
  have t_in': "t \<in> cfg_edges_collect ?g {s} ?v" by simp
  then obtain es where
        path: "cfg_path ?g (cfg_entry ?g) es ?v"
    and t: "t \<in> edges_collect es {s}"
    unfolding cfg_edges_collect_def by blast
  show "(c, s) \<rightarrow>* (SKIP, t)"
    using compile_path_small_step path t by blast 
qed


subsection \<open>Reverse bridge: small-step exit reachability implies \<open>runs_to\<close>\<close>

text \<open>
  Companion to \<open>runs_to_small_step\<close>.  Given a terminating small-step
  trace \<open>(c, s) \<rightarrow>* (SKIP, t)\<close> we construct an explicit CFG path from
  the entry to the exit of \<open>to_cfg c\<close> whose \<open>edges_collect\<close> contains
  \<open>t\<close>.  Path membership is then transferred to \<open>cfg_collect\<close> via
  \<open>cfg_collect_eq_cfg_edges_collect\<close>, yielding \<open>runs_to c s t\<close>.
\<close>

lemma path_imp_runs_to:
  assumes p: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
    and t: "t \<in> edges_collect es {s}"
  shows "runs_to c s t"
proof -
  have "t \<in> cfg_edges_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
    using p t unfolding cfg_edges_collect_def by blast
  hence "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
    using cfg_collect_eq_cfg_edges_collect by simp
  thus ?thesis unfolding runs_to_def .
qed

lemma runs_to_imp_path:
  assumes "runs_to c s t"
  shows "\<exists>es. cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))
              \<and> t \<in> edges_collect es {s}"
proof -
  from assms have "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
    unfolding runs_to_def .
  hence "t \<in> cfg_edges_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
    using cfg_collect_eq_cfg_edges_collect by simp
  thus ?thesis unfolding cfg_edges_collect_def by blast
qed


paragraph \<open>Internal path lemmas for \<open>runs_to\<close>\<close>

text \<open>
  Build a CFG path on \<open>to_cfg c\<close> and apply \<open>path_imp_runs_to\<close>.
  Used only for the \<open>small_step_runs_to\<close> proof.
\<close>

lemma runs_to_Skip:
  "runs_to SKIP s s"
proof -
  let ?g = "to_cfg SKIP"
  have E: "edges ?g = {(0, EA_Nop, 1)}"
    and en: "cfg_entry ?g = 0" and ex: "cfg_exit ?g = 1"
    by (auto simp: to_cfg_def Let_def)
  let ?es = "[(EA_Nop, 1::pp)]"
  have path: "cfg_path ?g 0 ?es 1"
    using E by (auto intro: cfg_path.intros)
  hence path': "cfg_path ?g (cfg_entry ?g) ?es (cfg_exit ?g)"
    using en ex by simp
  have t: "s \<in> edges_collect ?es {s}" by simp
  show ?thesis using path_imp_runs_to[OF path' t] .
qed

lemma runs_to_Assign:
  "runs_to (x ::= a) s (s(x := aval a s))"
proof -
  let ?g = "to_cfg (x ::= a)"
  have E: "edges ?g = {(0, EA_Assign x a, 1)}"
    and en: "cfg_entry ?g = 0" and ex: "cfg_exit ?g = 1"
    by (auto simp: to_cfg_def Let_def)
  let ?es = "[(EA_Assign x a, 1::pp)]"
  have path: "cfg_path ?g 0 ?es 1"
    using E by (auto intro: cfg_path.intros)
  hence path': "cfg_path ?g (cfg_entry ?g) ?es (cfg_exit ?g)"
    using en ex by simp
  have t: "s(x := aval a s) \<in> edges_collect ?es {s}" by simp
  show ?thesis using path_imp_runs_to[OF path' t] .
qed

lemma runs_to_Seq:
  assumes p1: "runs_to c1 s s2"
    and   p2: "runs_to c2 s2 t"
  shows "runs_to (c1 ;; c2) s t"
proof -
  obtain n1 en1 ex1 E1 where
        c1_0: "compile c1 0 = (n1, en1, ex1, E1)"
    and en1_eq: "cfg_entry (to_cfg c1) = en1"
    and ex1_eq: "cfg_exit  (to_cfg c1) = ex1"
    and E1_eq: "edges (to_cfg c1) = E1"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where
        c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and en20_eq: "cfg_entry (to_cfg c2) = en20"
    and ex20_eq: "cfg_exit  (to_cfg c2) = ex20"
    and E20_eq: "edges (to_cfg c2) = E20"
    by (rule to_cfg_compile)
  have c2_n: "compile c2 n1 =
              (n20 + n1, en20 + n1, ex20 + n1, offset_edges n1 E20)"
    using compile_from_0_offsets[OF c2_0, of n1] by simp
  have Eseq: "edges (to_cfg (c1 ;; c2)) =
              E1 \<union> {(ex1, EA_Nop, en20 + n1)} \<union> offset_edges n1 E20"
    and en_seq: "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    and ex_seq: "cfg_exit  (to_cfg (c1 ;; c2)) = ex20 + n1"
    using cfg_edges_entry_exit_Seq[OF c1_0 c2_n] by auto

  from runs_to_imp_path[OF p1] obtain es1 where
        es1_path: "cfg_path (to_cfg c1) (cfg_entry (to_cfg c1)) es1 (cfg_exit (to_cfg c1))"
    and s2_in: "s2 \<in> edges_collect es1 {s}"
    by blast
  from runs_to_imp_path[OF p2] obtain es2 where
        es2_path: "cfg_path (to_cfg c2) (cfg_entry (to_cfg c2)) es2 (cfg_exit (to_cfg c2))"
    and t_in: "t \<in> edges_collect es2 {s2}"
    by blast

  have es1_in_compound: "cfg_path (to_cfg (c1 ;; c2)) en1 es1 ex1"
  proof (rule cfg_path_mono_edges)
    show "edges (to_cfg c1) \<subseteq> edges (to_cfg (c1 ;; c2))"
      using E1_eq Eseq by blast
    show "cfg_path (to_cfg c1) en1 es1 ex1"
      using es1_path en1_eq ex1_eq by simp
  qed

  have bridge: "cfg_path (to_cfg (c1 ;; c2)) ex1 [(EA_Nop, en20 + n1)] (en20 + n1)"
    using Eseq by (auto intro: cfg_path.intros)

  have es2_offset_path: "cfg_path (mk_cfg (en20 + n1) (ex20 + n1) (offset_edges n1 E20))
                                  (en20 + n1) (offset_path n1 es2) (ex20 + n1)"
  proof -
    have toc2: "to_cfg c2 = mk_cfg en20 ex20 E20"
      using c2_0 by (simp add: to_cfg_def)
    have "cfg_path (mk_cfg en20 ex20 E20) en20 es2 ex20"
      using es2_path en20_eq ex20_eq toc2 by simp
    from cfg_path_offset[OF this, of n1]
    show ?thesis by simp
  qed
  have es2_in_compound: "cfg_path (to_cfg (c1 ;; c2)) (en20 + n1) (offset_path n1 es2) (ex20 + n1)"
  proof (rule cfg_path_mono_edges)
    show "edges (mk_cfg (en20 + n1) (ex20 + n1) (offset_edges n1 E20))
            \<subseteq> edges (to_cfg (c1 ;; c2))"
      using Eseq by auto
    show "cfg_path (mk_cfg (en20 + n1) (ex20 + n1) (offset_edges n1 E20))
                   (en20 + n1) (offset_path n1 es2) (ex20 + n1)"
      using es2_offset_path .
  qed

  let ?es = "es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2"
  have full_path: "cfg_path (to_cfg (c1 ;; c2)) en1 ?es (ex20 + n1)"
    using cfg_path_append[OF cfg_path_append[OF es1_in_compound bridge] es2_in_compound]
    by simp
  hence full_path': "cfg_path (to_cfg (c1 ;; c2)) (cfg_entry (to_cfg (c1 ;; c2))) ?es
                              (cfg_exit (to_cfg (c1 ;; c2)))"
    using en_seq ex_seq by simp

  have collect_eq: "edges_collect ?es {s} = edges_collect es2 (edges_collect es1 {s})"
  proof -
    have "edges_collect ?es {s}
          = edges_collect ((EA_Nop, en20 + n1) # offset_path n1 es2) (edges_collect es1 {s})"
      by (rule edges_collect_append)
    also have "\<dots> = edges_collect (offset_path n1 es2) (edges_collect es1 {s})" by simp
    also have "\<dots> = edges_collect es2 (edges_collect es1 {s})" by simp
    finally show ?thesis .
  qed
  have t_in_full: "t \<in> edges_collect ?es {s}"
  proof -
    from t_in s2_in have "t \<in> edges_collect es2 (edges_collect es1 {s})"
      using edges_collect_mono_strong by blast
    thus ?thesis using collect_eq by simp
  qed
  show ?thesis using path_imp_runs_to[OF full_path' t_in_full] .
qed

lemma runs_to_IfTrue:
  assumes bv: "bval b s"
    and rt: "runs_to c1 s t"
  shows "runs_to (IF b THEN c1 ELSE c2) s t"
proof -
  obtain n10 en10 ex10 E10 where
        c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    and en10_eq: "cfg_entry (to_cfg c1) = en10"
    and ex10_eq: "cfg_exit  (to_cfg c1) = ex10"
    and E10_eq: "edges (to_cfg c1) = E10"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where
        c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    by (rule to_cfg_compile)
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1_0, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2_0, of "n10 + 1"] by simp
  have Eif: "edges (to_cfg (IF b THEN c1 ELSE c2)) =
             {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, en20 + (n10 + 1))}
             \<union> offset_edges 1 E10 \<union> offset_edges (n10 + 1) E20
             \<union> {(ex10 + 1, EA_Nop, n20 + (n10 + 1)),
                (ex20 + (n10 + 1), EA_Nop, n20 + (n10 + 1))}"
    and en_if: "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and ex_if: "cfg_exit  (to_cfg (IF b THEN c1 ELSE c2)) = n20 + (n10 + 1)"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by auto

  from runs_to_imp_path[OF rt] obtain es1 where
        es1_path: "cfg_path (to_cfg c1) (cfg_entry (to_cfg c1)) es1 (cfg_exit (to_cfg c1))"
    and t_in1: "t \<in> edges_collect es1 {s}"
    by blast

  have toc1: "to_cfg c1 = mk_cfg en10 ex10 E10"
    using c1_0 by (simp add: to_cfg_def)
  have es1_in_mk: "cfg_path (mk_cfg en10 ex10 E10) en10 es1 ex10"
    using es1_path en10_eq ex10_eq toc1 by simp
  from cfg_path_offset[OF es1_in_mk, of 1]
  have es1_offset: "cfg_path (mk_cfg (en10 + 1) (ex10 + 1) (offset_edges 1 E10))
                              (en10 + 1) (offset_path 1 es1) (ex10 + 1)" by simp
  have es1_in_compound: "cfg_path (to_cfg (IF b THEN c1 ELSE c2))
                                   (en10 + 1) (offset_path 1 es1) (ex10 + 1)"
  proof (rule cfg_path_mono_edges)
    show "edges (mk_cfg (en10 + 1) (ex10 + 1) (offset_edges 1 E10))
            \<subseteq> edges (to_cfg (IF b THEN c1 ELSE c2))"
      using Eif by auto
    show "cfg_path (mk_cfg (en10 + 1) (ex10 + 1) (offset_edges 1 E10))
                   (en10 + 1) (offset_path 1 es1) (ex10 + 1)"
      using es1_offset .
  qed

  have head: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) 0 [(EA_Assume b, en10 + 1)] (en10 + 1)"
    using Eif by (auto intro: cfg_path.intros)
  have tail: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) (ex10 + 1) [(EA_Nop, n20 + (n10 + 1))]
                       (n20 + (n10 + 1))"
    using Eif by (auto intro: cfg_path.intros)

  let ?es = "(EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]"
  have full_path: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) 0 ?es (n20 + (n10 + 1))"
    using cfg_path_append[OF cfg_path_append[OF head es1_in_compound] tail]
    by simp
  hence full_path': "cfg_path (to_cfg (IF b THEN c1 ELSE c2))
                              (cfg_entry (to_cfg (IF b THEN c1 ELSE c2))) ?es
                              (cfg_exit (to_cfg (IF b THEN c1 ELSE c2)))"
    using en_if ex_if by simp

  have collect_eq: "edges_collect ?es {s} = edges_collect es1 {s}"
  proof -
    have "edges_collect ?es {s}
          = edges_collect (offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))])
                          (edge_collect (EA_Assume b) {s})"
      by simp
    also have "edge_collect (EA_Assume b) {s} = {s}" using bv by auto
    finally have "edges_collect ?es {s}
                  = edges_collect (offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]) {s}" by simp
    also have "\<dots> = edges_collect [(EA_Nop, n20 + (n10 + 1))] (edges_collect (offset_path 1 es1) {s})"
      by (simp add: edges_collect_append)
    also have "\<dots> = edges_collect (offset_path 1 es1) {s}" by simp
    also have "\<dots> = edges_collect es1 {s}" by simp
    finally show ?thesis .
  qed
  have t_in_full: "t \<in> edges_collect ?es {s}" using t_in1 collect_eq by simp
  show ?thesis using path_imp_runs_to[OF full_path' t_in_full] .
qed

lemma runs_to_IfFalse:
  assumes nbv: "\<not> bval b s"
    and rt: "runs_to c2 s t"
  shows "runs_to (IF b THEN c1 ELSE c2) s t"
proof -
  obtain n10 en10 ex10 E10 where
        c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where
        c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and en20_eq: "cfg_entry (to_cfg c2) = en20"
    and ex20_eq: "cfg_exit  (to_cfg c2) = ex20"
    and E20_eq: "edges (to_cfg c2) = E20"
    by (rule to_cfg_compile)
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1_0, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2_0, of "n10 + 1"] by simp
  have Eif: "edges (to_cfg (IF b THEN c1 ELSE c2)) =
             {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, en20 + (n10 + 1))}
             \<union> offset_edges 1 E10 \<union> offset_edges (n10 + 1) E20
             \<union> {(ex10 + 1, EA_Nop, n20 + (n10 + 1)),
                (ex20 + (n10 + 1), EA_Nop, n20 + (n10 + 1))}"
    and en_if: "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and ex_if: "cfg_exit  (to_cfg (IF b THEN c1 ELSE c2)) = n20 + (n10 + 1)"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by auto

  from runs_to_imp_path[OF rt] obtain es2 where
        es2_path: "cfg_path (to_cfg c2) (cfg_entry (to_cfg c2)) es2 (cfg_exit (to_cfg c2))"
    and t_in2: "t \<in> edges_collect es2 {s}"
    by blast

  have toc2: "to_cfg c2 = mk_cfg en20 ex20 E20"
    using c2_0 by (simp add: to_cfg_def)
  have es2_in_mk: "cfg_path (mk_cfg en20 ex20 E20) en20 es2 ex20"
    using es2_path en20_eq ex20_eq toc2 by simp
  from cfg_path_offset[OF es2_in_mk, of "n10 + 1"]
  have es2_offset: "cfg_path (mk_cfg (en20 + (n10 + 1)) (ex20 + (n10 + 1))
                                      (offset_edges (n10 + 1) E20))
                              (en20 + (n10 + 1)) (offset_path (n10 + 1) es2)
                              (ex20 + (n10 + 1))" by simp
  have es2_in_compound: "cfg_path (to_cfg (IF b THEN c1 ELSE c2))
                                   (en20 + (n10 + 1)) (offset_path (n10 + 1) es2)
                                   (ex20 + (n10 + 1))"
  proof (rule cfg_path_mono_edges)
    show "edges (mk_cfg (en20 + (n10 + 1)) (ex20 + (n10 + 1)) (offset_edges (n10 + 1) E20))
            \<subseteq> edges (to_cfg (IF b THEN c1 ELSE c2))"
      using Eif by auto
    show "cfg_path (mk_cfg (en20 + (n10 + 1)) (ex20 + (n10 + 1)) (offset_edges (n10 + 1) E20))
                   (en20 + (n10 + 1)) (offset_path (n10 + 1) es2) (ex20 + (n10 + 1))"
      using es2_offset .
  qed

  have head: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) 0
                        [(EA_AssumeNot b, en20 + (n10 + 1))] (en20 + (n10 + 1))"
    using Eif by (auto intro: cfg_path.intros)
  have tail: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) (ex20 + (n10 + 1))
                        [(EA_Nop, n20 + (n10 + 1))] (n20 + (n10 + 1))"
    using Eif by (auto intro: cfg_path.intros)

  let ?es = "(EA_AssumeNot b, en20 + (n10 + 1)) #
             offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]"
  have full_path: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) 0 ?es (n20 + (n10 + 1))"
    using cfg_path_append[OF cfg_path_append[OF head es2_in_compound] tail]
    by simp
  hence full_path': "cfg_path (to_cfg (IF b THEN c1 ELSE c2))
                              (cfg_entry (to_cfg (IF b THEN c1 ELSE c2))) ?es
                              (cfg_exit (to_cfg (IF b THEN c1 ELSE c2)))"
    using en_if ex_if by simp

  have collect_eq: "edges_collect ?es {s} = edges_collect es2 {s}"
  proof -
    have "edges_collect ?es {s}
          = edges_collect (offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))])
                          (edge_collect (EA_AssumeNot b) {s})"
      by simp
    also have "edge_collect (EA_AssumeNot b) {s} = {s}" using nbv by auto
    finally have "edges_collect ?es {s}
                  = edges_collect (offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]) {s}"
      by simp
    also have "\<dots> = edges_collect [(EA_Nop, n20 + (n10 + 1))]
                                    (edges_collect (offset_path (n10 + 1) es2) {s})"
      by (simp add: edges_collect_append)
    also have "\<dots> = edges_collect (offset_path (n10 + 1) es2) {s}" by simp
    also have "\<dots> = edges_collect es2 {s}" by simp
    finally show ?thesis .
  qed
  have t_in_full: "t \<in> edges_collect ?es {s}" using t_in2 collect_eq by simp
  show ?thesis using path_imp_runs_to[OF full_path' t_in_full] .
qed

lemma runs_to_WhileFalse:
  assumes nbv: "\<not> bval b s"
  shows "runs_to (WHILE b DO c) s s"
proof -
  obtain n0 en0 ex0 E0 where
        c_0: "compile c 0 = (n0, en0, ex0, E0)"
    by (rule to_cfg_compile)
  have c_1: "compile c 1 = (n0 + 1, en0 + 1, ex0 + 1, offset_edges 1 E0)"
    using compile_from_0_offsets[OF c_0, of 1] by simp
  have Ew: "edges (to_cfg (WHILE b DO c)) =
            {(0, EA_Assume b, en0 + 1), (0, EA_AssumeNot b, n0 + 1)}
            \<union> offset_edges 1 E0 \<union> {(ex0 + 1, EA_Nop, 0)}"
    and en_w: "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    and ex_w: "cfg_exit  (to_cfg (WHILE b DO c)) = n0 + 1"
    using cfg_edges_entry_exit_While[OF c_1] by auto
  let ?es = "[(EA_AssumeNot b, n0 + 1::pp)]"
  have path: "cfg_path (to_cfg (WHILE b DO c)) 0 ?es (n0 + 1)"
    using Ew by (auto intro: cfg_path.intros)
  hence path': "cfg_path (to_cfg (WHILE b DO c)) (cfg_entry (to_cfg (WHILE b DO c))) ?es
                         (cfg_exit (to_cfg (WHILE b DO c)))"
    using en_w ex_w by simp
  have t: "s \<in> edges_collect ?es {s}" using nbv by simp
  show ?thesis using path_imp_runs_to[OF path' t] .
qed

lemma runs_to_WhileTrue:
  assumes bv: "bval b s"
    and body: "runs_to c s s'"
    and rest: "runs_to (WHILE b DO c) s' t"
  shows "runs_to (WHILE b DO c) s t"
proof -
  obtain n0 en0 ex0 E0 where
        c_0: "compile c 0 = (n0, en0, ex0, E0)"
    and en0_eq: "cfg_entry (to_cfg c) = en0"
    and ex0_eq: "cfg_exit  (to_cfg c) = ex0"
    and E0_eq: "edges (to_cfg c) = E0"
    by (rule to_cfg_compile)
  have c_1: "compile c 1 = (n0 + 1, en0 + 1, ex0 + 1, offset_edges 1 E0)"
    using compile_from_0_offsets[OF c_0, of 1] by simp
  have Ew: "edges (to_cfg (WHILE b DO c)) =
            {(0, EA_Assume b, en0 + 1), (0, EA_AssumeNot b, n0 + 1)}
            \<union> offset_edges 1 E0 \<union> {(ex0 + 1, EA_Nop, 0)}"
    and en_w: "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    and ex_w: "cfg_exit  (to_cfg (WHILE b DO c)) = n0 + 1"
    using cfg_edges_entry_exit_While[OF c_1] by auto

  from runs_to_imp_path[OF body] obtain es_body where
        body_path: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es_body (cfg_exit (to_cfg c))"
    and s'_in: "s' \<in> edges_collect es_body {s}"
    by blast
  from runs_to_imp_path[OF rest] obtain es_rest where
        rest_path: "cfg_path (to_cfg (WHILE b DO c)) (cfg_entry (to_cfg (WHILE b DO c)))
                              es_rest (cfg_exit (to_cfg (WHILE b DO c)))"
    and t_in_rest: "t \<in> edges_collect es_rest {s'}"
    by blast

  have toc: "to_cfg c = mk_cfg en0 ex0 E0"
    using c_0 by (simp add: to_cfg_def)
  have body_in_mk: "cfg_path (mk_cfg en0 ex0 E0) en0 es_body ex0"
    using body_path en0_eq ex0_eq toc by simp
  from cfg_path_offset[OF body_in_mk, of 1]
  have body_offset: "cfg_path (mk_cfg (en0 + 1) (ex0 + 1) (offset_edges 1 E0))
                               (en0 + 1) (offset_path 1 es_body) (ex0 + 1)" by simp
  have body_in_compound: "cfg_path (to_cfg (WHILE b DO c)) (en0 + 1) (offset_path 1 es_body)
                                    (ex0 + 1)"
  proof (rule cfg_path_mono_edges)
    show "edges (mk_cfg (en0 + 1) (ex0 + 1) (offset_edges 1 E0))
            \<subseteq> edges (to_cfg (WHILE b DO c))"
      using Ew by auto
    show "cfg_path (mk_cfg (en0 + 1) (ex0 + 1) (offset_edges 1 E0))
                   (en0 + 1) (offset_path 1 es_body) (ex0 + 1)"
      using body_offset .
  qed

  have head: "cfg_path (to_cfg (WHILE b DO c)) 0 [(EA_Assume b, en0 + 1)] (en0 + 1)"
    using Ew by (auto intro: cfg_path.intros)
  have loopback: "cfg_path (to_cfg (WHILE b DO c)) (ex0 + 1) [(EA_Nop, 0::pp)] 0"
    using Ew by (auto intro: cfg_path.intros)
  have rest_from_0: "cfg_path (to_cfg (WHILE b DO c)) 0 es_rest (n0 + 1)"
    using rest_path en_w ex_w by simp

  let ?es = "(EA_Assume b, en0 + 1) # offset_path 1 es_body @ (EA_Nop, 0) # es_rest"
  have full_path: "cfg_path (to_cfg (WHILE b DO c)) 0 ?es (n0 + 1)"
    using cfg_path_append[OF cfg_path_append[OF cfg_path_append[OF head body_in_compound] loopback] rest_from_0]
    by simp
  hence full_path': "cfg_path (to_cfg (WHILE b DO c))
                              (cfg_entry (to_cfg (WHILE b DO c))) ?es
                              (cfg_exit (to_cfg (WHILE b DO c)))"
    using en_w ex_w by simp

  have filt: "edge_collect (EA_Assume b) {s} = {s}" using bv by auto
  have collect_eq: "edges_collect ?es {s} = edges_collect es_rest (edges_collect es_body {s})"
  proof -
    have "edges_collect ?es {s}
          = edges_collect (offset_path 1 es_body @ (EA_Nop, 0) # es_rest)
                          (edge_collect (EA_Assume b) {s})"
      by simp
    also have "\<dots> = edges_collect (offset_path 1 es_body @ (EA_Nop, 0) # es_rest) {s}"
      using filt by simp
    also have "\<dots> = edges_collect ((EA_Nop, 0) # es_rest) (edges_collect (offset_path 1 es_body) {s})"
      by (simp add: edges_collect_append)
    also have "\<dots> = edges_collect es_rest (edges_collect (offset_path 1 es_body) {s})"
      by simp
    also have "\<dots> = edges_collect es_rest (edges_collect es_body {s})"
      by simp
    finally show ?thesis .
  qed
  have t_in_full: "t \<in> edges_collect ?es {s}"
  proof -
    from t_in_rest s'_in have "t \<in> edges_collect es_rest (edges_collect es_body {s})"
      using edges_collect_mono_strong by blast
    thus ?thesis using collect_eq by simp
  qed
  show ?thesis using path_imp_runs_to[OF full_path' t_in_full] .
qed


paragraph \<open>Internal evaluation predicate (proof helper)\<close>

text \<open>
  \<open>terminates_to\<close> is an internal inductive helper for the
  \<open>small_step \<rightarrow> runs_to\<close> bridge (not exported semantics).
\<close>

inductive terminates_to :: "com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  TSkip:    "terminates_to SKIP s s"
| TAssign:  "terminates_to (x ::= a) s (s(x := aval a s))"
| TSeq:     "terminates_to c1 s s2 \<Longrightarrow> terminates_to c2 s2 t
             \<Longrightarrow> terminates_to (c1 ;; c2) s t"
| TIfTrue:  "bval b s \<Longrightarrow> terminates_to c1 s t
             \<Longrightarrow> terminates_to (IF b THEN c1 ELSE c2) s t"
| TIfFalse: "\<not> bval b s \<Longrightarrow> terminates_to c2 s t
             \<Longrightarrow> terminates_to (IF b THEN c1 ELSE c2) s t"
| TWhileF:  "\<not> bval b s \<Longrightarrow> terminates_to (WHILE b DO c) s s"
| TWhileT:  "bval b s \<Longrightarrow> terminates_to c s s'
             \<Longrightarrow> terminates_to (WHILE b DO c) s' t
             \<Longrightarrow> terminates_to (WHILE b DO c) s t"

lemma small1_terminates_continue:
  "(c, s) \<rightarrow> (c', s') \<Longrightarrow> terminates_to c' s' t \<Longrightarrow> terminates_to c s t"
proof (induction c s c' s' arbitrary: t rule: small_step_induct)
  case (Assign x a s)
  hence "t = s(x := aval a s)" by (auto elim!: terminates_to.cases)
  thus ?case by (metis TAssign)
next
  case (Seq1 c2 s) thus ?case by (auto intro: TSeq TSkip)
next
  case (Seq2 c1 s c1' s' c2)
  from Seq2.prems obtain s2 where
        a: "terminates_to c1' s' s2" and b: "terminates_to c2 s2 t"
    using terminates_to.cases by force
  from Seq2.IH[OF a] b show ?case by (auto intro: TSeq)
next
  case (IfTrue b s c1 c2) thus ?case by (auto intro: TIfTrue)
next
  case (IfFalse b s c1 c2) thus ?case by (auto intro: TIfFalse)
next
  case (While b c s)
  from While.prems show ?case
  proof (cases rule: terminates_to.cases)
    case TIfTrue
    then obtain s' where bv: "bval b s"
                     and bd: "terminates_to c s s'"
                     and wh: "terminates_to (WHILE b DO c) s' t"
      using terminates_to.cases by force
    show ?thesis using TWhileT[OF bv bd wh] .
  next
    case TIfFalse
    then have nbv: "\<not> bval b s" and sk: "terminates_to SKIP s t" by auto
    from sk have "t = s" by (auto elim: terminates_to.cases)
    thus ?thesis using nbv TWhileF by auto
  qed
qed

lemma small_step_imp_terminates_to:
  "(c, s) \<rightarrow>* (SKIP, t) \<Longrightarrow> terminates_to c s t"
proof (induction "(c, s)" "(SKIP, t)" arbitrary: c s rule: star.induct)
  case refl thus ?case by (auto intro: TSkip)
next
  case (step y)
  obtain c' s' where y_eq: "y = (c', s')" by (cases y)
  with step have "(c, s) \<rightarrow> (c', s')" by simp
  moreover have "terminates_to c' s' t"
    using step y_eq by simp
  ultimately show ?case
    using small1_terminates_continue by blast
qed

lemma terminates_to_imp_runs_to:
  "terminates_to c s t \<Longrightarrow> runs_to c s t"
proof (induction rule: terminates_to.induct)
  case (TSkip s) thus ?case by (rule runs_to_Skip)
next
  case (TAssign x a s) thus ?case by (rule runs_to_Assign)
next
  case (TSeq c1 s s2 c2 t) thus ?case using runs_to_Seq by blast
next
  case (TIfTrue b s c1 t c2) thus ?case using runs_to_IfTrue by blast
next
  case (TIfFalse b s c2 t c1) thus ?case using runs_to_IfFalse by blast
next
  case (TWhileF b s c) thus ?case by (rule runs_to_WhileFalse)
next
  case (TWhileT b s c s' t) thus ?case using runs_to_WhileTrue by blast
qed


paragraph \<open>Main reverse bridge\<close>

theorem small_step_runs_to:
  "(c, s) \<rightarrow>* (SKIP, t) \<Longrightarrow> runs_to c s t"
  using small_step_imp_terminates_to terminates_to_imp_runs_to by blast

text \<open>
  Combined biconditional surface for downstream consumers.
\<close>

theorem runs_to_iff_small_step:
  "runs_to c s t \<longleftrightarrow> (c, s) \<rightarrow>* (SKIP, t)"
  using runs_to_small_step small_step_runs_to by blast


end
