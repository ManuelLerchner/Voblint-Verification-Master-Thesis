theory CFG_Runs_To_Bridge
  imports CFG_Path_Bridge
begin

(*
  CFG collecting layer — import this theory for the full chain.

  Core spec: cfg_collect (per-pp lfp) and cfg_edges_collect (paths).
  Canonical soundness uses cfg_collect at every program point (Pipeline).

  runs_to c s t is definitional exit sugar (runs_to_def), not a second
  operational semantics. Small-step is linked via runs_to_iff_small_step.

  Implementation in src/CFG/Collecting/:
    CFG_Edges_Collect, CFG_Collecting_Core, CFG_Compound_Paths,
    CFG_Path_Bridge, and this file (runs_to + small-step bridge).
*)

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
        path: "?g \<turnstile> (cfg_entry ?g) \<longrightarrow>\<^bsub>es\<^esub> ?v"
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
  assumes p: "(to_cfg c) \<turnstile> (cfg_entry (to_cfg c)) \<longrightarrow>\<^bsub>es\<^esub> (cfg_exit (to_cfg c))"
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
  shows "\<exists>es. (to_cfg c) \<turnstile> (cfg_entry (to_cfg c)) \<longrightarrow>\<^bsub>es\<^esub> (cfg_exit (to_cfg c))
              \<and> t \<in> edges_collect es {s}"
proof -
  from assms have "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
    unfolding runs_to_def .
  hence "t \<in> cfg_edges_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
    using cfg_collect_eq_cfg_edges_collect by simp
  thus ?thesis unfolding cfg_edges_collect_def by blast
qed

lemma runs_to_SKIP_eq_imp:
  "runs_to SKIP s t \<Longrightarrow> t = s"
proof -
  assume rt: "runs_to SKIP s t"
  from runs_to_imp_path[OF rt] obtain es where
        p: "(to_cfg SKIP) \<turnstile> (cfg_entry (to_cfg SKIP)) \<longrightarrow>\<^bsub>es\<^esub> (cfg_exit (to_cfg SKIP))"
    and t_in: "t \<in> edges_collect es {s}"
    by blast
  have E: "edges (to_cfg SKIP) = {(0, EA_Nop, 1)}"
    and en: "cfg_entry (to_cfg SKIP) = 0" and ex: "cfg_exit (to_cfg SKIP) = 1"
    by (auto simp: to_cfg_def Let_def)
  from p en ex have p': "(to_cfg SKIP) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> 1" by simp
  have es_eq: "es = [(EA_Nop, 1)]"
    by (rule cfg_path_singleton_edge[OF E _ p']) simp
  from t_in es_eq show "t = s" by simp
qed

lemma runs_to_SeqE:
  assumes "runs_to (c1 ;; c2) s t"
  shows "\<exists>s2. runs_to c1 s s2 \<and> runs_to c2 s2 t"
proof -
  from assms obtain es where
        p: "(to_cfg (c1 ;; c2)) \<turnstile> (cfg_entry (to_cfg (c1 ;; c2))) \<longrightarrow>\<^bsub>es\<^esub> (cfg_exit (to_cfg (c1 ;; c2)))"
    and t_in: "t \<in> edges_collect es {s}"
    using runs_to_imp_path by blast
  obtain n1 en1 ex1 E1 where
        c1_0: "compile c1 0 = (n1, en1, ex1, E1)"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where
        c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    by (rule to_cfg_compile)
  have c2_n: "compile c2 n1 =
              (n20 + n1, en20 + n1, ex20 + n1, offset_edges n1 E20)"
    using compile_from_0_offsets[OF c2_0, of n1] by simp
  have en_seq: "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    and ex_comp: "cfg_exit (to_cfg (c1 ;; c2)) = ex20 + n1"
    using cfg_edges_entry_exit_Seq[OF c1_0 c2_n] by auto
  from cfg_path_Seq_iff[OF c1_0 c2_0, THEN iffD1, OF p[unfolded en_seq ex_comp]]
  obtain es1 es2 where
        es_eq: "es = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2"
    and p1: "(to_cfg c1) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1"
    and p2: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    by blast
  have collect_eq: "edges_collect es {s} = edges_collect es2 (edges_collect es1 {s})"
    unfolding es_eq by (simp add: edges_collect_append)
  from t_in collect_eq have t_in': "t \<in> edges_collect es2 (edges_collect es1 {s})"
    by simp
  from t_in' obtain s2 where
        s2_in: "s2 \<in> edges_collect es1 {s}"
    and t_in2: "t \<in> edges_collect es2 {s2}"
    by (rule edges_collect_memberE)
  have en1_cfg: "cfg_entry (to_cfg c1) = en1" and ex1_cfg: "cfg_exit (to_cfg c1) = ex1"
    using to_cfg_of_compile_0[OF c1_0] by auto
  have en20_cfg: "cfg_entry (to_cfg c2) = en20" and ex20_cfg: "cfg_exit (to_cfg c2) = ex20"
    using to_cfg_of_compile_0[OF c2_0] by auto
  have p1': "(to_cfg c1) \<turnstile> (cfg_entry (to_cfg c1)) \<longrightarrow>\<^bsub>es1\<^esub> (cfg_exit (to_cfg c1))"
    using p1 en1_cfg ex1_cfg by simp
  have p2': "(to_cfg c2) \<turnstile> (cfg_entry (to_cfg c2)) \<longrightarrow>\<^bsub>es2\<^esub> (cfg_exit (to_cfg c2))"
    using p2 en20_cfg ex20_cfg by simp
  show ?thesis
    using path_imp_runs_to[OF p1' s2_in] path_imp_runs_to[OF p2' t_in2] by blast
qed

lemma runs_to_IfTrueE:
  assumes rt: "runs_to (IF b THEN c1 ELSE c2) s t" and bv: "bval b s"
  shows "runs_to c1 s t"
proof -
  from rt obtain es where
        p: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> (cfg_entry (to_cfg (IF b THEN c1 ELSE c2))) \<longrightarrow>\<^bsub>es\<^esub> (cfg_exit (to_cfg (IF b THEN c1 ELSE c2)))"
    and t_in: "t \<in> edges_collect es {s}"
    using runs_to_imp_path by blast
  obtain n10 en10 ex10 E10 where c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    by (rule to_cfg_compile)
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1_0, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2_0, of "n10 + 1"] by simp
  have en_if: "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and ex_if: "cfg_exit (to_cfg (IF b THEN c1 ELSE c2)) = n20 + (n10 + 1)"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by auto
  from p en_if ex_if have p_if: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n20 + (n10 + 1))"
    by simp
  from cfg_path_If_iff[OF c1_0 c2_0, THEN iffD1, OF p_if] have split_or:
    "(\<exists>es1. es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]
                \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10)
   \<or> (\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]
                \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20)" .
  show ?thesis
  proof (rule disjE[OF split_or])
    assume "\<exists>es1. es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]
                  \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10"
    then obtain es1 where
          es_eq: "es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]"
      and pc1: "(to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10"
      by blast
    have filt: "edge_collect (EA_Assume b) {s} = {s}"
      using bv by auto
    have collect: "edges_collect es {s} = edges_collect es1 {s}"
    proof -
      have "edges_collect es {s}
            = edges_collect (offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))])
                           (edge_collect (EA_Assume b) {s})"
        unfolding es_eq by (simp add: edges_collect_append)
      also have "\<dots> = edges_collect (offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]) {s}"
        using filt by simp
      also have "\<dots> = edges_collect es1 {s}"
        using edges_collect_nop_append by force 
      ultimately show ?thesis
        by blast 
    qed
    from t_in collect have t_in1: "t \<in> edges_collect es1 {s}" by simp
    have en10_cfg: "cfg_entry (to_cfg c1) = en10" and ex10_cfg: "cfg_exit (to_cfg c1) = ex10"
      using to_cfg_of_compile_0[OF c1_0] by auto
    have p1': "(to_cfg c1) \<turnstile> (cfg_entry (to_cfg c1)) \<longrightarrow>\<^bsub>es1\<^esub> (cfg_exit (to_cfg c1))"
      using pc1 en10_cfg ex10_cfg by simp
    show ?thesis using path_imp_runs_to[OF p1' t_in1] .
  next
    assume "\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]
                  \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    then obtain es2 where
          es_eq: "es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]"
      by blast
    have filt: "edge_collect (EA_AssumeNot b) {s} = {}"
      using bv by auto
    have "edges_collect es {s} = {}"
    proof -
      have "edges_collect es {s}
            = edges_collect (offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))])
                           (edge_collect (EA_AssumeNot b) {s})"
        unfolding es_eq by (simp add: edges_collect_append)
      also have "\<dots> = {}" using filt
        using edges_collect_empty_set by presburger 
      finally show ?thesis .
    qed
    with t_in show ?thesis by simp
  qed
qed

lemma runs_to_IfFalseE:
  assumes rt: "runs_to (IF b THEN c1 ELSE c2) s t" and nbv: "\<not> bval b s"
  shows "runs_to c2 s t"
proof -
  from rt obtain es where
        p: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> (cfg_entry (to_cfg (IF b THEN c1 ELSE c2))) \<longrightarrow>\<^bsub>es\<^esub> (cfg_exit (to_cfg (IF b THEN c1 ELSE c2)))"
    and t_in: "t \<in> edges_collect es {s}"
    using runs_to_imp_path by blast
  obtain n10 en10 ex10 E10 where c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    by (rule to_cfg_compile)
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1_0, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2_0, of "n10 + 1"] by simp
  have en_if: "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and ex_if: "cfg_exit (to_cfg (IF b THEN c1 ELSE c2)) = n20 + (n10 + 1)"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by auto
  from p en_if ex_if have p_if: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n20 + (n10 + 1))"
    by simp
  from cfg_path_If_iff[OF c1_0 c2_0, THEN iffD1, OF p_if] have split_or:
    "(\<exists>es1. es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]
                \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10)
   \<or> (\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]
                \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20)" .
  show ?thesis
  proof (rule disjE[OF split_or])
    assume "\<exists>es1. es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]
                  \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10"
    then obtain es1 where
          es_eq: "es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]"
      by blast
    have filt: "edge_collect (EA_Assume b) {s} = {}"
      using nbv by auto
    have "edges_collect es {s} = {}"
    proof -
      have "edges_collect es {s}
            = edges_collect (offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))])
                           (edge_collect (EA_Assume b) {s})"
        unfolding es_eq by (simp add: edges_collect_append)
      also have "\<dots> = {}" using filt
        using edges_collect_empty_set by presburger 
      finally show ?thesis .
    qed
    with t_in show ?thesis by simp
  next
    assume "\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]
                  \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    then obtain es2 where
          es_eq: "es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]"
      and pc2: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
      by blast
    have filt: "edge_collect (EA_AssumeNot b) {s} = {s}"
      using nbv by auto
    have collect: "edges_collect es {s} = edges_collect es2 {s}"
    proof -
      have "edges_collect es {s}
            = edges_collect (offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))])
                           (edge_collect (EA_AssumeNot b) {s})"
        unfolding es_eq by (simp add: edges_collect_append)
      also have "\<dots> = edges_collect (offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]) {s}"
        using filt by simp
      also have "\<dots> = edges_collect es2 {s}"
        by (simp add: edges_collect_append) 
      finally show ?thesis .
    qed
    from t_in collect have t_in2: "t \<in> edges_collect es2 {s}" by simp
    have en20_cfg: "cfg_entry (to_cfg c2) = en20" and ex20_cfg: "cfg_exit (to_cfg c2) = ex20"
      using to_cfg_of_compile_0[OF c2_0] by auto
    have p2': "(to_cfg c2) \<turnstile> (cfg_entry (to_cfg c2)) \<longrightarrow>\<^bsub>es2\<^esub> (cfg_exit (to_cfg c2))"
      using pc2 en20_cfg ex20_cfg by simp
    show ?thesis using path_imp_runs_to[OF p2' t_in2] .
  qed
qed


paragraph \<open>Path-layer helpers for \<open>small_step_preserves_runs_to\<close>\<close>

text \<open>
  Build \<open>runs_to\<close> from explicit CFG paths via Phase-7 \<open>cfg_path_*_iff\<close>.
  Not operational intro rules -- only used inside the reverse bridge.
\<close>

lemma runs_to_skip: "runs_to SKIP s s"
proof -
  have p: "(to_cfg SKIP) \<turnstile> (cfg_entry (to_cfg SKIP)) \<longrightarrow>\<^bsub>[(EA_Nop, cfg_exit (to_cfg SKIP))]\<^esub> (cfg_exit (to_cfg SKIP))"
    by (auto simp: to_cfg_def Let_def intro: cfg_path.intros)
  show ?thesis using path_imp_runs_to[OF p] by simp
qed

lemma path_collect_imp_runs_to_Seq:
  assumes c1_0: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and es1_path: "(to_cfg c1) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1"
    and s2_in: "s2 \<in> edges_collect es1 {s}"
    and es2_path: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    and t_in: "t \<in> edges_collect es2 {s2}"
  shows "runs_to (c1 ;; c2) s t"
proof -
  let ?es = "es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2"
  have c2_n: "compile c2 n1 = (n20 + n1, en20 + n1, ex20 + n1, offset_edges n1 E20)"
    using compile_from_0_offsets[OF c2_0, of n1] by simp
  have en_seq: "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    and ex_seq: "cfg_exit (to_cfg (c1 ;; c2)) = ex20 + n1"
    using cfg_edges_entry_exit_Seq[OF c1_0 c2_n] by auto
  have path_mid: "(to_cfg (c1 ;; c2)) \<turnstile> en1 \<longrightarrow>\<^bsub>?es\<^esub> (ex20 + n1)"
  proof (rule cfg_path_Seq_iff[OF c1_0 c2_0, THEN iffD2])
    show "\<exists>es1 es2. ?es = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2
          \<and> (to_cfg c1) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1
          \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
      using es1_path es2_path by blast
  qed
  have full_path: "(to_cfg (c1 ;; c2)) \<turnstile> (cfg_entry (to_cfg (c1 ;; c2))) \<longrightarrow>\<^bsub>?es\<^esub> (cfg_exit (to_cfg (c1 ;; c2)))"
    using path_mid en_seq ex_seq by simp
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
    from s2_in have sub: "{s2} \<subseteq> edges_collect es1 {s}" by simp
    from edges_collect_mono_strong[OF sub] t_in
    have "t \<in> edges_collect es2 (edges_collect es1 {s})" by blast
    thus ?thesis using collect_eq by simp
  qed
  show ?thesis using path_imp_runs_to[OF full_path t_in_full] .
qed

lemma path_collect_imp_runs_to_IfTrue:
  assumes c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and bv: "bval b s"
    and es1_path: "(to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10"
    and t_in1: "t \<in> edges_collect es1 {s}"
  shows "runs_to (IF b THEN c1 ELSE c2) s t"
proof -
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1_0, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2_0, of "n10 + 1"] by simp
  have en_if: "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and ex_if: "cfg_exit (to_cfg (IF b THEN c1 ELSE c2)) = n20 + (n10 + 1)"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by auto
  let ?es = "(EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]"
  have path_mid: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>?es\<^esub> (n20 + (n10 + 1))"
  proof (rule cfg_path_If_iff[OF c1_0 c2_0, THEN iffD2])
    show "((\<exists>es1. ?es = (EA_Assume b, en10 + 1) # offset_path 1 es1
                        @ [(EA_Nop, n20 + (n10 + 1))]
                    \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10)
          \<or> (\<exists>es2. ?es = (EA_AssumeNot b, en20 + (n10 + 1)) #
                        offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]
                    \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20))"
      by (rule disjI1) (rule_tac x = es1 in exI, use es1_path in auto)
  qed
  have full_path: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> (cfg_entry (to_cfg (IF b THEN c1 ELSE c2))) \<longrightarrow>\<^bsub>?es\<^esub> (cfg_exit (to_cfg (IF b THEN c1 ELSE c2)))"
    using path_mid en_if ex_if by simp
  have collect_eq: "edges_collect ?es {s} = edges_collect es1 {s}"
  proof -
    have "edges_collect ?es {s}
          = edges_collect (offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))])
                          (edge_collect (EA_Assume b) {s})" by simp
    also have "edge_collect (EA_Assume b) {s} = {s}" using bv by auto
    finally have "edges_collect ?es {s}
                  = edges_collect (offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]) {s}" by simp
    also have "\<dots> = edges_collect es1 {s}" by simp
    finally show ?thesis .
  qed
  have t_in_full: "t \<in> edges_collect ?es {s}" using t_in1 collect_eq by simp
  show ?thesis using path_imp_runs_to[OF full_path t_in_full] .
qed

lemma path_collect_imp_runs_to_IfFalse:
  assumes c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and nbv: "\<not> bval b s"
    and es2_path: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    and t_in2: "t \<in> edges_collect es2 {s}"
  shows "runs_to (IF b THEN c1 ELSE c2) s t"
proof -
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1_0, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2_0, of "n10 + 1"] by simp
  have en_if: "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and ex_if: "cfg_exit (to_cfg (IF b THEN c1 ELSE c2)) = n20 + (n10 + 1)"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by auto
  let ?es = "(EA_AssumeNot b, en20 + (n10 + 1)) #
             offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]"
  have path_mid: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>?es\<^esub> (n20 + (n10 + 1))"
  proof (rule cfg_path_If_iff[OF c1_0 c2_0, THEN iffD2])
    show "((\<exists>es1. ?es = (EA_Assume b, en10 + 1) # offset_path 1 es1
                        @ [(EA_Nop, n20 + (n10 + 1))]
                    \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10)
          \<or> (\<exists>es2. ?es = (EA_AssumeNot b, en20 + (n10 + 1)) #
                        offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]
                    \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20))"
      by (rule disjI2) (rule_tac x = es2 in exI, use es2_path in auto)
  qed
  have full_path: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> (cfg_entry (to_cfg (IF b THEN c1 ELSE c2))) \<longrightarrow>\<^bsub>?es\<^esub> (cfg_exit (to_cfg (IF b THEN c1 ELSE c2)))"
    using path_mid en_if ex_if by simp
  have collect_eq: "edges_collect ?es {s} = edges_collect es2 {s}"
  proof -
    have "edges_collect ?es {s}
          = edges_collect (offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))])
                          (edge_collect (EA_AssumeNot b) {s})" by simp
    also have "edge_collect (EA_AssumeNot b) {s} = {s}" using nbv by auto
    finally have "edges_collect ?es {s}
                  = edges_collect (offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]) {s}"
      by simp
    also have "\<dots> = edges_collect es2 {s}" by simp
    finally show ?thesis .
  qed
  have t_in_full: "t \<in> edges_collect ?es {s}" using t_in2 collect_eq by simp
  show ?thesis using path_imp_runs_to[OF full_path t_in_full] .
qed

lemma path_collect_imp_runs_to_WhileFalse:
  assumes c_0: "compile c 0 = (n0, en0, ex0, E0)"
    and nbv: "\<not> bval b s"
  shows "runs_to (WHILE b DO c) s s"
proof -
  have c_1: "compile c 1 = (n0 + 1, en0 + 1, ex0 + 1, offset_edges 1 E0)"
    using compile_from_0_offsets[OF c_0, of 1] by simp
  have Ew: "edges (to_cfg (WHILE b DO c)) =
            {(0, EA_Assume b, en0 + 1), (0, EA_AssumeNot b, n0 + 1)}
            \<union> offset_edges 1 E0 \<union> {(ex0 + 1, EA_Nop, 0)}"
    and en_w: "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    and ex_w: "cfg_exit (to_cfg (WHILE b DO c)) = n0 + 1"
    using cfg_edges_entry_exit_While[OF c_1] by auto
  let ?es = "[(EA_AssumeNot b, n0 + 1)]"
  have path: "(to_cfg (WHILE b DO c)) \<turnstile> (cfg_entry (to_cfg (WHILE b DO c))) \<longrightarrow>\<^bsub>?es\<^esub> (cfg_exit (to_cfg (WHILE b DO c)))"
    using Ew en_w ex_w by (auto intro: cfg_path.intros)
  have t: "s \<in> edges_collect ?es {s}" using nbv by simp
  show ?thesis using path_imp_runs_to[OF path t] .
qed

lemma path_collect_imp_runs_to_WhileTrue:
  assumes c_0: "compile c 0 = (n0, en0, ex0, E0)"
    and bv: "bval b s"
    and body_path: "(to_cfg c) \<turnstile> en0 \<longrightarrow>\<^bsub>es_body\<^esub> ex0"
    and s'_in: "s' \<in> edges_collect es_body {s}"
    and rest_path: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> (n0 + 1)"
    and t_in_rest: "t \<in> edges_collect es_rest {s'}"
  shows "runs_to (WHILE b DO c) s t"
proof -
  have c_1: "compile c 1 = (n0 + 1, en0 + 1, ex0 + 1, offset_edges 1 E0)"
    using compile_from_0_offsets[OF c_0, of 1] by simp
  have Ew: "edges (to_cfg (WHILE b DO c)) =
            {(0, EA_Assume b, en0 + 1), (0, EA_AssumeNot b, n0 + 1)}
            \<union> offset_edges 1 E0 \<union> {(ex0 + 1, EA_Nop, 0)}"
    and en_w: "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    and ex_w: "cfg_exit (to_cfg (WHILE b DO c)) = n0 + 1"
    using cfg_edges_entry_exit_While[OF c_1] by auto
  have body_in: "(to_cfg (WHILE b DO c)) \<turnstile> (en0 + 1) \<longrightarrow>\<^bsub>(offset_path 1 es_body)\<^esub> (ex0 + 1)"
    by (rule cfg_path_sub_offset_into[OF c_0 body_path]) (auto simp: Ew)
  have head: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>[(EA_Assume b, en0 + 1)]\<^esub> (en0 + 1)"
    using Ew by (auto intro: cfg_path.intros)
  have loopback: "(to_cfg (WHILE b DO c)) \<turnstile> (ex0 + 1) \<longrightarrow>\<^bsub>[(EA_Nop, 0)]\<^esub> 0"
    using Ew by (auto intro: cfg_path.intros)
  let ?es = "(EA_Assume b, en0 + 1) # offset_path 1 es_body @ (EA_Nop, 0) # es_rest"
  have path_mid: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>?es\<^esub> (n0 + 1)"
    using cfg_path_append[OF cfg_path_append[OF cfg_path_append[OF head body_in] loopback] rest_path]
    by simp
  have full_path: "(to_cfg (WHILE b DO c)) \<turnstile> (cfg_entry (to_cfg (WHILE b DO c))) \<longrightarrow>\<^bsub>?es\<^esub> (cfg_exit (to_cfg (WHILE b DO c)))"
    using path_mid en_w ex_w by simp
  have filt: "edge_collect (EA_Assume b) {s} = {s}" using bv by auto
  have collect_eq: "edges_collect ?es {s} = edges_collect es_rest (edges_collect es_body {s})"
  proof -
    have "edges_collect ?es {s}
          = edges_collect (offset_path 1 es_body @ (EA_Nop, 0) # es_rest)
                          (edge_collect (EA_Assume b) {s})" by simp
    also have "\<dots> = edges_collect (offset_path 1 es_body @ (EA_Nop, 0) # es_rest) {s}"
      using filt by simp
    also have "\<dots> = edges_collect es_rest (edges_collect es_body {s})" by simp
    finally show ?thesis .
  qed
  have t_in_full: "t \<in> edges_collect ?es {s}"
  proof -
    from s'_in have sub: "{s'} \<subseteq> edges_collect es_body {s}" by simp
    from edges_collect_mono_strong[OF sub] t_in_rest
    have "t \<in> edges_collect es_rest (edges_collect es_body {s})" by blast
    thus ?thesis using collect_eq by simp
  qed
  show ?thesis using path_imp_runs_to[OF full_path t_in_full] .
qed

paragraph \<open>Direct reverse bridge\<close>

lemma small_step_preserves_runs_to:
  "(c, s) \<rightarrow> (c', s') \<Longrightarrow> runs_to c' s' t \<Longrightarrow> runs_to c s t"
proof (induction c s c' s' arbitrary: t rule: small_step_induct)
  case (Assign x a s)
  show ?case
  proof -
    from Assign.prems have eq: "t = s(x := aval a s)"
      using runs_to_small_step star_SKIP_eq by blast

    have p: "(to_cfg (x ::= a)) \<turnstile> (cfg_entry (to_cfg (x ::= a))) \<longrightarrow>\<^bsub>[(EA_Assign x a, cfg_exit (to_cfg (x ::= a)))]\<^esub> (cfg_exit (to_cfg (x ::= a)))"
      by (auto simp: to_cfg_def Let_def intro: cfg_path.intros)
    show "runs_to (x ::= a) s t"
      using path_imp_runs_to[OF p] eq by simp
  qed
next
  case (Seq1 c2 s)
  thus ?case
  proof -
    from Seq1.prems have rt2: "runs_to c2 s t" by simp
    obtain n1 en1 ex1 E1 where c1_0: "compile SKIP 0 = (n1, en1, ex1, E1)"
      and en1_eq: "cfg_entry (to_cfg SKIP) = en1" and ex1_eq: "cfg_exit (to_cfg SKIP) = ex1"
      by (rule to_cfg_compile)
    obtain n20 en20 ex20 E20 where c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
      and en20_eq: "cfg_entry (to_cfg c2) = en20" and ex20_eq: "cfg_exit (to_cfg c2) = ex20"
      by (rule to_cfg_compile)
    from runs_to_imp_path[OF runs_to_skip] obtain es1 where
          es1_path: "(to_cfg SKIP) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1"
      and s_in: "s \<in> edges_collect es1 {s}"
      by (simp add: en1_eq ex1_eq) blast
    from runs_to_imp_path[OF rt2] obtain es2 where
          es2_path: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
      and t_in: "t \<in> edges_collect es2 {s}"
      by (simp add: en20_eq ex20_eq) blast
    show "runs_to (SKIP ;; c2) s t"
      using path_collect_imp_runs_to_Seq[OF c1_0 c2_0 es1_path s_in es2_path t_in] .
  qed
next
  case (Seq2 c1 s c1' s' c2)
  from Seq2.prems obtain s2 where
        a: "runs_to c1' s' s2" and b: "runs_to c2 s2 t"
    using runs_to_SeqE by blast
  from Seq2.IH[OF a] have rt1: "runs_to c1 s s2" .
  obtain n1 en1 ex1 E1 where c1_0: "compile c1 0 = (n1, en1, ex1, E1)"
    and en1_eq: "cfg_entry (to_cfg c1) = en1" and ex1_eq: "cfg_exit (to_cfg c1) = ex1"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and en20_eq: "cfg_entry (to_cfg c2) = en20" and ex20_eq: "cfg_exit (to_cfg c2) = ex20"
    by (rule to_cfg_compile)
  from runs_to_imp_path[OF rt1] obtain es1 where
        es1_path: "(to_cfg c1) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1"
    and s2_in: "s2 \<in> edges_collect es1 {s}"
    by (simp add: en1_eq ex1_eq) blast
  from runs_to_imp_path[OF b] obtain es2 where
        es2_path: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    and t_in: "t \<in> edges_collect es2 {s2}"
    by (simp add: en20_eq ex20_eq) blast
  show ?case
    using path_collect_imp_runs_to_Seq[OF c1_0 c2_0 es1_path s2_in es2_path t_in] .
next
  case (IfTrue b s c1 c2)
  from IfTrue.prems have rt: "runs_to c1 s t" by simp
  obtain n10 en10 ex10 E10 where c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    and en10_eq: "cfg_entry (to_cfg c1) = en10" and ex10_eq: "cfg_exit (to_cfg c1) = ex10"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    by (rule to_cfg_compile)
  from runs_to_imp_path[OF rt] obtain es1 where
        es1_path: "(to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10"
    and t_in1: "t \<in> edges_collect es1 {s}"
    by (simp add: en10_eq ex10_eq) blast
  show "runs_to (IF b THEN c1 ELSE c2) s t"
    using path_collect_imp_runs_to_IfTrue[OF c1_0 c2_0 IfTrue.hyps es1_path t_in1] .
next
  case (IfFalse b s c1 c2)
  from IfFalse.prems have rt: "runs_to c2 s t" by simp
  obtain n10 en10 ex10 E10 where c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and en20_eq: "cfg_entry (to_cfg c2) = en20" and ex20_eq: "cfg_exit (to_cfg c2) = ex20"
    by (rule to_cfg_compile)
  from runs_to_imp_path[OF rt] obtain es2 where
        es2_path: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    and t_in2: "t \<in> edges_collect es2 {s}"
    by (simp add: en20_eq ex20_eq) blast
  show "runs_to (IF b THEN c1 ELSE c2) s t"
    using path_collect_imp_runs_to_IfFalse[OF c1_0 c2_0 IfFalse.hyps es2_path t_in2] .
next
  case (While b c s)
  from While.prems show ?case
  proof (cases "bval b s")
    case True
    from runs_to_IfTrueE[OF While.prems True] have seq_rt: "runs_to (c ;; WHILE b DO c) s t" .
    from seq_rt obtain s2 where bd: "runs_to c s s2" and wh: "runs_to (WHILE b DO c) s2 t"
      using runs_to_SeqE by blast
    obtain n0 en0 ex0 E0 where c_0: "compile c 0 = (n0, en0, ex0, E0)"
      and en0_eq: "cfg_entry (to_cfg c) = en0" and ex0_eq: "cfg_exit (to_cfg c) = ex0"
      by (rule to_cfg_compile)
    have c_1: "compile c 1 = (n0 + 1, en0 + 1, ex0 + 1, offset_edges 1 E0)"
      using compile_from_0_offsets[OF c_0, of 1] by simp
    have en_w: "cfg_entry (to_cfg (WHILE b DO c)) = 0"
      and ex_w: "cfg_exit (to_cfg (WHILE b DO c)) = n0 + 1"
      using cfg_edges_entry_exit_While[OF c_1] by auto
    from runs_to_imp_path[OF bd] obtain es_body where
          body_path: "(to_cfg c) \<turnstile> en0 \<longrightarrow>\<^bsub>es_body\<^esub> ex0"
      and s2_in: "s2 \<in> edges_collect es_body {s}"
      by (simp add: en0_eq ex0_eq) blast
    from runs_to_imp_path[OF wh] obtain es_rest where
          rest_path: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> (n0 + 1)"
      and t_in_rest: "t \<in> edges_collect es_rest {s2}"
      by (simp add: en_w ex_w) blast
    show ?thesis
      using path_collect_imp_runs_to_WhileTrue[OF c_0 True body_path s2_in rest_path t_in_rest] .
  next
    case False
    from runs_to_IfFalseE[OF While.prems False] have skip_rt: "runs_to SKIP s t" .
    have eq: "t = s"
      using runs_to_small_step skip_rt star_SKIP_eq by blast
    obtain n0 en0 ex0 E0 where c_0: "compile c 0 = (n0, en0, ex0, E0)"
      by (rule to_cfg_compile)
    show ?thesis using path_collect_imp_runs_to_WhileFalse[OF c_0 False] eq by simp
  qed
qed

lemma small_step_imp_runs_to:
  "(c, s) \<rightarrow>* (SKIP, t) \<Longrightarrow> runs_to c s t"
proof (induction "(c, s)" "(SKIP, t)" arbitrary: c s rule: star.induct)
  case refl thus ?case by (auto intro: runs_to_skip)
next
  case (step y)
  obtain c' s' where y_eq: "y = (c', s')" by (cases y)
  with step have st: "(c, s) \<rightarrow> (c', s')" and ih: "runs_to c' s' t"
    by simp_all
  show ?case using small_step_preserves_runs_to[OF st ih] .
qed

paragraph \<open>Main reverse bridge\<close>

theorem small_step_runs_to:
  "(c, s) \<rightarrow>* (SKIP, t) \<Longrightarrow> runs_to c s t"
  by (rule small_step_imp_runs_to)

text \<open>
  Combined biconditional surface for downstream consumers.
\<close>

theorem runs_to_iff_small_step:
  "runs_to c s t \<longleftrightarrow> (c, s) \<rightarrow>* (SKIP, t)"
  using runs_to_small_step small_step_runs_to by blast


end
