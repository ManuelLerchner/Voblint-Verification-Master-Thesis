theory CFG_Compound_Paths
  imports CFG_Collecting_Core
begin

(* Compound-command CFG path structure (Seq / If / While). *)

(* \<midarrow>\<midarrow> to_cfg / compile alignment \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

lemma to_cfg_mk:
  assumes "compile c 0 = (n, en, ex, E)"
  shows "to_cfg c = mk_cfg en ex E"
  using assms by (simp add: to_cfg_def Let_def split: prod.splits)

lemmas to_cfg_simps = to_cfg_mk to_cfg_def Let_def

lemma to_cfg_of_compile_0:
  assumes "compile c 0 = (n, en, ex, E)"
  shows "cfg_entry (to_cfg c) = en" and "cfg_exit (to_cfg c) = ex" and "edges (to_cfg c) = E"
  using assms to_cfg_mk by auto

lemma to_cfg_compile:
  obtains n' en ex E where
    "compile c 0 = (n', en, ex, E)"
    "cfg_entry (to_cfg c) = en"
    "cfg_exit (to_cfg c) = ex"
    "edges (to_cfg c) = E"
  by (cases "compile c 0") (auto simp: to_cfg_simps)

 

lemma cfg_edges_entry_exit_Seq:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "edges (to_cfg (c1 ;; c2)) = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    and "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    and "cfg_exit (to_cfg (c1 ;; c2)) = ex2"
proof -
  define E12 where "E12 = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
  from c1 c2 have cmp: "compile (c1 ;; c2) 0 = (n2, en1, ex2, E12)"
    unfolding E12_def by simp
  show "edges (to_cfg (c1 ;; c2)) = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    using cmp unfolding E12_def by (simp add: to_cfg_simps)
  show "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    using cmp by (simp add: to_cfg_simps)
  show "cfg_exit (to_cfg (c1 ;; c2)) = ex2"
    using cmp by (simp add: to_cfg_simps)
qed

lemma cfg_edges_entry_exit_If:
  assumes c1: "compile c1 1 = (n1, en1, ex1, E1)"
    and   c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "edges (to_cfg (IF b THEN c1 ELSE c2)) =
         {(0, EA_Assume b, en1), (0, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
         \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    and "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and "cfg_exit  (to_cfg (IF b THEN c1 ELSE c2)) = n2"
  using assms
proof -
  define EI where "EI = {(0, EA_Assume b, en1), (0, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
                       \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
  from c1 c2 have cmp: "compile (IF b THEN c1 ELSE c2) 0 = (n2 + 1, 0, n2, EI)"
    unfolding EI_def by simp
  show "edges (to_cfg (IF b THEN c1 ELSE c2)) =
        {(0, EA_Assume b, en1), (0, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
        \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    using cmp unfolding EI_def by (simp add: to_cfg_simps)
  show "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    using cmp by (simp add: to_cfg_simps)
  show "cfg_exit  (to_cfg (IF b THEN c1 ELSE c2)) = n2"
    using cmp by (simp add: to_cfg_simps)
qed

lemma cfg_edges_entry_exit_While:
  assumes c: "compile c 1 = (n1, en1, ex1, E1)"
  shows "edges (to_cfg (WHILE b DO c)) =
         {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)}"
    and "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    and "cfg_exit  (to_cfg (WHILE b DO c)) = n1"
proof -
  define EW where "EW = {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)}"
  from c have cmp: "compile (WHILE b DO c) 0 = (Suc n1, 0, n1, EW)"
    unfolding EW_def by simp
  show "edges (to_cfg (WHILE b DO c)) =
        {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)}"
    using cmp unfolding EW_def by (simp add: to_cfg_simps)
  show "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    using cmp by (simp add: to_cfg_simps)
  show "cfg_exit  (to_cfg (WHILE b DO c)) = n1"
    using cmp by (simp add: to_cfg_simps)
qed

lemma cfg_edges_If_from_0:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
  shows "edges (to_cfg (IF b THEN c1 ELSE c2)) =
         {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, en20 + (n10 + 1))}
         \<union> offset_edges 1 E10
         \<union> offset_edges (n10 + 1) E20
         \<union> {(ex10 + 1, EA_Nop, n20 + (n10 + 1)),
            (ex20 + (n10 + 1), EA_Nop, n20 + (n10 + 1))}"
proof -
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2, of "n10 + 1"] by simp
  show ?thesis using cfg_edges_entry_exit_If[OF c1_1 c2_n] by simp
qed

lemma cfg_edges_While_from_0:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
  shows "edges (to_cfg (WHILE b DO c)) =
         {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, n10 + 1)}
         \<union> offset_edges 1 E10 \<union> {(ex10 + 1, EA_Nop, 0)}"
proof -
  have c1: "compile c 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c0, of 1] by simp
  show ?thesis using cfg_edges_entry_exit_While[OF c1] by simp
qed

lemma cfg_path_mono_edges[intro]:
  assumes p: "g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> v"
    and sub: "edges g \<subseteq> edges h"
  shows "h \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> v"
  using assms apply (induction rule: cfg_path.induct)
  by auto

lemma cfg_path_sub_offset_into:
  assumes c0: "compile c 0 = (n, en, ex, E)"
    and p: "(to_cfg c) \<turnstile> en \<longrightarrow>\<^bsub>es\<^esub> ex"
    and sub: "edges (mk_cfg (en + k) (ex + k) (offset_edges k E)) \<subseteq> edges g"
  shows "g \<turnstile> (en + k) \<longrightarrow>\<^bsub>(offset_path k es)\<^esub> (ex + k)"
proof -
  have p_off: "(mk_cfg (en + k) (ex + k) (offset_edges k E)) \<turnstile> (en + k) \<longrightarrow>\<^bsub>(offset_path k es)\<^esub> (ex + k)"
    using cfg_path_offset to_cfg_mk c0 p by presburger 
  then show ?thesis
    using sub by blast
qed

lemma cfg_path_no_out_empty:
  assumes p: "g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> v"
    and no_out: "\<not> (\<exists>a w. (u, a, w) \<in> edges g)"
  shows "es = [] \<and> u = v"
  using p no_out by (cases rule: cfg_path.cases[OF p]) auto

(*
  Edge classification in `to_cfg (c1 ;; c2)`.  By compile_fresh / compile_ge:
  - E1 edges have both endpoints < n1
  - the bridge (ex1, EA_Nop, en20+n1) has source ex1 < n1
  - offset_edges n1 E20 has all endpoints \<ge> n1
  So an edge's source decides which subset it belongs to.
*)

lemma compound_Seq_edge_src_ge_n1:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and edge: "(u, a, w) \<in> edges (to_cfg (c1 ;; c2))"
    and u_ge: "n1 \<le> u"
  shows "(u, a, w) \<in> offset_edges n1 E20"
proof -
  have c2_n: "compile c2 n1 = (n20 + n1, en20 + n1, ex20 + n1, offset_edges n1 E20)"
    using compile_from_0_offsets[OF c2_0, of n1] by simp
  have Eseq: "edges (to_cfg (c1 ;; c2)) =
              E1 \<union> {(ex1, EA_Nop, en20 + n1)} \<union> offset_edges n1 E20"
    using cfg_edges_entry_exit_Seq[OF c1 c2_n] by simp
  from compile_fresh[OF c1] have E1_src_lt: "\<forall>e \<in> E1. fst e < n1" by fastforce
  from compile_fresh[OF c1] have ex1_lt: "ex1 < n1" by simp
  show ?thesis
    using edge u_ge Eseq E1_src_lt ex1_lt by force
qed


lemma compound_Seq_edge_src_lt_n1:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and edge: "(u, a, w) \<in> edges (to_cfg (c1 ;; c2))"
    and u_lt: "u < n1"
  shows "(u, a, w) \<in> E1 \<or> (u = ex1 \<and> a = EA_Nop \<and> w = en20 + n1)"
proof -
  have c2_n: "compile c2 n1 = (n20 + n1, en20 + n1, ex20 + n1, offset_edges n1 E20)"
    using compile_from_0_offsets[OF c2_0, of n1] by simp
  have Eseq: "edges (to_cfg (c1 ;; c2)) =
              E1 \<union> {(ex1, EA_Nop, en20 + n1)} \<union> offset_edges n1 E20"
    using cfg_edges_entry_exit_Seq[OF c1 c2_n] by simp
  from compile_ge[OF c2_n] have E2_src_ge: "\<forall>e \<in> offset_edges n1 E20. n1 \<le> fst e" by simp
  show ?thesis
    using edge u_lt Eseq E2_src_ge by force
qed

(*
  A compound-Seq path starting at u \<ge> n1 stays in the c2 region; its
  step list is the offset_path of a path in to_cfg c2.
*)
lemma cfg_path_Seq_in_c2:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and p: "(to_cfg (c1 ;; c2)) \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> v"
    and u_ge: "n1 \<le> u"
  shows "\<exists>es'. es = offset_path n1 es' \<and>
                (to_cfg c2) \<turnstile> (u - n1) \<longrightarrow>\<^bsub>es'\<^esub> (v - n1)"
  using p u_ge
proof (induction es arbitrary: u)
  case Nil
  then have "u = v"
    by blast 
  hence "(to_cfg c2) \<turnstile> (u - n1) \<longrightarrow>\<^bsub>[]\<^esub> (v - n1)"
    by (simp add: cfg_path.empty)
  thus ?case
    by (simp add: offset_path_def)
next
  case (Cons hd tl)
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from Cons.prems(1) hd_eq obtain
        e_compound: "(u, a, w) \<in> edges (to_cfg (c1 ;; c2))"
    and ps: "(to_cfg (c1 ;; c2)) \<turnstile> w \<longrightarrow>\<^bsub>tl\<^esub> v"
    by blast
  have e_off: "(u, a, w) \<in> offset_edges n1 E20"
    using Cons.prems(2) c1 c2_0 compound_Seq_edge_src_ge_n1 e_compound by auto
  from e_off obtain u0 w0 where
        decomp: "u = u0 + n1" "w = w0 + n1" "(u0, a, w0) \<in> E20"
    unfolding offset_edges_def by auto
  have kw: "n1 \<le> w" using decomp(2) by simp
  from Cons.IH[OF ps kw] obtain es' where
        es_eq: "tl = offset_path n1 es'"
    and pe2: "(to_cfg c2) \<turnstile> (w - n1) \<longrightarrow>\<^bsub>es'\<^esub> (v - n1)"
    by auto
  have toc2_edges: "edges (to_cfg c2) = E20"
    using c2_0 by (simp add: to_cfg_simps)
  have edge_c2: "(u - n1, a, w - n1) \<in> edges (to_cfg c2)"
    using toc2_edges decomp by simp
  let ?es'_full = "(a, w - n1) # es'"
  have p_full: "(to_cfg c2) \<turnstile> (u - n1) \<longrightarrow>\<^bsub>?es'_full\<^esub> (v - n1)"
    by (rule cfg_path.step[OF edge_c2 pe2])
  have list_eq: "(a, w) # tl = offset_path n1 ?es'_full"
    using es_eq decomp(2) by simp
  show ?case
    using p_full list_eq hd_eq by (rule_tac x = "?es'_full" in exI) simp
qed

(*
  Strong Seq path split.  A path in to_cfg (c1;;c2) starting at u < n1
  and ending at the compound exit factors uniquely through the bridge
  (ex1, EA_Nop, en20+n1) into a path in to_cfg c1 (u \<to> ex1) and a
  path in to_cfg c2 (en20 \<to> ex20), with the c2-part shifted via
  offset_path n1.
*)
lemma cfg_path_Seq_split:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and p: "(to_cfg (c1 ;; c2)) \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> (ex20 + n1)"
    and u_lt: "u < n1"
  shows "\<exists>es1 es2.
           es = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2 \<and>
           (to_cfg c1) \<turnstile> u \<longrightarrow>\<^bsub>es1\<^esub> ex1 \<and>
           (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
  using p u_lt
proof (induction es arbitrary: u)
  case Nil
  from Nil(1) have eq: "u = ex20 + n1" by (cases rule: cfg_path.cases) simp_all
  with Nil.prems(2) show ?case by simp
next
  case (Cons hd tl)
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from Cons.prems(1) hd_eq obtain
        e_compound: "(u, a, w) \<in> edges (to_cfg (c1 ;; c2))"
    and ps: "(to_cfg (c1 ;; c2)) \<turnstile> w \<longrightarrow>\<^bsub>tl\<^esub> (ex20 + n1)"
    by (cases rule: cfg_path.cases) auto
  from compound_Seq_edge_src_lt_n1[OF c1 c2_0 e_compound Cons.prems(2)]
  consider (E1) "(u, a, w) \<in> E1" | (bridge) "u = ex1" "a = EA_Nop" "w = en20 + n1"
    by auto
  thus ?case
  proof cases
    case E1
    from compile_fresh[OF c1] E1 have w_lt: "w < n1" by auto
    from Cons.IH[OF ps w_lt] obtain es1 es2 where
          tl_eq: "tl = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2"
      and p1: "(to_cfg c1) \<turnstile> w \<longrightarrow>\<^bsub>es1\<^esub> ex1"
      and p2: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
      by blast
    have toc1_edges: "edges (to_cfg c1) = E1"
      using c1 by (simp add: to_cfg_simps)
    have edge_c1: "(u, a, w) \<in> edges (to_cfg c1)" using E1 toc1_edges by simp
    let ?es1_full = "(a, w) # es1"
    have p1_full: "(to_cfg c1) \<turnstile> u \<longrightarrow>\<^bsub>?es1_full\<^esub> ex1"
      by (rule cfg_path.step[OF edge_c1 p1])
    have list_eq: "(a, w) # tl = ?es1_full @ (EA_Nop, en20 + n1) # offset_path n1 es2"
      using tl_eq by simp
    show ?thesis
      using list_eq p1_full p2 hd_eq by blast
  next
    case bridge
    have w_ge: "n1 \<le> w" using bridge(3) by simp
    from cfg_path_Seq_in_c2[OF c1 c2_0 ps w_ge] obtain es' where
          tl_eq: "tl = offset_path n1 es'"
      and pe2: "(to_cfg c2) \<turnstile> (w - n1) \<longrightarrow>\<^bsub>es'\<^esub> ((ex20 + n1) - n1)"
      by auto
    have wn: "w - n1 = en20" using bridge(3) by simp
    have exn: "(ex20 + n1) - n1 = ex20" by simp
    have p2: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es'\<^esub> ex20" using pe2 wn exn by simp
    have p1: "(to_cfg c1) \<turnstile> u \<longrightarrow>\<^bsub>[]\<^esub> ex1"
      using bridge(1) by (simp add: cfg_path.empty)
    have list_eq: "(a, w) # tl = [] @ (EA_Nop, en20 + n1) # offset_path n1 es'"
      using bridge tl_eq by simp
    show ?thesis
      using list_eq p1 p2 hd_eq by blast
  qed
qed

(* Bidirectional Seq path characterization (Phase 7). *)
lemma cfg_path_Seq_iff:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
  shows "(to_cfg (c1 ;; c2)) \<turnstile> en1 \<longrightarrow>\<^bsub>es\<^esub> (ex20 + n1)
         \<longleftrightarrow> (\<exists>es1 es2.
              es = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2
              \<and> (to_cfg c1) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1
              \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20)"
proof (intro iffI)
  assume p: "(to_cfg (c1 ;; c2)) \<turnstile> en1 \<longrightarrow>\<^bsub>es\<^esub> (ex20 + n1)"
  show "\<exists>es1 es2.
          es = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2
          \<and> (to_cfg c1) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1
          \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    using cfg_path_Seq_split[OF c1 c2_0 p] compile_fresh[OF c1]
    by auto
next
  assume "\<exists>es1 es2.
          es = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2
          \<and> (to_cfg c1) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1
          \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
  then obtain es1 es2 where
        es_eq: "es = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2"
    and p1: "(to_cfg c1) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1"
    and p2: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
    by blast
    have c2_n: "compile c2 n1 =
                (n20 + n1, en20 + n1, ex20 + n1, offset_edges n1 E20)"
      using compile_from_0_offsets[OF c2_0, of n1] by simp
    have Eseq: "edges (to_cfg (c1 ;; c2)) =
                E1 \<union> {(ex1, EA_Nop, en20 + n1)} \<union> offset_edges n1 E20"
      using cfg_edges_entry_exit_Seq[OF c1 c2_n] by auto
    have sub_c1: "edges (to_cfg c1) \<subseteq> edges (to_cfg (c1 ;; c2))"
      unfolding to_cfg_mk[OF c1] using Eseq by auto
    have es1_in: "(to_cfg (c1 ;; c2)) \<turnstile> en1 \<longrightarrow>\<^bsub>es1\<^esub> ex1"
      using p1 sub_c1 by blast
    have bridge: "(to_cfg (c1 ;; c2)) \<turnstile> ex1 \<longrightarrow>\<^bsub>[(EA_Nop, en20 + n1)]\<^esub> (en20 + n1)"
      using Eseq by (auto)
    have sub_off: "edges (mk_cfg (en20 + n1) (ex20 + n1) (offset_edges n1 E20))
                    \<subseteq> edges (to_cfg (c1 ;; c2))"
      using Eseq by auto
    have es2_in: "(to_cfg (c1 ;; c2)) \<turnstile> (en20 + n1) \<longrightarrow>\<^bsub>(offset_path n1 es2)\<^esub> (ex20 + n1)"
      by (rule cfg_path_sub_offset_into[OF c2_0 p2 sub_off])
    show "(to_cfg (c1 ;; c2)) \<turnstile> en1 \<longrightarrow>\<^bsub>es\<^esub> (ex20 + n1)"
      using cfg_path_append[OF cfg_path_append[OF es1_in bridge] es2_in] es_eq by simp
qed

(*
  Edge classification in `to_cfg (IF b THEN c1 ELSE c2)` by source pp.
  Compound layout (compile c1 at 1, compile c2 at n10+1):
    pp 0          : entry, source of two pre-edges (Assume / AssumeNot)
    [1, n10+1)    : c1 region (offset_edges 1 E10 + source of c1-post bridge)
    [n10+1, n2)   : c2 region (offset_edges (n10+1) E20 + source of c2-post bridge)
    pp n2 = n20+(n10+1) : exit, sink (no outgoing edges)
*)

lemma compound_If_edge_src_c1:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
    and edge: "(u, a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2))"
    and u_in: "1 \<le> u" and u_lt: "u < n10 + 1"
  shows "(u, a, w) \<in> offset_edges 1 E10 \<or>
         (u = ex10 + 1 \<and> a = EA_Nop \<and> w = n20 + (n10 + 1))"
proof -
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2, of "n10 + 1"] by simp
  show ?thesis
    using cfg_edges_If_from_0[OF c1 c2] edge u_in u_lt compile_ge[OF c2_n] by force
qed

lemma compound_If_edge_src_c2:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
    and edge: "(u, a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2))"
    and u_in: "n10 + 1 \<le> u" and u_lt: "u < n20 + (n10 + 1)"
  shows "(u, a, w) \<in> offset_edges (n10 + 1) E20 \<or>
         (u = ex20 + (n10 + 1) \<and> a = EA_Nop \<and> w = n20 + (n10 + 1))"
proof -
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1, of 1] by simp
  show ?thesis
    using cfg_edges_If_from_0[OF c1 c2] edge u_in u_lt compile_fresh[OF c1_1] by force
qed

(* The compound If exit pp n2 has no outgoing edges (it is a sink). *)
lemma compound_If_no_source_n2:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
  shows "\<not> (\<exists>a w. (n20 + (n10 + 1), a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2)))"
proof -
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2, of "n10 + 1"] by simp
  show ?thesis
    using cfg_edges_If_from_0[OF c1 c2] compile_fresh[OF c1_1] compile_fresh[OF c2_n] by force
qed


(* Generic branch factor: path inside region [k, n0+k) to sink
   = offset branch-path followed by a Nop bridge to sink. *)
lemma cfg_path_If_factor_branch:
  assumes c0: "compile c 0 = (n0, en0, ex0, E0)"
    and edge_cls: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> k \<le> u \<Longrightarrow> u < n0 + k
                   \<Longrightarrow> (u, a, w) \<in> offset_edges k E0
                       \<or> (u = ex0 + k \<and> a = EA_Nop \<and> w = sink)"
    and sink_out: "n0 + k \<le> sink"
    and no_out: "\<not> (\<exists>a w. (sink, a, w) \<in> edges g)"
    and p: "g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> sink"
    and u_in: "k \<le> u" and u_lt: "u < n0 + k"
  shows "\<exists>es'. es = offset_path k es' @ [(EA_Nop, sink)]
                \<and> (to_cfg c) \<turnstile> (u - k) \<longrightarrow>\<^bsub>es'\<^esub> ex0"
  using p u_in u_lt
proof (induction es arbitrary: u)
  case Nil
  from Nil(1) have "u = sink" by (cases rule: cfg_path.cases) simp_all
  with sink_out Nil.prems(3) show ?case by simp
next
  case (Cons hd tl)
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from Cons.prems(1) hd_eq obtain
        e_g: "(u, a, w) \<in> edges g"
    and ps: "g \<turnstile> w \<longrightarrow>\<^bsub>tl\<^esub> sink"
    by (cases rule: cfg_path.cases) auto
  from edge_cls[OF e_g Cons.prems(2) Cons.prems(3)]
  consider (body) "(u, a, w) \<in> offset_edges k E0"
         | (bridge) "u = ex0 + k" "a = EA_Nop" "w = sink"
    by auto
  thus ?case
  proof cases
    case body
    from body obtain u0 w0 where
          decomp: "u = u0 + k" "w = w0 + k" "(u0, a, w0) \<in> E0"
      unfolding offset_edges_def by auto
    have w_in: "k \<le> w" using decomp(2) by simp
    have w_lt: "w < n0 + k" using compile_fresh[OF c0] decomp(2,3) by force
    from Cons.IH[OF ps w_in w_lt] obtain es' where
          tl_eq: "tl = offset_path k es' @ [(EA_Nop, sink)]"
      and pe: "(to_cfg c) \<turnstile> (w - k) \<longrightarrow>\<^bsub>es'\<^esub> ex0"
      by auto
    have edge_c: "(u - k, a, w - k) \<in> edges (to_cfg c)"
      using c0 decomp by (auto simp: to_cfg_simps)
    let ?full = "(a, w - k) # es'"
    show ?thesis
      using cfg_path.step[OF edge_c pe] tl_eq decomp(2) hd_eq
      by (rule_tac x = "?full" in exI) simp
  next
    case bridge
    have tl_empty: "tl = []"
    proof (cases tl)
      case Nil then show ?thesis by simp
    next
      case (Cons hd' tl')
      obtain a' w' where "hd' = (a', w')" by (cases hd') auto
      with ps Cons bridge(3) have "(sink, a', w') \<in> edges g"
        by (cases rule: cfg_path.cases) auto
      with no_out show ?thesis by blast
    qed
    show ?thesis
      using cfg_path.empty bridge(1) tl_empty bridge hd_eq
      by (rule_tac x = "[]" in exI) simp
  qed
qed

lemma cfg_path_If_factor_c1:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
    and p: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> (n20 + (n10 + 1))"
    and u_in: "1 \<le> u" and u_lt: "u < n10 + 1"
  shows "\<exists>es'. es = offset_path 1 es' @ [(EA_Nop, n20 + (n10 + 1))]
                \<and> (to_cfg c1) \<turnstile> (u - 1) \<longrightarrow>\<^bsub>es'\<^esub> ex10"
proof -
  have cls: "\<And>u a w. (u, a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2)) \<Longrightarrow>
                     1 \<le> u \<Longrightarrow> u < n10 + 1 \<Longrightarrow>
                     (u, a, w) \<in> offset_edges 1 E10 \<or>
                     (u = ex10 + 1 \<and> a = EA_Nop \<and> w = n20 + (n10 + 1))"
    using compound_If_edge_src_c1[OF c1 c2] by blast
  have sink_out: "n10 + 1 \<le> n20 + (n10 + 1)" by simp
  show ?thesis
    by (rule cfg_path_If_factor_branch[OF c1 cls sink_out compound_If_no_source_n2[OF c1 c2]
                                         p u_in u_lt])
qed

lemma cfg_path_If_factor_c2:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
    and p: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> (n20 + (n10 + 1))"
    and u_in: "n10 + 1 \<le> u" and u_lt: "u < n20 + (n10 + 1)"
  shows "\<exists>es'. es = offset_path (n10 + 1) es' @ [(EA_Nop, n20 + (n10 + 1))]
                \<and> (to_cfg c2) \<turnstile> (u - (n10 + 1)) \<longrightarrow>\<^bsub>es'\<^esub> ex20"
proof -
  have cls: "\<And>u a w. (u, a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2)) \<Longrightarrow>
                     n10 + 1 \<le> u \<Longrightarrow> u < n20 + (n10 + 1) \<Longrightarrow>
                     (u, a, w) \<in> offset_edges (n10 + 1) E20 \<or>
                     (u = ex20 + (n10 + 1) \<and> a = EA_Nop \<and> w = n20 + (n10 + 1))"
    using compound_If_edge_src_c2[OF c1 c2] by blast
  show ?thesis
    by (rule cfg_path_If_factor_branch[OF c2 cls le_refl compound_If_no_source_n2[OF c1 c2]
                                         p u_in u_lt])
qed

(*
  Strong If path split.  A path in to_cfg (IF b THEN c1 ELSE c2) from
  the compound entry 0 to the compound exit n2 begins with one of the
  two pre-edges (Assume b / AssumeNot b) and ends with the matching
  post-Nop bridge.
*)
lemma cfg_path_If_split:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
    and p: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n20 + (n10 + 1))"
  shows "(\<exists>es1. es = (EA_Assume b, en10 + 1)
                     # offset_path 1 es1
                     @ [(EA_Nop, n20 + (n10 + 1))]
              \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10)
       \<or> (\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1))
                     # offset_path (n10 + 1) es2
                     @ [(EA_Nop, n20 + (n10 + 1))]
              \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20)"
proof -
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2, of "n10 + 1"] by simp
  note Eif = cfg_edges_If_from_0[OF c1 c2]
  have es_ne: "es \<noteq> []" using p by (auto elim: cfg_path.cases)
  then obtain hd tl where es_cons: "es = hd # tl" by (cases es) auto
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from p es_cons hd_eq obtain
        e_first: "(0, a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2))"
    and ps: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> w \<longrightarrow>\<^bsub>tl\<^esub> (n20 + (n10 + 1))"
    by (cases rule: cfg_path.cases) auto
  have e_cases:
    "(a = EA_Assume b \<and> w = en10 + 1) \<or> (a = EA_AssumeNot b \<and> w = en20 + (n10 + 1))"
    using e_first Eif compile_ge[OF c1_1] compile_ge[OF c2_n]
    by (force simp: offset_edges_def)
  thus ?thesis
  proof
    assume A: "a = EA_Assume b \<and> w = en10 + 1"
    hence w_eq: "w = en10 + 1" and a_eq: "a = EA_Assume b" by auto
    have w_in: "1 \<le> w" "w < n10 + 1" using w_eq compile_fresh[OF c1_1] by auto
    from cfg_path_If_factor_c1[OF c1 c2 ps w_in(1) w_in(2)] obtain es1 where
          tl_eq: "tl = offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]"
      and pc1: "(to_cfg c1) \<turnstile> (w - 1) \<longrightarrow>\<^bsub>es1\<^esub> ex10"
      by blast
    have pc1': "(to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10" using pc1 w_eq by simp
    have es_eq: "es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]"
      using es_cons hd_eq a_eq w_eq tl_eq by simp
    show ?thesis using es_eq pc1' by blast
  next
    assume A: "a = EA_AssumeNot b \<and> w = en20 + (n10 + 1)"
    hence w_eq: "w = en20 + (n10 + 1)" and a_eq: "a = EA_AssumeNot b" by auto
    have w_in: "n10 + 1 \<le> w" "w < n20 + (n10 + 1)"
      using w_eq compile_ge[OF c2_n] compile_fresh[OF c2_n] by auto
    from cfg_path_If_factor_c2[OF c1 c2 ps w_in(1) w_in(2)] obtain es2 where
          tl_eq: "tl = offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]"
      and pc2: "(to_cfg c2) \<turnstile> (w - (n10 + 1)) \<longrightarrow>\<^bsub>es2\<^esub> ex20"
      by blast
    have pc2': "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20" using pc2 w_eq by simp
    have es_eq: "es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]"
      using es_cons hd_eq a_eq w_eq tl_eq by simp
    show ?thesis using es_eq pc2' by blast
  qed
qed


lemma cfg_path_singleton_edge:
  assumes E: "edges g = {(u0, a0, v0)}"
    and ne: "u0 \<noteq> v0"
    and p: "g \<turnstile> u0 \<longrightarrow>\<^bsub>es\<^esub> v0"
  shows "es = [(a0, v0)]"
proof (cases es)
  case Nil
  with p ne show ?thesis by (auto elim: cfg_path.cases)
next
  case (Cons hd tl)
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from Cons hd_eq p obtain
        edge: "(u0, a, w) \<in> edges g"
    and p_tl: "g \<turnstile> w \<longrightarrow>\<^bsub>tl\<^esub> v0"
    by (auto elim: cfg_path.cases)
  from edge E have aw: "a = a0" "w = v0" by auto
  have "tl = []"
  proof (rule ccontr)
    assume "tl \<noteq> []"
    then obtain hd' tl' where tl_eq: "tl = hd' # tl'" by (cases tl) auto
    obtain a' w' where hd'_eq: "hd' = (a', w')" by (cases hd') auto
    from p_tl tl_eq hd'_eq aw(2) obtain edge': "(v0, a', w') \<in> edges g"
      by (auto elim: cfg_path.cases)
    from edge' E ne show False by auto
  qed
  with Cons hd_eq aw show ?thesis by simp
qed


lemma compound_While_edge_src_body:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
    and edge: "(u, aa, w) \<in> edges (to_cfg (WHILE b DO c))"
    and u_ge: "1 \<le> u" and u_lt: "u < n10 + 1"
  shows "(u, aa, w) \<in> offset_edges 1 E10 \<or> (u = ex10 + 1 \<and> aa = EA_Nop \<and> w = 0)"
  using edge u_ge u_lt cfg_edges_While_from_0[OF c0] by force

lemma compound_While_edge_into_exit:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
    and e: "(mid, aa, v) \<in> edges (to_cfg (WHILE b DO c))"
    and v: "v = n10 + 1"
  shows "mid = 0 \<and> aa = EA_AssumeNot b"
proof -
  note Ew = cfg_edges_While_from_0[OF c0]
  from compile_fresh[OF c0] have E10_bd: "\<forall>e \<in> E10. snd (snd e) < n10" by fastforce
  have off_no: "\<And>x ay y. (x, ay, y) \<in> offset_edges 1 E10 \<Longrightarrow> y \<le> n10"
    using E10_bd unfolding offset_edges_def by force
  from compile_fresh[OF c0] have assume_b_ne: "en10 + 1 \<noteq> n10 + 1" by simp
  show ?thesis using e v Ew off_no assume_b_ne by force
qed

(* The compound While exit pp n10+1 has no outgoing edges (it is a sink). *)
lemma compound_While_no_source_n1:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
  shows "\<not> (\<exists>a w. (n10 + 1, a, w) \<in> edges (to_cfg (WHILE b DO c)))"
proof -
  note Ew = cfg_edges_While_from_0[OF c0]
  from compile_fresh[OF c0] have E1_src_lt: "\<forall>e \<in> offset_edges 1 E10. fst e < n10 + 1"
    by (fastforce simp: offset_edges_def)
  from compile_fresh[OF c0] have ex1_lt: "ex10 + 1 < n10 + 1" by simp
  show ?thesis using Ew E1_src_lt ex1_lt by force
qed

lemma compound_While_edges_from_zero:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
    and e: "(0, a, w) \<in> edges (to_cfg (WHILE b DO c))"
  shows "a = EA_Assume b \<and> w = en10 + 1 \<or> a = EA_AssumeNot b \<and> w = n10 + 1"
  using e cfg_edges_While_from_0[OF c0] by (force simp: offset_edges_def)

lemma cfg_path_While_split_trailing_exit:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
    and p: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n10 + 1)"
    and ne: "es \<noteq> []"
  shows "\<exists>es_pre. es = es_pre @ [(EA_AssumeNot b, n10 + 1)]
          \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_pre\<^esub> 0"
proof -
  from cfg_path_split_last[OF p ne] obtain es_pre mid aa where
        spl: "es = es_pre @ [(aa, n10 + 1)]"
    and p_pre: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_pre\<^esub> mid"
    and last_e: "(mid, aa, n10 + 1) \<in> edges (to_cfg (WHILE b DO c))"
    by blast
  from compound_While_edge_into_exit[OF c0 last_e] have mid_aa: "mid = 0 \<and> aa = EA_AssumeNot b"
    by simp
  show ?thesis
    using spl p_pre mid_aa by blast
qed

lemma cfg_path_While_loop_first_edge:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
    and p: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (0 :: pp)"
    and ne: "es \<noteq> []"
  obtains tl where "es = (EA_Assume b, en10 + 1) # tl"
    and "(to_cfg (WHILE b DO c)) \<turnstile> (en10 + 1) \<longrightarrow>\<^bsub>tl\<^esub> 0"
proof -
  obtain aa w tl where es_eq: "es = (aa, w) # tl"
    using ne p by auto
  from p es_eq obtain
        e0: "(0, aa, w) \<in> edges (to_cfg (WHILE b DO c))"
    and ps: "(to_cfg (WHILE b DO c)) \<turnstile> w \<longrightarrow>\<^bsub>tl\<^esub> 0"
    by (cases rule: cfg_path.cases) auto
  have not_assume_not: "\<not> (aa = EA_AssumeNot b \<and> w = n10 + 1)"
  proof
    assume H: "aa = EA_AssumeNot b \<and> w = n10 + 1"
    with ps have sink_path: "(to_cfg (WHILE b DO c)) \<turnstile> (n10 + 1) \<longrightarrow>\<^bsub>tl\<^esub> 0" by simp
    from cfg_path_no_out_empty[OF sink_path compound_While_no_source_n1[OF c0]]
    show False by simp
  qed
  from e0 compound_While_edges_from_zero[OF c0] not_assume_not
  have aw: "aa = EA_Assume b \<and> w = en10 + 1" by auto
  from es_eq aw ps that show thesis by simp
qed

lemma cfg_path_While_u_body_to_zero_split:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
    and u_ge: "1 \<le> u" and u_lt: "u < n10 + 1"
    and p: "(to_cfg (WHILE b DO c)) \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> (0 :: pp)"
  shows "\<exists>es_body es_rest.
      es = offset_path 1 es_body @ [(EA_Nop, 0)] @ es_rest
      \<and> (to_cfg c) \<turnstile> (u - 1) \<longrightarrow>\<^bsub>es_body\<^esub> ex10
      \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> 0"
  using p u_ge u_lt
proof (induction es arbitrary: u)
  case Nil
  then have "u = (0::pp)" by (cases rule: cfg_path.cases) simp_all
  with Nil.prems(2) show ?case by simp
next
  case (Cons hd tl)
  obtain aa w where hd_eq: "hd = (aa, w)" by (cases hd) auto
  from Cons.prems(1) hd_eq obtain
        e_compound: "(u, aa, w) \<in> edges (to_cfg (WHILE b DO c))"
    and ps: "(to_cfg (WHILE b DO c)) \<turnstile> w \<longrightarrow>\<^bsub>tl\<^esub> 0"
    by (cases rule: cfg_path.cases) auto
  from compound_While_edge_src_body[OF c0 e_compound Cons.prems(2) Cons.prems(3)]
  consider (body) "(u, aa, w) \<in> offset_edges 1 E10"
         | (backa) "u = ex10 + 1" "aa = EA_Nop" "w = 0"
    by auto
  thus ?case
  proof cases
    case body
    from body obtain u0 w0 where
          decomp: "u = u0 + 1" "w = w0 + 1" "(u0, aa, w0) \<in> E10"
      unfolding offset_edges_def by auto
    have w_ge: "1 \<le> w" using decomp(2) by simp
    have w_lt: "w < n10 + 1"
      using compile_fresh[OF c0] decomp(1,3)
      using decomp(2) by auto  
    from Cons.IH[OF ps w_ge w_lt] obtain es_body es_rest where
          tl_eq: "tl = offset_path 1 es_body @ [(EA_Nop, 0)] @ es_rest"
      and pe1: "(to_cfg c) \<turnstile> (w - 1) \<longrightarrow>\<^bsub>es_body\<^esub> ex10"
      and p0: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> 0"
      by blast
    have toc_edges: "edges (to_cfg c) = E10"
      using c0 by (simp add: to_cfg_simps)
    have edge_c1: "(u - 1, aa, w - 1) \<in> edges (to_cfg c)"
      using toc_edges decomp by simp
    let ?esb = "(aa, w - 1) # es_body"
    have p_body: "(to_cfg c) \<turnstile> (u - 1) \<longrightarrow>\<^bsub>?esb\<^esub> ex10"
      by (rule cfg_path.step[OF edge_c1 pe1])
    have list_eq: "(aa, w) # tl = offset_path 1 ?esb @ [(EA_Nop, 0)] @ es_rest"
      using tl_eq decomp(2) by simp
    show ?thesis
      using list_eq p_body p0 hd_eq by blast
  next
    case backa
    have p_body: "(to_cfg c) \<turnstile> (u - 1) \<longrightarrow>\<^bsub>[]\<^esub> ex10"
      using backa(1) by (simp add: cfg_path.empty)
    have list_eq: "(aa, w) # tl = offset_path 1 [] @ [(EA_Nop, 0)] @ tl"
      using backa by simp
    show ?thesis
      using list_eq p_body ps hd_eq
      using backa(3) by blast 
  qed
qed

lemma cfg_path_While_loop_peel:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
    and p: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (0 :: pp)"
    and ne: "es \<noteq> []"
  shows "\<exists>es_body es_rest.
      es = [(EA_Assume b, en10 + 1)] @ offset_path 1 es_body @ [(EA_Nop, 0)] @ es_rest
      \<and> (to_cfg c) \<turnstile> en10 \<longrightarrow>\<^bsub>es_body\<^esub> ex10
      \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> 0"
proof -
  from cfg_path_While_loop_first_edge[OF c0 p ne] obtain tl where
        es_eq: "es = (EA_Assume b, en10 + 1) # tl"
    and p_tl: "(to_cfg (WHILE b DO c)) \<turnstile> (en10 + 1) \<longrightarrow>\<^bsub>tl\<^esub> 0"
    by blast
  from compile_fresh[OF c0] have en_lt: "en10 < n10" by simp
  have u_ge: "1 \<le> en10 + 1" and u_lt: "en10 + 1 < n10 + 1" using en_lt by simp+
  from cfg_path_While_u_body_to_zero_split[OF c0 u_ge u_lt p_tl] obtain es_body es_rest where
        tl_eq: "tl = offset_path 1 es_body @ [(EA_Nop, 0)] @ es_rest"
    and pc: "(to_cfg c) \<turnstile> en10 \<longrightarrow>\<^bsub>es_body\<^esub> ex10"
    and pr: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> 0"
    by auto
  have "es = [(EA_Assume b, en10 + 1)] @ offset_path 1 es_body @ [(EA_Nop, 0)] @ es_rest"
    using es_eq tl_eq by simp
  thus ?thesis using pc pr by blast
qed

(* Phase 7: bidirectional compound path characterizations (after split/peel lemmas). *)

lemma cfg_path_If_iff:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
  shows "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n20 + (n10 + 1))
         \<longleftrightarrow>
         ((\<exists>es1. es = (EA_Assume b, en10 + 1) # offset_path 1 es1
                        @ [(EA_Nop, n20 + (n10 + 1))]
              \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10)
          \<or> (\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1))
                        # offset_path (n10 + 1) es2
                        @ [(EA_Nop, n20 + (n10 + 1))]
              \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20))"
proof (intro iffI)
  assume p: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n20 + (n10 + 1))"
  show "((\<exists>es1. es = (EA_Assume b, en10 + 1) # offset_path 1 es1
                        @ [(EA_Nop, n20 + (n10 + 1))]
              \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10)
          \<or> (\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1))
                        # offset_path (n10 + 1) es2
                        @ [(EA_Nop, n20 + (n10 + 1))]
              \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20))"
    using cfg_path_If_split[OF c1 c2 p] by blast
next
  assume rhs: "((\<exists>es1. es = (EA_Assume b, en10 + 1) # offset_path 1 es1
                        @ [(EA_Nop, n20 + (n10 + 1))]
              \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10)
          \<or> (\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1))
                        # offset_path (n10 + 1) es2
                        @ [(EA_Nop, n20 + (n10 + 1))]
              \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20))"
  show "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n20 + (n10 + 1))"
  proof -
    note Eif = cfg_edges_If_from_0[OF c1 c2]
    from rhs show ?thesis
    proof (elim disjE)
      assume left: "\<exists>es1. es = (EA_Assume b, en10 + 1) # offset_path 1 es1
                        @ [(EA_Nop, n20 + (n10 + 1))]
                    \<and> (to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10"
      then obtain es1 where H: "es = (EA_Assume b, en10 + 1) # offset_path 1 es1
                        @ [(EA_Nop, n20 + (n10 + 1))]"
        and p1: "(to_cfg c1) \<turnstile> en10 \<longrightarrow>\<^bsub>es1\<^esub> ex10"
        by blast
      have es1_in: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> (en10 + 1) \<longrightarrow>\<^bsub>(offset_path 1 es1)\<^esub> (ex10 + 1)"
        by (rule cfg_path_sub_offset_into[OF c1 p1]) (auto simp: Eif)
      have head: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>[(EA_Assume b, en10 + 1)]\<^esub> (en10 + 1)"
        using Eif by (auto)
      have tail: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> (ex10 + 1) \<longrightarrow>\<^bsub>[(EA_Nop, n20 + (n10 + 1))]\<^esub> (n20 + (n10 + 1))"
        using Eif by (auto)
      show ?thesis
        using cfg_path_append[OF cfg_path_append[OF head es1_in] tail] H by simp
    next
      assume right: "\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1)) #
                        offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]
                    \<and> (to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
      then obtain es2 where H: "es = (EA_AssumeNot b, en20 + (n10 + 1)) #
                        offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]"
        and p2: "(to_cfg c2) \<turnstile> en20 \<longrightarrow>\<^bsub>es2\<^esub> ex20"
        by blast
      have es2_in: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> (en20 + (n10 + 1)) \<longrightarrow>\<^bsub>(offset_path (n10 + 1) es2)\<^esub> (ex20 + (n10 + 1))"
        by (rule cfg_path_sub_offset_into[OF c2 p2]) (auto simp: Eif)
      have head: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> 0 \<longrightarrow>\<^bsub>[(EA_AssumeNot b, en20 + (n10 + 1))]\<^esub> (en20 + (n10 + 1))"
        using Eif by (auto)
      have tail: "(to_cfg (IF b THEN c1 ELSE c2)) \<turnstile> (ex20 + (n10 + 1)) \<longrightarrow>\<^bsub>[(EA_Nop, n20 + (n10 + 1))]\<^esub> (n20 + (n10 + 1))"
        using Eif by (auto)
      show ?thesis
        using cfg_path_append[OF cfg_path_append[OF head es2_in] tail] H by simp
    qed
  qed
qed

lemma cfg_path_While_exit_iff:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
  shows "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n10 + 1)
         \<longleftrightarrow>
         (es \<noteq> [] \<and> (\<exists>es_pre. es = es_pre @ [(EA_AssumeNot b, n10 + 1)]
              \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_pre\<^esub> 0))"
proof (intro iffI)
  assume p: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n10 + 1)"
  have ne: "es \<noteq> []"
    using p by (auto elim: cfg_path.cases)
  show "es \<noteq> [] \<and> (\<exists>es_pre. es = es_pre @ [(EA_AssumeNot b, n10 + 1)]
              \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_pre\<^esub> 0)"
    using ne cfg_path_While_split_trailing_exit[OF c0 p ne] by blast
next
  assume rhs: "es \<noteq> [] \<and> (\<exists>es_pre. es = es_pre @ [(EA_AssumeNot b, n10 + 1)]
              \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_pre\<^esub> 0)"
  then obtain es_pre where es_eq: "es = es_pre @ [(EA_AssumeNot b, n10 + 1)]"
    and p0: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_pre\<^esub> 0" by auto
  have step: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>[(EA_AssumeNot b, n10 + 1)]\<^esub> (n10 + 1)"
    using cfg_edges_While_from_0[OF c0] by auto
  show "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> (n10 + 1)"
    using cfg_path_append[OF p0 step] es_eq by simp
qed

lemma cfg_path_While_loop_iff:
  assumes c0: "compile c 0 = (n10, en10, ex10, E10)"
  shows "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> 0
         \<longleftrightarrow>
         (es = [] \<or> (\<exists>es_body es_rest.
              es = [(EA_Assume b, en10 + 1)] @ offset_path 1 es_body @ [(EA_Nop, 0)] @ es_rest
              \<and> (to_cfg c) \<turnstile> en10 \<longrightarrow>\<^bsub>es_body\<^esub> ex10
              \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> 0))"
proof (intro iffI)
  assume p: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> 0"
  show "es = [] \<or> (\<exists>es_body es_rest.
              es = [(EA_Assume b, en10 + 1)] @ offset_path 1 es_body @ [(EA_Nop, 0)] @ es_rest
              \<and> (to_cfg c) \<turnstile> en10 \<longrightarrow>\<^bsub>es_body\<^esub> ex10
              \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> 0)"
  proof (cases es)
    case Nil then show ?thesis by simp
  next
    case (Cons hd tl)
    from cfg_path_While_loop_peel[OF c0 p] show ?thesis
      using Cons by (auto intro!: disjI2)
  qed
next
  assume rhs: "es = [] \<or> (\<exists>es_body es_rest.
              es = [(EA_Assume b, en10 + 1)] @ offset_path 1 es_body @ [(EA_Nop, 0)] @ es_rest
              \<and> (to_cfg c) \<turnstile> en10 \<longrightarrow>\<^bsub>es_body\<^esub> ex10
              \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> 0)"
  from rhs show "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es\<^esub> 0"
  proof (elim disjE)
    assume eq: "es = []"
    show ?thesis by (simp add: eq cfg_path.empty)
  next
    assume "\<exists>es_body es_rest.
              es = [(EA_Assume b, en10 + 1)] @ offset_path 1 es_body @ [(EA_Nop, 0)] @ es_rest
              \<and> (to_cfg c) \<turnstile> en10 \<longrightarrow>\<^bsub>es_body\<^esub> ex10
              \<and> (to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> 0"
    then obtain es_body es_rest where
        es_eq: "es = [(EA_Assume b, en10 + 1)] @ offset_path 1 es_body @ [(EA_Nop, 0)] @ es_rest"
      and pb: "(to_cfg c) \<turnstile> en10 \<longrightarrow>\<^bsub>es_body\<^esub> ex10"
      and pr: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>es_rest\<^esub> 0"
      by blast
    note Ew = cfg_edges_While_from_0[OF c0]
    have body_in: "(to_cfg (WHILE b DO c)) \<turnstile> (en10 + 1) \<longrightarrow>\<^bsub>(offset_path 1 es_body)\<^esub> (ex10 + 1)"
      by (rule cfg_path_sub_offset_into[OF c0 pb]) (auto simp: Ew)
    have head: "(to_cfg (WHILE b DO c)) \<turnstile> 0 \<longrightarrow>\<^bsub>[(EA_Assume b, en10 + 1)]\<^esub> (en10 + 1)"
      using Ew by auto
    have loopback: "(to_cfg (WHILE b DO c)) \<turnstile> (ex10 + 1) \<longrightarrow>\<^bsub>[(EA_Nop, 0)]\<^esub> 0"
      using Ew by auto
    show ?thesis
      using cfg_path_append[OF cfg_path_append[OF cfg_path_append[OF head body_in] loopback] pr]
        es_eq by simp
  qed
qed

end
