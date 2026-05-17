theory IMP2_to_CFG
  imports CFG_Def IMP2_Semantics
begin

(*
  IMP2 -- Translation to CFG.

  compile c n  returns  (n', entry, exit, edges)  where:
    n    = fresh program-point counter on entry
    n'   = fresh counter on exit (all pp's allocated are in [n, n'))
    entry, exit  are the entry and exit nodes for c's sub-graph
    edges        is the set of CFG edges for c

  Translation scheme (standard structured-program CFG):
    SKIP           : entry -[Nop]-> exit
    x ::= a        : entry -[Assign x a]-> exit
    c1 ;; c2       : c1_entry ---c1---> c1_exit -[Nop]-> c2_entry ---c2---> c2_exit
    IF b THEN c1 ELSE c2 :
                     entry -[Assume b]-> c1_entry ---c1---> c1_exit -[Nop]-> exit
                     entry -[AssumeNot b]-> c2_entry ---c2---> c2_exit -[Nop]-> exit
    WHILE b DO c   :
                     head -[Assume b]-> body_entry ---c---> body_exit -[Nop]-> head  (back)
                     head -[AssumeNot b]-> exit
*)

(* ── Compile Function ─────────────────────────────────────────── *)

fun compile :: "com => nat => nat * pp * pp * (pp * edge_action * pp) set"
where
    "compile SKIP n =
       (n + 2, n, n + 1, {(n, EA_Nop, n + 1)})"

  | "compile (x ::= a) n =
       (n + 2, n, n + 1, {(n, EA_Assign x a, n + 1)})"

  | "compile (c1 ;; c2) n =
       (let (n1, en1, ex1, E1) = compile c1 n;
            (n2, en2, ex2, E2) = compile c2 n1
        in  (n2, en1, ex2, E1 Un {(ex1, EA_Nop, en2)} Un E2))"

  | "compile (IF b THEN c1 ELSE c2) n =
       (let en  = n;
            (n1, en1, ex1, E1) = compile c1 (n + 1);
            (n2, en2, ex2, E2) = compile c2 n1;
            xn  = n2
        in  (n2 + 1, en, xn,
             {(en, EA_Assume b,    en1),
              (en, EA_AssumeNot b, en2)}
             Un E1 Un E2
             Un {(ex1, EA_Nop, xn),
                 (ex2, EA_Nop, xn)}))"

  | "compile (WHILE b DO c) n =
       (let head = n;
            (n1, en1, ex1, E1) = compile c (n + 1);
            xn  = n1
        in  (n1 + 1, head, xn,
             {(head, EA_Assume b,    en1),
              (head, EA_AssumeNot b, xn)}
             Un E1
             Un {(ex1, EA_Nop, head)}))"

(* ── Top-Level Wrapper ────────────────────────────────────────── *)

definition to_cfg :: "com => cfg" where
  "to_cfg c =
     (let (_, en, ex, E) = compile c 0
      in  (| cfg_entry = en, cfg_exit = ex, cfg_edges = E |))"

(* ── Freshness: Allocated pp's Are Disjoint From Counter ──────── *)

lemma compile_counter_mono:
  "compile c n = (n', en, ex, E) \<Longrightarrow> n < n'"
proof (induct c arbitrary: n n' en ex E rule: com.induct)
  case SKIP
  then show ?case
    using SKIP.prems by (fastforce simp add: compile.simps)
next
  case (Assign x a)
  then show ?case
    using Assign.prems by (fastforce simp add: compile.simps)
next
  case (Seq c1 c2)
  from Seq.prems obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2"
    by (simp add: compile.simps Let_def split: prod.splits)
  have "n < n1"
    using Seq.hyps(1)[OF c1] .
  also have "n1 < n2"
    using Seq.hyps(2)[OF c2] .
  finally show ?case
    using n' by simp
next
  case (If b c1 c2)
  from If.prems obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 (n + 1) = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2 + 1"
    by (simp add: compile.simps Let_def split: prod.splits)
  have "n + 1 < n1"
    using If.hyps(1)[OF c1] by simp
  then have "n < n1"
    by simp
  also have "n1 < n2"
    using If.hyps(2)[OF c2] .
  finally have "n < n2" .
  then show ?case
    using n' by simp
next
  case (While b c)
  from While.prems obtain n1 en1 ex1 E1 where
    c: "compile c (n + 1) = (n1, en1, ex1, E1)"
    and n': "n' = n1 + 1"
    by (simp add: compile.simps Let_def split: prod.splits)
  have "n + 1 < n1"
    using While.hyps[OF c] by simp
  then show ?case
    using n' by linarith
qed

(* Split \<forall> over A \<union> {a} \<union> B keeps automation on tiny goals (no deep blast on big unions). *)
lemma ball_union3:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "\<forall>e\<in>A. P e" and "P a" and "\<forall>e\<in>B. P e"
  shows "\<forall>e\<in>A \<union> {a} \<union> B. P e"
  using assms by auto

lemma compile_fresh:
  "compile c n = (n', en, ex, E) \<Longrightarrow>
   (\<forall>e \<in> E. fst e < n' \<and> snd (snd e) < n') \<and> en < n' \<and> ex < n' \<and> n \<le> n'"
proof (induct c arbitrary: n n' en ex E rule: com.induct)
  case SKIP
  show ?case
    using SKIP.prems by (fastforce simp add: compile.simps)
next
  case (Assign x a)
  show ?case
    using Assign.prems by (fastforce simp add: compile.simps)
next
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2" and en: "en = en1" and ex: "ex = ex2"
    and E: "E = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    by (simp add: compile.simps Let_def split: prod.splits)
  have IH1: "(\<forall>e\<in>E1. fst e < n1 \<and> snd (snd e) < n1) \<and> en1 < n1 \<and> ex1 < n1 \<and> n \<le> n1"
    using Seq.hyps(1)[OF c1] .
  have IH2: "(\<forall>e\<in>E2. fst e < n2 \<and> snd (snd e) < n2) \<and> en2 < n2 \<and> ex2 < n2 \<and> n1 \<le> n2"
    using Seq.hyps(2)[OF c2] .
  have n1n2: "n1 < n2"
    using compile_counter_mono[OF c2] .
  show ?case
    unfolding en ex E n' using IH1 IH2 n1n2
    by auto
next
  case (If b c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 (n + 1) = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2 + 1"
    by (simp add: compile.simps Let_def split: prod.splits)
  from If.prems have en: "en = n" and ex: "ex = n2"
    using c1 c2 by (auto split: prod.splits)

  have E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
          \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    using If.prems c1 c2 by (auto split: prod.splits)

  have IH1: "(\<forall>e\<in>E1. fst e < n1 \<and> snd (snd e) < n1) \<and> en1 < n1 \<and> ex1 < n1 \<and> n + 1 \<le> n1"
    using If.hyps(1)[OF c1] .
  have IH2: "(\<forall>e\<in>E2. fst e < n2 \<and> snd (snd e) < n2) \<and> en2 < n2 \<and> ex2 < n2 \<and> n1 \<le> n2"
    using If.hyps(2)[OF c2] .
  have "n < n2"
  proof -
    have "n + 1 < n1"
      using compile_counter_mono[OF c1] by simp
    moreover have "n1 < n2"
      using compile_counter_mono[OF c2] by simp
    ultimately show ?thesis
      by linarith
  qed
  then have "n < n'" "n2 < n'"
    unfolding n' by simp_all
  show ?case
    unfolding en ex E n' using IH1 IH2 \<open>n < n'\<close> \<open>n2 < n'\<close>
    by auto
next
  case (While b c)
  then obtain n1 en1 ex1 E1 where
    c: "compile c (n + 1) = (n1, en1, ex1, E1)"
    and n': "n' = n1 + 1" and en: "en = n" and ex: "ex = n1"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, n)}"
    apply (auto)
    by (smt (verit) Pair_inject case_prod_unfold prod.collapse)

  have IH: "(\<forall>e\<in>E1. fst e < n1 \<and> snd (snd e) < n1) \<and> en1 < n1 \<and> ex1 < n1 \<and> n + 1 \<le> n1"
    using While.hyps[OF c] .
  have "n < n1"
    using compile_counter_mono[OF c] by simp
  show ?case
    unfolding en ex E n' using IH \<open>n < n1\<close>
    by auto
qed

(* All allocated pp's are >= n (nothing reuses old counters). *)
lemma compile_ge:
  "compile c n = (n', en, ex, E) \<Longrightarrow>
   (\<forall>e \<in> E. fst e \<ge> n \<and> snd (snd e) \<ge> n) \<and> en \<ge> n \<and> ex \<ge> n"
proof (induct c arbitrary: n n' en ex E rule: com.induct)
  case SKIP
  show ?case
    using SKIP.prems by (fastforce simp add: compile.simps)
next
  case (Assign x a)
  show ?case
    using Assign.prems by (fastforce simp add: compile.simps)
next
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2" and en: "en = en1" and ex: "ex = ex2"
    and E: "E = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    by (simp add: compile.simps Let_def split: prod.splits)
  have IH1: "(\<forall>e\<in>E1. n \<le> fst e \<and> n \<le> snd (snd e)) \<and> n \<le> en1 \<and> n \<le> ex1"
    using Seq.hyps(1)[OF c1] by simp
  have IH2: "(\<forall>e\<in>E2. n1 \<le> fst e \<and> n1 \<le> snd (snd e)) \<and> n1 \<le> en2 \<and> n1 \<le> ex2"
    using Seq.hyps(2)[OF c2] by simp
  have nn1: "n \<le> n1"
    using compile_counter_mono[OF c1] by linarith
  have ballE: "\<forall>e\<in>E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2. n \<le> fst e \<and> n \<le> snd (snd e)"
  proof (rule ball_union3)
    show "\<forall>e\<in>E1. n \<le> fst e \<and> n \<le> snd (snd e)"
      using IH1 by simp
  next
    show "n \<le> fst (ex1, EA_Nop, en2) \<and> n \<le> snd (snd (ex1, EA_Nop, en2))"
      using IH1 IH2 nn1 by simp
  next
    show "\<forall>e\<in>E2. n \<le> fst e \<and> n \<le> snd (snd e)"
    proof (rule ballI)
      fix e assume "e \<in> E2"
      have ge1: "n1 \<le> fst e" and ge2: "n1 \<le> snd (snd e)"
        using IH2 \<open>e \<in> E2\<close> by simp_all
      with nn1 show "n \<le> fst e \<and> n \<le> snd (snd e)"
        by linarith

    qed
  qed
  show ?case
    unfolding en ex E n' using ballE IH1 IH2 nn1
    by (simp add: order.trans)
next
  case (If b c1 c2)
  from If.prems obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 (n + 1) = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2 + 1" and en: "en = n" and ex: "ex = n2"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
          \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    by (fastforce split: prod.splits)

  have IH1: "(\<forall>e\<in>E1. n + 1 \<le> fst e \<and> n + 1 \<le> snd (snd e)) \<and> n + 1 \<le> en1 \<and> n + 1 \<le> ex1"
    using If.hyps(1)[OF c1] by simp
  have IH2: "(\<forall>e\<in>E2. n1 \<le> fst e \<and> n1 \<le> snd (snd e)) \<and> n1 \<le> en2 \<and> n1 \<le> ex2"
    using If.hyps(2)[OF c2] by simp
  show ?case
    unfolding en ex E n' using IH1 IH2
    apply (auto)
    apply (metis If.prems Suc_eq_plus1 compile_counter_mono less_Suc_eq_le n')
         apply (meson c1 compile_fresh dual_order.trans le_add1)
    apply (metis If.prems Suc_eq_plus1 compile_counter_mono less_Suc_eq_le n')
       apply (meson c1 compile_fresh dual_order.trans le_add1)
    apply (metis (no_types, opaque_lifting) Suc_eq_plus1_left Suc_leD add.commute c1 compile_fresh
        dual_order.trans split_pairs2)
    apply (metis (no_types, lifting) c1 compile_fresh dual_order.trans le_add1 snd_conv)
    apply (metis If.prems Suc_eq_plus1 compile_counter_mono less_Suc_eq_le n')
    done
next
  case (While b c)
  then obtain n1 en1 ex1 E1 where
    c: "compile c (n + 1) = (n1, en1, ex1, E1)"
    and n': "n' = n1 + 1" and en: "en = n" and ex: "ex = n1"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, n)}"
    by (fastforce split: prod.splits)

  have IH: "(\<forall>e\<in>E1. n + 1 \<le> fst e \<and> n + 1 \<le> snd (snd e)) \<and> n + 1 \<le> en1 \<and> n + 1 \<le> ex1"
    using While.hyps[OF c] by simp
  show ?case
    unfolding en ex E n' using IH
    apply (auto)
    apply (meson add_le_imp_le_right c compile_fresh trans_le_add1)
    apply (meson add_le_imp_le_right c compile_fresh trans_le_add1)
    done
qed

(* Shifting the fresh-program-point baseline by k shifts every allocated pp uniformly. *)

lemma compile_add_offset:
  fixes c :: com and n k n' en ex E
  assumes cmp: "compile c n = (n', en, ex, E)"
  shows "compile c (n + k) = (n' + k, en + k, ex + k, offset_edges k E)"
  using cmp
using assms proof (induct c arbitrary: n n' en ex E rule: com.induct)
  case SKIP
  then show ?case
    by (force simp: compile.simps offset_edges_def)
next
  case (Assign x a)
  then show ?case
    by (force simp: compile.simps offset_edges_def)
next
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2" and en: "en = en1" and ex: "ex = ex2"
    and E: "E = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    by (simp add: compile.simps Let_def split: prod.splits)

  obtain n1k en1k ex1k E1k where c1k: "compile c1 (n + k) = (n1k, en1k, ex1k, E1k)"
    by (cases "compile c1 (n + k)") auto
  from Seq.hyps(1)[OF c1] c1k have c12: "compile c1 (n + k) = (n1 + k, en1 + k, ex1 + k, offset_edges k E1)"
    using c1 by blast
     

  obtain n2k en2k ex2k E2k where c2k: "compile c2 (n1 + k) = (n2k, en2k, ex2k, E2k)"
    by (cases "compile c2 (n1 + k)") auto
  from Seq.hyps(2)[OF c2] c2k have c22: "compile c2 (n1 + k) = (n2 + k, en2 + k, ex2 + k, offset_edges k E2)"
    using c2 by blast
  

  show ?case
  proof -
    have "compile (c1 ;; c2) (n + k) =
        (let (n1a, en1a, ex1a, E1a) = compile c1 (n + k);
             (n2a, en2a, ex2a, E2a) = compile c2 n1a
        in (n2a, en1a, ex2a, E1a \<union> {(ex1a, EA_Nop, en2a)} \<union> E2a))"
      by (simp only: compile.simps)
    also have "\<dots> = (n2 + k, en1 + k, ex2 + k,
        offset_edges k E1 \<union> {(ex1 + k, EA_Nop, en2 + k)} \<union> offset_edges k E2)"
      by (simp add: Let_def c12 c22)
    also have "\<dots> =
        (n2 + k, en1 + k, ex2 + k, offset_edges k (E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2))"
      by (simp add: offset_edges_insert_shift)
    finally show ?case unfolding n' en ex E .
  qed
next
  case (If b c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 (n + 1) = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2 + 1"
    and en: "en = n"
    and ex: "ex = n2"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
           \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    apply (simp)
    by (smt (verit, ccfv_threshold) Pair_inject case_prod_unfold prod.collapse)
     


  obtain n1k en1k ex1k E1k where ck1: "compile c1 (n + k + 1) = (n1k, en1k, ex1k, E1k)"
    by (cases "compile c1 (n + k + 1)") auto
  from If.hyps(1)[OF c1] ck1 have ofs1:
    "n1k = n1 + k" "en1k = en1 + k" "ex1k = ex1 + k" "E1k = offset_edges k E1"
    using c1 by auto
    
  obtain n2k en2k ex2k E2k where ck2: "compile c2 (n1 + k) = (n2k, en2k, ex2k, E2k)"
    using prod_cases4 by blast
 
    
 
  from If.hyps(2)[OF c2] ck2 ofs1 have ofs2:
    "n2k = n2 + k" "en2k = en2 + k" "ex2k = ex2 + k" "E2k = offset_edges k E2"
    by (auto simp add: c2)

 

  show ?case
  proof -
    have lhs: "compile (IF b THEN c1 ELSE c2) (n + k) =
        (let (na1, ena1, exa1, Ea1) = compile c1 (n + k + 1);
             (na2, ena2, exa2, Ea2) = compile c2 na1
         in (na2 + 1, n + k, na2,
             {(n + k, EA_Assume b, ena1), (n + k, EA_AssumeNot b, ena2)}
             \<union> Ea1 \<union> Ea2 \<union> {(exa1, EA_Nop, na2), (exa2, EA_Nop, na2)}))"
      apply (auto simp add: compile.simps split:prod.splits)
      by metis
    have ck1': "compile c1 (n + k + 1) = (n1 + k, en1 + k, ex1 + k, offset_edges k E1)"
      using ck1 ofs1(1,2,3,4) by blast
 
    have ck2': "compile c2 (n1 + k) = (n2 + k, en2 + k, ex2 + k, offset_edges k E2)"
      using ck2 ofs2(1,2,3,4) by fastforce
      
    show ?thesis
      unfolding lhs n' en ex E
      using  ck1' ck2'    apply(simp)
      by (simp add: offset_edges_insert_shift)
      
  
  qed
next
  case (While b c)
  then obtain n1 en1 ex1 E1 where
    c: "compile c (n + 1) = (n1, en1, ex1, E1)"
    and n': "n' = n1 + 1"
    and en: "en = n"
    and ex: "ex = n1"
    and E:
    "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, n)}"
    by (smt (verit, del_insts) Pair_inject case_prod_unfold compile.simps(5) prod.collapse)
  
  obtain n1k en1k ex1k E1k where ck: "compile c (n + k + 1) = (n1k, en1k, ex1k, E1k)"
    by (cases "compile c (n + k + 1)") auto
  have ofs:
    "n1k = n1 + k" "en1k = en1 + k" "ex1k = ex1 + k" "E1k = offset_edges k E1"
    using While.hyps c ck apply fastforce +
  done

  show ?case
    unfolding compile.simps Let_def n' en ex E ofs
    unfolding offset_edges_def
    apply( auto)
    using ck offset_edges_def ofs(1,2,3,4) by auto
qed

lemma compile_from_0_offsets:
  assumes "compile c 0 = (n0, en0, ex0, E0)"
  shows "compile c k = (n0 + k, en0 + k, ex0 + k, offset_edges k E0)"
  using compile_add_offset[OF assms, of k] by simp

(* ── Structural Correctness Statements ───────────────────────── *)
(*
  The key correctness property:
  If compile c n = (n', en, ex, E), then for any two states s and t,
    big_step (c, s) t
  iff
    there exists a CFG path from en to ex in E that transforms s to t.
  Proved in CFG_Collecting.thy.
*)

lemma compile_entry_lt_exit:
  "compile c n = (n', en, ex, E) \<Longrightarrow> en < ex"
proof (induct c arbitrary: n n' en ex E rule: com.induct)
  case SKIP
  show ?case
    using SKIP.prems by (fastforce simp add: compile.simps)
next
  case (Assign x a)
  show ?case
    using Assign.prems by (fastforce simp add: compile.simps)
next
  case (Seq c1 c2)
  from Seq.prems obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2" and en: "en = en1" and ex: "ex = ex2"
    by (simp add: compile.simps Let_def split: prod.splits)
  have "en1 < n1"
    using compile_fresh[OF c1] by auto
  moreover have "n1 \<le> ex2"
    using compile_ge[OF c2] by auto
  ultimately show ?case
    unfolding en ex by linarith
next
  case (If b c1 c2)
  from If.prems obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 (n + 1) = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2 + 1"
    by (simp add: compile.simps Let_def split: prod.splits)
  from If.prems n' have en: "en = n" and ex: "ex = n2"
    by (auto split: prod.splits)

  have "n + 1 < n1"
    using compile_counter_mono[OF c1] by simp
  moreover have "n1 < n2"
    using compile_counter_mono[OF c2] by simp
  ultimately have "n < n2"
    by linarith
  then show ?case
    unfolding en ex by simp
next
  case (While b c)
  from While.prems obtain n1 en1 ex1 E1 where
    c: "compile c (n + 1) = (n1, en1, ex1, E1)"
    and en: "en = n" and ex: "ex = n1"
    by (simp add: compile.simps Let_def split: prod.splits)
  have "n + 1 < n1"
    using compile_counter_mono[OF c] by simp
  then show ?case
    unfolding en ex by linarith
qed

lemma compile_entry_ne_exit:
  "compile c n = (n', en, ex, E) \<Longrightarrow> en \<noteq> ex"
  by (rule less_imp_neq[OF compile_entry_lt_exit])

(* Every CFG produced by compile has finitely many edges (programs are finite). *)
lemma compile_finite:
  "compile c n = (n', en, ex, E) \<Longrightarrow> finite E"
proof (induct c arbitrary: n n' en ex E rule: com.induct)
  case SKIP
  show ?case
    using SKIP.prems by (fastforce simp add: compile.simps)
next
  case (Assign x a)
  show ?case
    using Assign.prems by (fastforce simp add: compile.simps)
next
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and E: "E = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    by (simp add: compile.simps Let_def split: prod.splits)
  show ?case
    unfolding E using Seq.hyps(1)[OF c1] Seq.hyps(2)[OF c2] by simp
next
  case (If b c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 (n + 1) = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
          \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    by (simp add: compile.simps Let_def split: prod.splits) blast
  show ?case
    unfolding E using If.hyps(1)[OF c1] If.hyps(2)[OF c2] by simp
next
  case (While b c)
  then obtain n1 en1 ex1 E1 where
    c: "compile c (n + 1) = (n1, en1, ex1, E1)"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, n)}"
    by (simp add: compile.simps Let_def split: prod.splits) blast
  show ?case
    unfolding E using While.hyps[OF c] by simp
qed

lemma to_cfg_finite: "finite (cfg_edges (to_cfg c))"
  unfolding to_cfg_def
  by (simp add: Let_def split: prod.splits) (meson compile_finite)


end
