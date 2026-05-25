theory IMP2_to_CFG
  imports CFG_Def IMP2_SmallStep
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

(* \<midarrow>\<midarrow> Compile Function \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

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

(* \<midarrow>\<midarrow> Top-Level Wrapper \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

definition to_cfg :: "com => cfg" where
  "to_cfg c =
     (let (_, en, ex, E) = compile c 0
      in  mk_cfg en ex E)"

(* \<midarrow>\<midarrow> Freshness: Allocated pp's Are Disjoint From Counter \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)


lemma compile_counter_mono:
  "compile c n = (n', en, ex, E) \<Longrightarrow> n < n'"
  apply (induction c arbitrary: n n' en ex E rule: com.induct)
  by(fastforce split:prod.splits) +

lemma compile_fresh:
  "compile c n = (n', en, ex, E) \<Longrightarrow>
    (\<forall>u a w. (u, a, w) \<in> E \<longrightarrow> u < n' \<and> w < n') \<and> en < n' \<and> ex < n' \<and> n \<le> n'"
proof (induction arbitrary: n n' en ex E rule: com.induct)
  case SKIP
  then show ?case by auto
next
  case (Assign x a)
  then show ?case by auto
next
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
        c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2" and en: "en = en1" and ex: "ex = ex2"
    and E: "E = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    by(auto split:prod.splits)
  
  have IH1: "(\<forall>e\<in>E1. fst e < n1 \<and> snd (snd e) < n1) \<and> en1 < n1 \<and> ex1 < n1 \<and> n \<le> n1"
    by (metis Seq.IH(1) c1 prod.exhaust_sel)
   
  moreover have IH2: "(\<forall>e\<in>E2. fst e < n2 \<and> snd (snd e) < n2) \<and> en2 < n2 \<and> ex2 < n2 \<and> n1 \<le> n2"
    by (metis Seq.IH(2) c2 prod.exhaust_sel)
    
  moreover have n1n2: "n1 < n2"
    using c2 compile_counter_mono by auto
    
  ultimately show ?case
    using E en ex n' by auto
next
  case (If b c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 (n + 1) = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2 + 1"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
          \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    by(auto split:prod.splits)

  have en: "en = n" and ex: "ex = n2"
    using If.prems c1 c2 by (auto)

  have IH1: "(\<forall>e\<in>E1. fst e < n1 \<and> snd (snd e) < n1) \<and> en1 < n1 \<and> ex1 < n1 \<and> n + 1 \<le> n1"
    by (metis If.IH(1) c1 prod.exhaust_sel)
 
  moreover have IH2: "(\<forall>e\<in>E2. fst e < n2 \<and> snd (snd e) < n2) \<and> en2 < n2 \<and> ex2 < n2 \<and> n1 \<le> n2"
    by (metis If.IH(2) c2 prod.exhaust_sel)

  moreover have "n < n' \<and> n2 < n'"
    using calculation(1,2) n' by linarith
  
  ultimately show ?case
    using E en ex n' by auto
next
  case (While b c)
  then obtain n1 en1 ex1 E1 where
    c: "compile c (n + 1) = (n1, en1, ex1, E1)"
    and n': "n' = n1 + 1" and en: "en = n" and ex: "ex = n1"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, n)}"
    by(fastforce split:prod.splits)
  
  have IH: "(\<forall>e\<in>E1. fst e < n1 \<and> snd (snd e) < n1) \<and> en1 < n1 \<and> ex1 < n1 \<and> n + 1 \<le> n1"
    by (metis While.IH(1) c prod.exhaust_sel)

  moreover have "n < n1"
    using IH by auto

  ultimately show ?case
   using E en ex n' by auto
qed

(* All allocated pp's are >= n (nothing reuses old counters). *)
lemma compile_ge:
  "compile c n = (n', en, ex, E) \<Longrightarrow>
   (\<forall>e \<in> E. fst e \<ge> n \<and> snd (snd e) \<ge> n) \<and> en \<ge> n \<and> ex \<ge> n"
proof (induction c arbitrary: n n' en ex E rule: com.induct)
  case SKIP
  then show ?case by auto
next
  case (Assign x a)
  then show ?case by auto
next
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2" and en: "en = en1" and ex: "ex = ex2"
    and E: "E = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    by (auto simp add:split: prod.splits)

  have IH1: "(\<forall>e\<in>E1. n \<le> fst e \<and> n \<le> snd (snd e)) \<and> n \<le> en1 \<and> n \<le> ex1"
     by (metis Seq.IH(1) c1)
  moreover have IH2: "(\<forall>e\<in>E2. n1 \<le> fst e \<and> n1 \<le> snd (snd e)) \<and> n1 \<le> en2 \<and> n1 \<le> ex2"
     by (metis Seq.IH(2) c2)
  moreover have nn1: "n \<le> n1"
    using c1 compile_fresh by auto
  moreover have ballE: "\<forall>e\<in>E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2. n \<le> fst e \<and> n \<le> snd (snd e)"
    using IH1 IH2 nn1 by fastforce
 
  ultimately show ?case
    using E en ex n' by auto
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
      by (metis If.IH(1) c1)
  moreover have IH2: "(\<forall>e\<in>E2. n1 \<le> fst e \<and> n1 \<le> snd (snd e)) \<and> n1 \<le> en2 \<and> n1 \<le> ex2"
    by (metis If.IH(2) c2)

  moreover have nn1: "n \<le> n1"
    using c1 compile_counter_mono by fastforce

  moreover have ballE: "\<forall>e\<in>E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2. n \<le> fst e \<and> n \<le> snd (snd e)"
    using IH1 IH2 nn1 by fastforce

  moreover have n1_le_n2: "n1 \<le> n2"
    using c2 compile_fresh by auto  

  ultimately show ?case
  using E en ex n' by auto
  
next
  case (While b c)
  then obtain n1 en1 ex1 E1 where
    c: "compile c (n + 1) = (n1, en1, ex1, E1)"
    and n': "n' = n1 + 1" and en: "en = n" and ex: "ex = n1"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, n)}"
    by (fastforce split: prod.splits)

  have n': "n' = n1 + 1" and en: "en = n" and ex: "ex = n1"
    using While.prems c by auto

moreover have IH: "\<forall>e\<in>E1. fst e \<ge> n + 1 \<and> snd (snd e) \<ge> n + 1"
  using While.IH c by blast

  moreover have  "en1 \<ge> n + 1 \<and> ex1 \<ge> n + 1"
    using While.IH c by blast
  moreover have n_le_n1: "n < n1"
   by (meson c compile_fresh less_iff_succ_less_eq)
 
  
  ultimately show ?case
  using E en ex n' by auto

qed

(* Shifting the fresh-program-point baseline by k shifts every allocated pp uniformly. *)

lemma compile_add_offset:
  fixes c :: com and n k n' en ex E
  assumes cmp: "compile c n = (n', en, ex, E)"
  shows "compile c (n + k) = (n' + k, en + k, ex + k, offset_edges k E)"
  using cmp
proof (induct c arbitrary: n n' en ex E rule: com.induct)
  case SKIP
  then show ?case by (auto simp: offset_edges_insert_shift offset_edges_def)
next
  case (Assign x a)
  then show ?case by (auto simp: offset_edges_insert_shift offset_edges_def)
next
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2" and en: "en = en1" and ex: "ex = ex2"
    and E: "E = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    by (auto split: prod.splits)
  from Seq.hyps(1)[OF c1] have c1k:
    "compile c1 (n + k) = (n1 + k, en1 + k, ex1 + k, offset_edges k E1)" .
  from Seq.hyps(2)[OF c2] have c2k:
    "compile c2 (n1 + k) = (n2 + k, en2 + k, ex2 + k, offset_edges k E2)" .
  show ?case
    using c1k c2k unfolding n' en ex E
    by (simp add: Let_def offset_edges_insert_shift)
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
    by (fastforce split: prod.splits)
  from If.hyps(1)[OF c1] have c1k:
    "compile c1 (n + k + 1) = (n1 + k, en1 + k, ex1 + k, offset_edges k E1)"
    by (simp add: add.assoc add.commute)
  from If.hyps(2)[OF c2] have c2k:
    "compile c2 (n1 + k) = (n2 + k, en2 + k, ex2 + k, offset_edges k E2)" .
  show ?case
    using c1k c2k unfolding n' en ex E
    by (simp add: Let_def offset_edges_insert_shift)
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
  from While.hyps[OF c] have ck:
    "compile c (n + k + 1) = (n1 + k, en1 + k, ex1 + k, offset_edges k E1)"
    by (simp add: add.assoc add.commute)
  show ?case
    using ck unfolding n' en ex E
    by (simp add: Let_def offset_edges_insert_shift)
qed

lemma compile_from_0_offsets:
  assumes "compile c 0 = (n0, en0, ex0, E0)"
  shows "compile c k = (n0 + k, en0 + k, ex0 + k, offset_edges k E0)"
  using compile_add_offset[OF assms, of k] by simp

(* \<midarrow>\<midarrow> Structural Correctness Statements \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  The key correctness property:
  If compile c n = (n', en, ex, E), then for any two states s and t,
    runs_to c s t
  iff
    there exists a CFG path from en to ex in E that transforms s to t.
  Characterised by cfg_collect / path_sound in CFG_Runs_To_Bridge.thy.
*)

lemma compile_entry_lt_exit:
  "compile c n = (n', en, ex, E) \<Longrightarrow> en < ex"
proof (induct c arbitrary: n n' en ex E rule: com.induct)
  case SKIP
  show ?case
    using SKIP.prems by fastforce
next
  case (Assign x a)
  show ?case
    using Assign.prems by fastforce
next
  case (Seq c1 c2)
  from Seq.prems obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and n': "n' = n2" and en: "en = en1" and ex: "ex = ex2"
    by (simp add: Let_def split: prod.splits)
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
    by (simp add: Let_def split: prod.splits)
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
    by (simp add: Let_def split: prod.splits)
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
    using SKIP.prems by fastforce
next
  case (Assign x a)
  show ?case
    using Assign.prems by fastforce
next
  case (Seq c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 n = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and E: "E = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    by (simp add: Let_def split: prod.splits)
  show ?case
    unfolding E using Seq.hyps(1)[OF c1] Seq.hyps(2)[OF c2] by simp
next
  case (If b c1 c2)
  then obtain n1 en1 ex1 E1 n2 en2 ex2 E2 where
    c1: "compile c1 (n + 1) = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
          \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    by (simp add: Let_def split: prod.splits) blast
  show ?case
    unfolding E using If.hyps(1)[OF c1] If.hyps(2)[OF c2] by simp
next
  case (While b c)
  then obtain n1 en1 ex1 E1 where
    c: "compile c (n + 1) = (n1, en1, ex1, E1)"
    and E: "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, n)}"
    by (simp add: Let_def split: prod.splits) blast
  show ?case
    unfolding E using While.hyps[OF c] by simp
qed

lemma to_cfg_finite: "finite (edges (to_cfg c))"
  unfolding to_cfg_def
  by (simp add: Let_def split: prod.splits) (meson compile_finite)


end
