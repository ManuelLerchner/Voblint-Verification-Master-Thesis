theory Compile_Edge_Determinism
  imports Compile_Locality Compile_Invariants
begin

section \<open>Determinism of compiled intra edges\<close>

text \<open>
  A compiled program's \<open>intra\<close> relation is edge-action functional: for a fixed source and
  target node there is at most one labelling action.  This is the proof obligation
  \<open>GHOST_DOMAIN_SEEDING_MIGRATION.md\<close> section 5 identifies as needed to read a write-site
  identity directly off a trace's \<^const>\<open>path\<close> and \<^const>\<open>intra\<close>, without enriching the
  trace type with the action that fired at each step.
\<close>

subsection \<open>Source-range bound\<close>

text \<open>Every intra edge \<^const>\<open>compile\<close> emits sources at a freshly allocated statement
  inside its own counter range --- unconditionally, independent of the continuation.\<close>

lemma compile_E_src_range:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (Statement j, a, v) \<in> E \<Longrightarrow> n \<le> j \<and> j < n'"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and n': "n' = n2" and E: "E = E1 \<union> E2"
    by (auto simp: Let_def split: prod.splits)
  from Seq.prems(2) E consider (L) "(Statement j, a, v) \<in> E1" | (R) "(Statement j, a, v) \<in> E2"
    by auto
  then show ?case
  proof cases
    case L
    have L1: "n \<le> j" and L2: "j < n1" using Seq.IH(1)[OF c1 L] by auto
    show ?thesis using L1 L2 n' compile_next_id[OF c1] compile_next_id[OF c2] by linarith
  next
    case R
    have "n + csize c1 \<le> j \<and> j < n2" using Seq.IH(2)[OF c2 R] .
    then show ?thesis using n' by simp
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and n': "n' = n2"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2"
    by (auto split: prod.splits)
  from If.prems(2) E consider
      (G) "(Statement j, a, v)
             \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}"
    | (L) "(Statement j, a, v) \<in> E1" | (R) "(Statement j, a, v) \<in> E2"
    by auto
  then show ?case
  proof cases
    case G
    then have "j = n" by auto
    then show ?thesis
      using n' compile_next_id[OF c1] compile_next_id[OF c2] csize_pos[of c1] csize_pos[of c2]
      by simp
  next
    case L
    have "Suc n \<le> j \<and> j < n1" using If.IH(1)[OF c1 L] .
    then show ?thesis using n' compile_next_id[OF c2] by simp
  next
    case R
    have "n1 \<le> j \<and> j < n2" using If.IH(2)[OF c2 R] .
    then show ?thesis using n' compile_next_id[OF c1] by linarith
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 en1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and n': "n' = n1"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1"
    by (auto split: prod.splits)
  from While.prems(2) E consider
      (G) "(Statement j, a, v)
             \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)}"
    | (B) "(Statement j, a, v) \<in> E1"
    by auto
  then show ?case
  proof cases
    case G
    then have "j = n" by auto
    then show ?thesis using n' compile_next_id[OF c1] csize_pos[of c] by simp
  next
    case B
    have "Suc n \<le> j \<and> j < n1" using While.IH[OF c1 B] .
    then show ?thesis using n' by simp
  qed
qed auto

subsection \<open>Edge-action functionality, given a fresh continuation\<close>

text \<open>\<open>k_fresh k lo hi\<close> says the continuation \<open>k\<close>, if it is a \<^const>\<open>Statement\<close> at all,
  does not fall inside the counter range \<open>[lo, hi)\<close> a compile call is about to allocate.  This
  is what rules out a compiled \<^const>\<open>While\<close> guard's two branches --- one into the freshly
  allocated body entry, one into \<open>k\<close> --- accidentally coinciding.\<close>

definition k_fresh :: "cfg_node \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "k_fresh k lo hi \<longleftrightarrow> (\<forall>j. k = Statement j \<longrightarrow> \<not> (lo \<le> j \<and> j < hi))"

lemma k_fresh_mono:
  "k_fresh k lo hi \<Longrightarrow> lo \<le> lo' \<Longrightarrow> hi' \<le> hi \<Longrightarrow> k_fresh k lo' hi'"
  unfolding k_fresh_def by auto

text \<open>The node-set form of \<open>compile_E_src_range\<close>: a source lies in the fragment's own
  \<^const>\<open>Statement\<close> range.  Stated as set membership so a cross-fragment clash between two
  sibling sub-compiles is a set-disjointness fact, without naming the underlying index.\<close>

lemma compile_E_src_img:
  assumes c: "compile \<Pi> p c k n = (n', en, E, K)" and e: "(u, a, v) \<in> E"
  shows "u \<in> Statement ` {n..<n'}"
proof -
  from compile_E_shape[OF c e] obtain j where uj: "u = Statement j" by blast
  from e uj have e': "(Statement j, a, v) \<in> E" by simp
  from compile_E_src_range[OF c e'] show ?thesis using uj by auto
qed

text \<open>Given a continuation fresh for the whole fragment, \<^const>\<open>compile\<close> emits at most one
  action for a fixed source/target pair.  The continuation freshness is only ever spent at a
  \<^const>\<open>While\<close> guard, where it rules out \<open>k\<close> coinciding with the freshly allocated body
  entry; every other clash is ruled out by \<open>compile_E_src_img\<close> alone, since sibling
  sub-fragments allocate disjoint counter ranges.\<close>

lemma compile_functional:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> k_fresh k n n'
   \<Longrightarrow> (u, a1, v) \<in> E \<Longrightarrow> (u, a2, v) \<in> E \<Longrightarrow> a1 = a2"
proof (induction c arbitrary: k n n' en E K u a1 a2 v rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and n': "n' = n2" and E: "E = E1 \<union> E2"
    by (auto simp: Let_def split: prod.splits)
  have i1: "n1 = n + csize c1" using compile_next_id[OF c1] .
  have kf1: "k_fresh (Statement (n + csize c1)) n n1"
    unfolding k_fresh_def using i1 by auto
  have kf2: "k_fresh k (n + csize c1) n2"
    using Seq.prems(2) n' unfolding k_fresh_def by auto
  from Seq.prems(3) E have m1: "(u, a1, v) \<in> E1 \<or> (u, a1, v) \<in> E2" by auto
  from Seq.prems(4) E have m2: "(u, a2, v) \<in> E1 \<or> (u, a2, v) \<in> E2" by auto
  have disj: "Statement ` {n..<n1} \<inter> Statement ` {n1..<n2} = {}" by auto
  consider (L1) "(u, a1, v) \<in> E1" | (R1) "(u, a1, v) \<in> E2" using m1 by auto
  then show ?case
  proof cases
    case L1
    then consider (L2) "(u, a2, v) \<in> E1" | (R2) "(u, a2, v) \<in> E2" using m2 by auto
    then show ?thesis
    proof cases
      case L2 show ?thesis using Seq.IH(1)[OF c1 kf1 L1 L2] .
    next
      case R2
      have "u \<in> Statement ` {n..<n1}" using compile_E_src_img[OF c1 L1] .
      moreover have "u \<in> Statement ` {n1..<n2}"
        using compile_E_src_img[OF c2 R2] i1 by simp
      ultimately show ?thesis using disj by blast
    qed
  next
    case R1
    then consider (L2) "(u, a2, v) \<in> E1" | (R2) "(u, a2, v) \<in> E2" using m2 by auto
    then show ?thesis
    proof cases
      case L2
      have "u \<in> Statement ` {n1..<n2}"
        using compile_E_src_img[OF c2 R1] i1 by simp
      moreover have "u \<in> Statement ` {n..<n1}" using compile_E_src_img[OF c1 L2] .
      ultimately show ?thesis using disj by blast
    next
      case R2 show ?thesis using Seq.IH(2)[OF c2 kf2 R1 R2] .
    qed
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and n': "n' = n2"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  have e2: "en2 = Statement n1" using compile_entry[OF c2] .
  have i1: "n1 = Suc n + csize c1" using compile_next_id[OF c1] .
  have i2: "n2 = n1 + csize c2" using compile_next_id[OF c2] .
  have en_ne: "en1 \<noteq> en2" using e1 e2 i1 csize_pos[of c1] by simp
  have kf1: "k_fresh k (Suc n) n1"
    using If.prems(2) n' i2 unfolding k_fresh_def by auto
  have kf2: "k_fresh k n1 n2"
    using If.prems(2) n' i1 unfolding k_fresh_def by auto
  have gL: "Statement n \<notin> Statement ` {Suc n..<n1}" by auto
  have gR: "Statement n \<notin> Statement ` {n1..<n2}" using i1 by auto
  have disjLR: "Statement ` {Suc n..<n1} \<inter> Statement ` {n1..<n2} = {}" by auto
  from If.prems(3) E have m1:
    "(u, a1, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
       \<or> (u, a1, v) \<in> E1 \<or> (u, a1, v) \<in> E2" by auto
  from If.prems(4) E have m2:
    "(u, a2, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
       \<or> (u, a2, v) \<in> E1 \<or> (u, a2, v) \<in> E2" by auto
  consider (G1) "(u, a1, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}"
    | (L1) "(u, a1, v) \<in> E1" | (R1) "(u, a1, v) \<in> E2" using m1 by auto
  then show ?case
  proof cases
    case G1
    then have u_n: "u = Statement n" by auto
    consider (G2) "(u, a2, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}"
      | (L2) "(u, a2, v) \<in> E1" | (R2) "(u, a2, v) \<in> E2" using m2 by auto
    then show ?thesis
    proof cases
      case G2 show ?thesis using G1 G2 en_ne by auto
    next
      case L2
      have "u \<in> Statement ` {Suc n..<n1}" using compile_E_src_img[OF c1 L2] .
      then show ?thesis using u_n gL by simp
    next
      case R2
      have "u \<in> Statement ` {n1..<n2}" using compile_E_src_img[OF c2 R2] .
      then show ?thesis using u_n gR by simp
    qed
  next
    case L1
    have uL: "u \<in> Statement ` {Suc n..<n1}" using compile_E_src_img[OF c1 L1] .
    consider (G2) "(u, a2, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}"
      | (L2) "(u, a2, v) \<in> E1" | (R2) "(u, a2, v) \<in> E2" using m2 by auto
    then show ?thesis
    proof cases
      case G2
      then have "u = Statement n" by auto
      then show ?thesis using uL gL by simp
    next
      case L2 show ?thesis using If.IH(1)[OF c1 kf1 L1 L2] .
    next
      case R2
      have "u \<in> Statement ` {n1..<n2}" using compile_E_src_img[OF c2 R2] .
      with uL disjLR show ?thesis by blast
    qed
  next
    case R1
    have uR: "u \<in> Statement ` {n1..<n2}" using compile_E_src_img[OF c2 R1] .
    consider (G2) "(u, a2, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}"
      | (L2) "(u, a2, v) \<in> E1" | (R2) "(u, a2, v) \<in> E2" using m2 by auto
    then show ?thesis
    proof cases
      case G2
      then have "u = Statement n" by auto
      then show ?thesis using uR gR by simp
    next
      case L2
      have "u \<in> Statement ` {Suc n..<n1}" using compile_E_src_img[OF c1 L2] .
      with uR disjLR show ?thesis by blast
    next
      case R2 show ?thesis using If.IH(2)[OF c2 kf2 R1 R2] .
    qed
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 en1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and n': "n' = n1"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  have i1: "n1 = Suc n + csize c" using compile_next_id[OF c1] .
  have kbody: "k_fresh (Statement n) (Suc n) n1" unfolding k_fresh_def by auto
  have gB: "Statement n \<notin> Statement ` {Suc n..<n1}" by auto
  have en1_ne_k: "en1 \<noteq> k"
  proof
    assume "en1 = k"
    then have "k = Statement (Suc n)" using e1 by simp
    then show False using While.prems(2) n' i1 csize_pos[of c]
      unfolding k_fresh_def by auto
  qed
  from While.prems(3) E have m1:
    "(u, a1, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)}
       \<or> (u, a1, v) \<in> E1" by auto
  from While.prems(4) E have m2:
    "(u, a2, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)}
       \<or> (u, a2, v) \<in> E1" by auto
  consider (G1) "(u, a1, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)}"
    | (B1) "(u, a1, v) \<in> E1" using m1 by auto
  then show ?case
  proof cases
    case G1
    then have u_n: "u = Statement n" by auto
    consider (G2) "(u, a2, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)}"
      | (B2) "(u, a2, v) \<in> E1" using m2 by auto
    then show ?thesis
    proof cases
      case G2 show ?thesis using G1 G2 en1_ne_k by auto
    next
      case B2
      have "u \<in> Statement ` {Suc n..<n1}" using compile_E_src_img[OF c1 B2] .
      then show ?thesis using u_n gB by simp
    qed
  next
    case B1
    have uB: "u \<in> Statement ` {Suc n..<n1}" using compile_E_src_img[OF c1 B1] .
    consider (G2) "(u, a2, v) \<in> {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)}"
      | (B2) "(u, a2, v) \<in> E1" using m2 by auto
    then show ?thesis
    proof cases
      case G2
      then have "u = Statement n" by auto
      then show ?thesis using uB gB by simp
    next
      case B2 show ?thesis using While.IH[OF c1 kbody B1 B2] .
    qed
  qed
qed auto

subsection \<open>Functionality of one compiled procedure\<close>

text \<open>A compiled procedure adds exactly two edges to its body's own: the fixed entry wiring
  \<open>(FunctionEntry p, EA_Nop, Statement n)\<close> and, when the body falls through, the fixed
  epilogue \<open>(Statement r, EA_Ret None p, FunctionResult p)\<close>.  Both are singletons at a source
  the body itself never uses (\<open>compile_E_src_img\<close> bounds the body's sources to
  \<open>[n, r)\<close>, excluding \<open>r\<close>; the body's own entry is \<open>Statement n\<close>, never \<open>FunctionEntry p\<close>),
  so the three sources never collide.\<close>

lemma compile_proc_functional:
  assumes cp: "compile_proc \<Pi> p decl n = (n', E, K)"
    and e1: "(u, a1, v) \<in> E" and e2: "(u, a2, v) \<in> E"
  shows "a1 = a2"
proof -
  define r where "r = n + csize (body decl)"
  obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement r) n = (r, Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry p, EA_Nop, Statement n)
              (if falls_through (body decl)
               then insert (Statement r, EA_Ret None p, FunctionResult p) Eb
               else Eb)"
    unfolding r_def by (rule compile_procE[OF cp])
  have kfb: "k_fresh (Statement r) n r" unfolding k_fresh_def by auto
  have not_entry: "(x, a, w) \<in> Eb \<Longrightarrow> x \<noteq> FunctionEntry p" for x a w
    using compile_E_src_img[OF cb] by auto
  have not_epi: "(x, a, w) \<in> Eb \<Longrightarrow> x \<noteq> Statement r" for x a w
  proof
    assume h: "(x, a, w) \<in> Eb" "x = Statement r"
    then have "Statement r \<in> Statement ` {n..<r}"
      using compile_E_src_img[OF cb] by blast
    then show False by auto
  qed
  consider (Ent) "u = FunctionEntry p"
    | (Epi) "u \<noteq> FunctionEntry p" "u = Statement r"
    | (Bod) "u \<noteq> FunctionEntry p" "u \<noteq> Statement r"
    by blast
  then show ?thesis
  proof cases
    case Ent
    then have "a1 = EA_Nop" using e1 E not_entry by (auto split: if_splits)
    moreover have "a2 = EA_Nop" using Ent e2 E not_entry by (auto split: if_splits)
    ultimately show ?thesis by simp
  next
    case Epi
    then have "a1 = EA_Ret None p" using e1 E not_epi by (auto split: if_splits)
    moreover have "a2 = EA_Ret None p" using Epi e2 E not_epi by (auto split: if_splits)
    ultimately show ?thesis by simp
  next
    case Bod
    then have b1: "(u, a1, v) \<in> Eb" using e1 E by (auto split: if_splits)
    have b2: "(u, a2, v) \<in> Eb" using Bod e2 E by (auto split: if_splits)
    show ?thesis using compile_functional[OF cb kfb b1 b2] .
  qed
qed

text \<open>Every edge a compiled procedure sources at a \<^const>\<open>FunctionEntry\<close> node is the fixed
  entry wiring, hence \<^const>\<open>EA_Nop\<close> --- independent of which procedure or which name.  This
  is what lets \<open>compile_procs_functional\<close> below skip range bookkeeping for the
  \<^const>\<open>FunctionEntry\<close>-sourced case entirely: two such edges agree on the action without
  needing their source procedures to be the same one.\<close>

lemma compile_proc_entry_nop:
  assumes cp: "compile_proc \<Pi> p decl n = (n', E, K)" and e: "(FunctionEntry q, a, v) \<in> E"
  shows "a = EA_Nop"
proof -
  define r where "r = n + csize (body decl)"
  obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement r) n = (r, Statement n, Eb, K)"
    and E: "E = insert (FunctionEntry p, EA_Nop, Statement n)
              (if falls_through (body decl)
               then insert (Statement r, EA_Ret None p, FunctionResult p) Eb
               else Eb)"
    unfolding r_def by (rule compile_procE[OF cp])
  have not_entry: "(x, a', w) \<in> Eb \<Longrightarrow> x \<noteq> FunctionEntry q" for x a' w
    using compile_E_src_img[OF cb] by auto
  from e E not_entry show ?thesis by (auto split: if_splits)
qed

lemma compile_procs_entry_nop:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (FunctionEntry q, a, v) \<in> E \<Longrightarrow> a = EA_Nop"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems(1) obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and E: "E = E0 \<union> E'"
      by (auto split: prod.splits)
    from Cons.prems(2) E consider "(FunctionEntry q, a, v) \<in> E0" | "(FunctionEntry q, a, v) \<in> E'"
      by auto
    then show ?thesis
    proof cases
      case 1 then show ?thesis using compile_proc_entry_nop[OF cp] by simp
    next
      case 2 then show ?thesis using Cons.IH[OF rest] by simp
    qed
  qed
qed

subsection \<open>Functionality of a compiled procedure list and a compiled program\<close>

text \<open>The \<^const>\<open>FunctionEntry\<close>-sourced case is discharged by \<open>compile_proc_entry_nop\<close>/
  \<open>compile_procs_entry_nop\<close> without any range argument.  The \<^const>\<open>Statement\<close>-sourced case
  reuses \<open>compile_proc_frag_range\<close>/\<open>compile_procs_frag_range\<close> (existing,
  \<open>Compile_Invariants.thy\<close>) for cross-procedure disjointness, mirroring the sibling-fragment
  argument \<open>compile_functional\<close> already makes inside one procedure.\<close>

lemma compile_procs_functional:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, a1, v) \<in> E \<Longrightarrow> (u, a2, v) \<in> E \<Longrightarrow> a1 = a2"
proof (induction ps arbitrary: n n' E K u a1 a2 v)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems(1) obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and E: "E = E0 \<union> E'"
      by (auto split: prod.splits)
    from Cons.prems(2) E have m1: "(u, a1, v) \<in> E0 \<or> (u, a1, v) \<in> E'" by auto
    from Cons.prems(3) E have m2: "(u, a2, v) \<in> E0 \<or> (u, a2, v) \<in> E'" by auto
    show ?thesis
    proof (cases "\<exists>q. u = FunctionEntry q")
      case True
      then obtain q where uq: "u = FunctionEntry q" by blast
      have "a1 = EA_Nop"
        using m1 uq compile_proc_entry_nop[OF cp] compile_procs_entry_nop[OF rest] by auto
      moreover have "a2 = EA_Nop"
        using m2 uq compile_proc_entry_nop[OF cp] compile_procs_entry_nop[OF rest] by auto
      ultimately show ?thesis by simp
    next
      case False
      then obtain j where uj: "u = Statement j"
        using compile_procs_frag_range compile_proc_frag_range m1
          frag_stmts_E_srcI[of j _ _ E0 K0] frag_stmts_E_srcI[of j _ _ E' K']
        by (metis Cons.prems(1,3) cfg_node.exhaust_sel
            compile_procs_no_result_source)
      have r0: "(u, a, v) \<in> E0 \<Longrightarrow> n \<le> j \<and> j < n1" for a
        using uj cp compile_proc_frag_range[OF cp] frag_stmts_E_srcI[of j a v E0 K0] by auto
      have r1: "(u, a, v) \<in> E' \<Longrightarrow> n1 \<le> j \<and> j < n2" for a
        using uj rest compile_procs_frag_range[OF rest] frag_stmts_E_srcI[of j a v E' K']
        by auto
      from m1 show ?thesis
      proof
        assume h1: "(u, a1, v) \<in> E0"
        from m2 show ?thesis
        proof
          assume h2: "(u, a2, v) \<in> E0"
          show ?thesis using compile_proc_functional[OF cp h1 h2] .
        next
          assume h2: "(u, a2, v) \<in> E'"
          show ?thesis using r0[OF h1] r1[OF h2] by linarith
        qed
      next
        assume h1: "(u, a1, v) \<in> E'"
        from m2 show ?thesis
        proof
          assume h2: "(u, a2, v) \<in> E0"
          show ?thesis using r1[OF h1] r0[OF h2] by linarith
        next
          assume h2: "(u, a2, v) \<in> E'"
          show ?thesis using Cons.IH[OF rest h1 h2] .
        qed
      qed
    qed
  qed
qed

text \<open>The compiled-program-level edge-action determinism theorem.  This resolves design-gate
  item 2 of \<open>GHOST_DOMAIN_SEEDING_MIGRATION.md\<close> section 9: \<^const>\<open>intra\<close> of a compiled program
  is functional, so a trace's \<^const>\<open>path\<close> determines the action that fired at each step
  without enriching the trace type.\<close>

theorem compile_prog_intra_functional:
  assumes e1: "(u, a1, v) \<in> intra (compile_prog \<Pi> ps mnm main)"
    and e2: "(u, a2, v) \<in> intra (compile_prog \<Pi> ps mnm main)"
  shows "a1 = a2"
proof -
  obtain n1 Eprocs Kprocs where procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    by (metis prod_cases3)
  obtain n2 Emain Kmain where
    mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    by (metis prod_cases3)
  have g: "compile_prog \<Pi> ps mnm main
             = \<lparr> intra = Eprocs \<union> Emain, calls = Kprocs \<union> Kmain, cfg_entry = FunctionEntry mnm,
                checks = (\<lambda>(u, a, v). (u, ea_check_cond a)) ` Set.filter (\<lambda>(u, a, v). is_EA_Check a) (Eprocs \<union> Emain) \<rparr>"
    unfolding compile_prog_def by (simp add: procs mainc Let_def)
  from e1 g have m1: "(u, a1, v) \<in> Eprocs \<or> (u, a1, v) \<in> Emain" by simp
  from e2 g have m2: "(u, a2, v) \<in> Eprocs \<or> (u, a2, v) \<in> Emain" by simp
  show ?thesis
  proof (cases "\<exists>q. u = FunctionEntry q")
    case True
    then obtain q where uq: "u = FunctionEntry q" by blast
    have "a1 = EA_Nop"
      using m1 uq compile_procs_entry_nop[OF procs] compile_proc_entry_nop[OF mainc] by auto
    moreover have "a2 = EA_Nop"
      using m2 uq compile_procs_entry_nop[OF procs] compile_proc_entry_nop[OF mainc] by auto
    ultimately show ?thesis by simp
  next
    case False
    then obtain j where uj: "u = Statement j"
      using m1
      by (metis compile_prog_no_result_source e1 kstmt.cases)
    have r0: "(u, a, v) \<in> Eprocs \<Longrightarrow> j < n1" for a
      using uj procs compile_procs_frag_range[OF procs] frag_stmts_E_srcI[of j a v Eprocs Kprocs]
      by auto
    have r1: "(u, a, v) \<in> Emain \<Longrightarrow> n1 \<le> j" for a
      using uj mainc compile_proc_frag_range[OF mainc] frag_stmts_E_srcI[of j a v Emain Kmain]
      by auto
    from m1 show ?thesis
    proof
      assume h1: "(u, a1, v) \<in> Eprocs"
      from m2 show ?thesis
      proof
        assume h2: "(u, a2, v) \<in> Eprocs"
        show ?thesis using compile_procs_functional[OF procs h1 h2] .
      next
        assume h2: "(u, a2, v) \<in> Emain"
        show ?thesis using r0[OF h1] r1[OF h2] by linarith
      qed
    next
      assume h1: "(u, a1, v) \<in> Emain"
      from m2 show ?thesis
      proof
        assume h2: "(u, a2, v) \<in> Eprocs"
        show ?thesis using r1[OF h1] r0[OF h2] by linarith
      next
        assume h2: "(u, a2, v) \<in> Emain"
        show ?thesis using compile_proc_functional[OF mainc h1 h2] .
      qed
    qed
  qed
qed

end

