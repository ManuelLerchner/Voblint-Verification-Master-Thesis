theory Compile_Wellformed
  imports VIMP_Proc_to_CFG
begin

section \<open>What is true of the graph the compiler produces\<close>

text \<open>
  The compiler theory says how a program becomes nodes and edges; this one says what holds of
  the result.  Three facts leave the session.  A compiled \<open>calls\<close> set never has two edges out
  of one node, because each fragment claims fresh \<^const>\<open>Statement\<close> indices for its call
  leaves (\<open>compile_prog_calls_source_unique\<close>) --- the context-sensitive analyses need it to
  read a call site's callee off the graph.  A compiled graph is finite
  (\<open>compile_prog_finite\<close>), which every solver instantiation requires.  And a compiled graph
  satisfies \<^const>\<open>wf_cfg\<close> (\<open>compile_prog_wf\<close>), the compiler-agnostic contract the D/G layer
  is stated against.

  \<open>frag_stmts\<close> is the local vocabulary: the set of \<^const>\<open>Statement\<close> indices an edge set
  mentions, which is how a fragment's claim on the counter is expressed and how two
  procedures are shown not to overlap.
\<close>

subsection \<open>Call-source uniqueness\<close>

text \<open>
  Each compiled fragment allocates its \<open>Call\<close> leaves at distinct, freshly claimed
  \<open>Statement\<close> indices, so a compiled \<open>calls\<close> set never has two different edges out of
  the same source node.  This is a structural fact about the compiler, not about
  \<^const>\<open>wf_cfg\<close> (which is deliberately compiler-agnostic) or about any particular
  program: a hand-built CFG whose source node has two distinct outgoing call edges can
  still violate it, but no \<^const>\<open>compile_prog\<close> output can, and it is what lets a
  context-routing hook resolve the one call at a node from the source node alone.
\<close>

lemma compile_calls_source_range:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>j. u = Statement j \<and> n \<le> j \<and> j < n'"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and n': "n' = n2" and K: "K = K1 \<union> K2"
    by (auto simp: Let_def split: prod.splits)
  have i1: "n1 = n + csize c1" using compile_next_id[OF c1] .
  have i2: "n2 = n + csize c1 + csize c2" using compile_next_id[OF c2] by simp
  from Seq.prems(2) K consider (L) "(u, act, ce, af) \<in> K1" | (R) "(u, act, ce, af) \<in> K2" by auto
  then show ?case
  proof cases
    case L with Seq.IH(1)[OF c1 L] i1 i2 show ?thesis unfolding n' by auto
  next
    case R with Seq.IH(2)[OF c2 R] i1 i2 show ?thesis unfolding n' by auto
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and n': "n' = n2" and K: "K = K1 \<union> K2"
    by (auto split: prod.splits)
  have i1: "n1 = Suc n + csize c1" using compile_next_id[OF c1] by simp
  have i2: "n2 = n1 + csize c2" using compile_next_id[OF c2] .
  from If.prems(2) K consider (L) "(u, act, ce, af) \<in> K1" | (R) "(u, act, ce, af) \<in> K2" by auto
  then show ?case
  proof cases
    case L with If.IH(1)[OF c1 L] i1 i2 show ?thesis unfolding n' by auto
  next
    case R with If.IH(2)[OF c2 R] i1 i2 show ?thesis unfolding n' by auto
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 en1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and n': "n' = n1" and K: "K = K1"
    by (auto split: prod.splits)
  from While.prems(2) K have "(u, act, ce, af) \<in> K1" by simp
  with While.IH[OF c1] show ?case unfolding n' by auto
qed (auto split: prod.splits option.splits)

lemma compile_calls_source_unique:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, ca1, ce1, af1) \<in> K \<Longrightarrow> (u, ca2, ce2, af2) \<in> K
   \<Longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      cc1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and cc2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and K: "K = K1 \<union> K2"
    by (auto simp: Let_def split: prod.splits)
  have i1: "n1 = n + csize c1" using compile_next_id[OF cc1] .
  have low: "\<And>u' act' ce' af'. (u', act', ce', af') \<in> K1 \<Longrightarrow> \<exists>j. u' = Statement j \<and> j < n1"
    using compile_calls_source_range[OF cc1] i1 by blast
  have high: "\<And>u' act' ce' af'. (u', act', ce', af') \<in> K2 \<Longrightarrow> \<exists>j. u' = Statement j \<and> n1 \<le> j"
    using compile_calls_source_range[OF cc2]
    using i1 by blast
  have not_both: "\<And>u' act1' ce1' af1' act2' ce2' af2'.
      (u', act1', ce1', af1') \<in> K1 \<Longrightarrow> (u', act2', ce2', af2') \<in> K2 \<Longrightarrow> False"
    using low high by fastforce
  from Seq.prems(2) K have m1: "(u, ca1, ce1, af1) \<in> K1 \<or> (u, ca1, ce1, af1) \<in> K2" by auto
  from Seq.prems(3) K have m2: "(u, ca2, ce2, af2) \<in> K1 \<or> (u, ca2, ce2, af2) \<in> K2" by auto
  consider (LL) "(u, ca1, ce1, af1) \<in> K1" "(u, ca2, ce2, af2) \<in> K1"
         | (RR) "(u, ca1, ce1, af1) \<in> K2" "(u, ca2, ce2, af2) \<in> K2"
         | (LR) "(u, ca1, ce1, af1) \<in> K1" "(u, ca2, ce2, af2) \<in> K2"
         | (RL) "(u, ca1, ce1, af1) \<in> K2" "(u, ca2, ce2, af2) \<in> K1"
    using m1 m2 by blast
  then show ?case
  proof cases
    case LL then show ?thesis using Seq.IH(1)[OF cc1] by blast
  next
    case RR then show ?thesis using Seq.IH(2)[OF cc2] by blast
  next
    case LR then show ?thesis using not_both by blast
  next
    case RL then show ?thesis using not_both by blast
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 en1 E1 K1 n2 en2 E2 K2 where
      cc1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and cc2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and K: "K = K1 \<union> K2"
    by (auto split: prod.splits)
  have low: "\<And>u' act' ce' af'. (u', act', ce', af') \<in> K1 \<Longrightarrow> \<exists>j. u' = Statement j \<and> j < n1"
    using compile_calls_source_range[OF cc1] by fastforce
  have high: "\<And>u' act' ce' af'. (u', act', ce', af') \<in> K2 \<Longrightarrow> \<exists>j. u' = Statement j \<and> n1 \<le> j"
    using compile_calls_source_range[OF cc2] by fastforce
  have not_both: "\<And>u' act1' ce1' af1' act2' ce2' af2'.
      (u', act1', ce1', af1') \<in> K1 \<Longrightarrow> (u', act2', ce2', af2') \<in> K2 \<Longrightarrow> False"
    using low high by fastforce
  from If.prems(2) K have m1: "(u, ca1, ce1, af1) \<in> K1 \<or> (u, ca1, ce1, af1) \<in> K2" by auto
  from If.prems(3) K have m2: "(u, ca2, ce2, af2) \<in> K1 \<or> (u, ca2, ce2, af2) \<in> K2" by auto
  consider (LL) "(u, ca1, ce1, af1) \<in> K1" "(u, ca2, ce2, af2) \<in> K1"
         | (RR) "(u, ca1, ce1, af1) \<in> K2" "(u, ca2, ce2, af2) \<in> K2"
         | (LR) "(u, ca1, ce1, af1) \<in> K1" "(u, ca2, ce2, af2) \<in> K2"
         | (RL) "(u, ca1, ce1, af1) \<in> K2" "(u, ca2, ce2, af2) \<in> K1"
    using m1 m2 by blast
  then show ?case
  proof cases
    case LL then show ?thesis using If.IH(1)[OF cc1] by blast
  next
    case RR then show ?thesis using If.IH(2)[OF cc2] by blast
  next
    case LR then show ?thesis using not_both by blast
  next
    case RL then show ?thesis using not_both by blast
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 en1 E1 K1 where
      cc1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and K: "K = K1"
    by (auto split: prod.splits)
  from While.prems(2) K have "(u, ca1, ce1, af1) \<in> K1" by simp
  moreover from While.prems(3) K have "(u, ca2, ce2, af2) \<in> K1" by simp
  ultimately show ?case using While.IH[OF cc1] by blast
qed (auto split: prod.splits option.splits)

lemma compile_proc_counter_mono:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> n \<le> n'"
  by auto

lemma compile_proc_calls_source_range:
  assumes "compile_proc \<Pi> p decl n = (n', E, K)" and "(u, act, ce, af) \<in> K"
  shows "\<exists>j. u = Statement j \<and> n \<le> j \<and> j < n'"
proof -
  from assms(1) obtain Eb where
      body: "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
               = (n + csize (body decl), Statement n, Eb, K)"
    and n': "n' = Suc (n + csize (body decl))"
    by (rule compile_procE)
  from compile_calls_source_range[OF body assms(2)] show ?thesis unfolding n' by auto
qed

lemma compile_proc_calls_source_unique:
  assumes "compile_proc \<Pi> p decl n = (n', E, K)"
    and "(u, ca1, ce1, af1) \<in> K" and "(u, ca2, ce2, af2) \<in> K"
  shows "ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
proof -
  from assms(1) obtain Eb where
    body: "compile \<Pi> p (body decl) (Statement (n + csize (body decl))) n
             = (n + csize (body decl), Statement n, Eb, K)"
    by (rule compile_procE)
  from compile_calls_source_unique[OF body assms(2,3)] show ?thesis .
qed

lemma compile_procs_counter_mono:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> n \<le> n'"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems obtain n1 E0 K0 n2 E' K' where
        cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and n': "n' = n2"
      by (auto split: prod.splits)
    from compile_proc_counter_mono[OF cp] Cons.IH[OF rest] n' show ?thesis by simp
  qed
qed

text \<open>Every edge of a \<^const>\<open>compile_procs\<close> pass comes from one declared member's
  \<^const>\<open>compile_proc\<close> fragment, compiled at some offset inside the pass's counter range;
  conversely every declared member contributes such a fragment.  The three facts below
  are what every structural property of a pass reduces to.\<close>
lemma compile_procs_intra_origin:
  assumes "compile_procs \<Pi> ps n = (n', E, K)" and "e \<in> E"
  shows "\<exists>p decl m m' Ep Kp. p \<in> set ps \<and> \<Pi> p = Some decl
           \<and> compile_proc \<Pi> p decl m = (m', Ep, Kp) \<and> n \<le> m \<and> m' \<le> n' \<and> e \<in> Ep"
  using assms
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems have "compile_procs \<Pi> qs n = (n', E, K)" by simp
    from Cons.IH[OF this Cons.prems(2)] show ?thesis by (blast intro: list.set_intros(2))
  next
    case (Some declq)
    from Cons.prems(1) Some obtain n1 Eq Kq n2 E' K' where
        cq: "compile_proc \<Pi> q declq n = (n1, Eq, Kq)"
      and rest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      and eq: "n' = n2" "E = Eq \<union> E'"
      by (auto split: prod.splits)
    have mono: "n \<le> n1" "n1 \<le> n2"
      using compile_proc_counter_mono[OF cq] compile_procs_counter_mono[OF rest] .
    show ?thesis
    proof (cases "e \<in> Eq")
      case True
      have "q \<in> set (q # qs) \<and> \<Pi> q = Some declq \<and> compile_proc \<Pi> q declq n = (n1, Eq, Kq)
              \<and> n \<le> n \<and> n1 \<le> n' \<and> e \<in> Eq"
        using Some cq mono(2) eq(1) True by simp
      then show ?thesis by blast
    next
      case False
      with Cons.prems(2) eq(2) have "e \<in> E'" by simp
      from Cons.IH[OF rest this] obtain p decl m m' Ep Kp where
        "p \<in> set qs" "\<Pi> p = Some decl" "compile_proc \<Pi> p decl m = (m', Ep, Kp)"
        "n1 \<le> m" "m' \<le> n2" "e \<in> Ep" by blast
      with mono(1) eq(1)
      have "p \<in> set (q # qs) \<and> \<Pi> p = Some decl \<and> compile_proc \<Pi> p decl m = (m', Ep, Kp)
              \<and> n \<le> m \<and> m' \<le> n' \<and> e \<in> Ep"
        by (auto intro: le_trans)
      then show ?thesis by blast
    qed
  qed
qed

lemma compile_procs_calls_origin:
  assumes "compile_procs \<Pi> ps n = (n', E, K)" and "e \<in> K"
  shows "\<exists>p decl m m' Ep Kp. p \<in> set ps \<and> \<Pi> p = Some decl
           \<and> compile_proc \<Pi> p decl m = (m', Ep, Kp) \<and> n \<le> m \<and> m' \<le> n' \<and> e \<in> Kp"
  using assms
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems have "compile_procs \<Pi> qs n = (n', E, K)" by simp
    from Cons.IH[OF this Cons.prems(2)] show ?thesis by (blast intro: list.set_intros(2))
  next
    case (Some declq)
    from Cons.prems(1) Some obtain n1 Eq Kq n2 E' K' where
        cq: "compile_proc \<Pi> q declq n = (n1, Eq, Kq)"
      and rest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      and eq: "n' = n2" "K = Kq \<union> K'"
      by (auto split: prod.splits)
    have mono: "n \<le> n1" "n1 \<le> n2"
      using compile_proc_counter_mono[OF cq] compile_procs_counter_mono[OF rest] .
    show ?thesis
    proof (cases "e \<in> Kq")
      case True
      have "q \<in> set (q # qs) \<and> \<Pi> q = Some declq \<and> compile_proc \<Pi> q declq n = (n1, Eq, Kq)
              \<and> n \<le> n \<and> n1 \<le> n' \<and> e \<in> Kq"
        using Some cq mono(2) eq(1) True by simp
      then show ?thesis by blast
    next
      case False
      with Cons.prems(2) eq(2) have "e \<in> K'" by simp
      from Cons.IH[OF rest this] obtain p decl m m' Ep Kp where
        "p \<in> set qs" "\<Pi> p = Some decl" "compile_proc \<Pi> p decl m = (m', Ep, Kp)"
        "n1 \<le> m" "m' \<le> n2" "e \<in> Kp" by blast
      with mono(1) eq(1)
      have "p \<in> set (q # qs) \<and> \<Pi> p = Some decl \<and> compile_proc \<Pi> p decl m = (m', Ep, Kp)
              \<and> n \<le> m \<and> m' \<le> n' \<and> e \<in> Kp"
        by (auto intro: le_trans)
      then show ?thesis by blast
    qed
  qed
qed

lemma compile_procs_member:
  assumes "compile_procs \<Pi> ps n = (n', E, K)" and "p \<in> set ps" and "\<Pi> p = Some decl"
  shows "\<exists>m m' Ep Kp. compile_proc \<Pi> p decl m = (m', Ep, Kp)
           \<and> n \<le> m \<and> m' \<le> n' \<and> Ep \<subseteq> E \<and> Kp \<subseteq> K"
  using assms
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems have "compile_procs \<Pi> qs n = (n', E, K)" "p \<in> set qs" by auto
    then show ?thesis using Cons.IH Cons.prems(3) by blast
  next
    case (Some declq)
    from Cons.prems(1) Some obtain n1 Eq Kq n2 E' K' where
        cq: "compile_proc \<Pi> q declq n = (n1, Eq, Kq)"
      and rest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      and eq: "n' = n2" "E = Eq \<union> E'" "K = Kq \<union> K'"
      by (auto split: prod.splits)
    have mono: "n \<le> n1" "n1 \<le> n2"
      using compile_proc_counter_mono[OF cq] compile_procs_counter_mono[OF rest] .
    show ?thesis
    proof (cases "p = q")
      case True
      with Cons.prems(3) Some have "decl = declq" by simp
      with True cq mono(2) eq
      have "compile_proc \<Pi> p decl n = (n1, Eq, Kq) \<and> n \<le> n \<and> n1 \<le> n' \<and> Eq \<subseteq> E \<and> Kq \<subseteq> K"
        by simp
      then show ?thesis by blast
    next
      case False
      with Cons.prems(2) have "p \<in> set qs" by simp
      from Cons.IH[OF rest this Cons.prems(3)] obtain m m' Ep Kp where
        "compile_proc \<Pi> p decl m = (m', Ep, Kp)" "n1 \<le> m" "m' \<le> n2" "Ep \<subseteq> E'" "Kp \<subseteq> K'"
        by blast
      with mono(1) eq
      have "compile_proc \<Pi> p decl m = (m', Ep, Kp) \<and> n \<le> m \<and> m' \<le> n' \<and> Ep \<subseteq> E \<and> Kp \<subseteq> K"
        by (auto intro: le_trans)
      then show ?thesis by blast
    qed
  qed
qed

lemma compile_procs_calls_source_range:
  assumes "compile_procs \<Pi> ps n = (n', E, K)" and "(u, act, ce, af) \<in> K"
  shows "\<exists>j. u = Statement j \<and> n \<le> j \<and> j < n'"
  using compile_procs_calls_origin[OF assms] compile_proc_calls_source_range by fastforce

lemma compile_procs_calls_source_unique:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, ca1, ce1, af1) \<in> K \<Longrightarrow> (u, ca2, ce2, af2) \<in> K
   \<Longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
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
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    have not_both: "\<And>u' act1' ce1' af1' act2' ce2' af2'.
        (u', act1', ce1', af1') \<in> K0 \<Longrightarrow> (u', act2', ce2', af2') \<in> K' \<Longrightarrow> False"
      using compile_proc_calls_source_range[OF cp]
            compile_procs_calls_source_range[OF rest]
      by fastforce
    from Cons.prems(2) K have m1: "(u, ca1, ce1, af1) \<in> K0 \<or> (u, ca1, ce1, af1) \<in> K'" by auto
    from Cons.prems(3) K have m2: "(u, ca2, ce2, af2) \<in> K0 \<or> (u, ca2, ce2, af2) \<in> K'" by auto
    consider (LL) "(u, ca1, ce1, af1) \<in> K0" "(u, ca2, ce2, af2) \<in> K0"
           | (RR) "(u, ca1, ce1, af1) \<in> K'" "(u, ca2, ce2, af2) \<in> K'"
           | (LR) "(u, ca1, ce1, af1) \<in> K0" "(u, ca2, ce2, af2) \<in> K'"
           | (RL) "(u, ca1, ce1, af1) \<in> K'" "(u, ca2, ce2, af2) \<in> K0"
      using m1 m2 by blast
    then show ?thesis
    proof cases
      case LL then show ?thesis using compile_proc_calls_source_unique[OF cp] by blast
    next
      case RR then show ?thesis using Cons.IH[OF rest] by blast
    next
      case LR then show ?thesis using not_both by blast
    next
      case RL then show ?thesis using not_both by blast
    qed
  qed
qed

text \<open>Whole-program call-source uniqueness: the fact a routed-context analysis needs
  to resolve the formals of the one call at a node without ambiguity, for any
  \<^const>\<open>compile_prog\<close> output. Combines the declared-procedures pass and the \<open>main\<close>
  pass the same way the well-formedness theorem combines its own two passes.\<close>

theorem compile_prog_calls_source_unique:
  assumes "(u, ca1, ce1, af1) \<in> calls (compile_prog \<Pi> ps main_name main)"
    and "(u, ca2, ce2, af2) \<in> calls (compile_prog \<Pi> ps main_name main)"
  shows "ca1 = ca2 \<and> ce1 = ce2 \<and> af1 = af2"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> main_name \<lparr>formals = [], body = main\<rparr> n1 = (n2, Emain, Kmain)"
    and g: "calls (compile_prog \<Pi> ps main_name main) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  have not_both: "\<And>u' act1' ce1' af1' act2' ce2' af2'.
      (u', act1', ce1', af1') \<in> Kprocs \<Longrightarrow> (u', act2', ce2', af2') \<in> Kmain \<Longrightarrow> False"
    using compile_procs_calls_source_range[OF procs] compile_proc_calls_source_range[OF mainc]
    by fastforce
  from assms show ?thesis unfolding g
    using compile_procs_calls_source_unique[OF procs] compile_proc_calls_source_unique[OF mainc]
      not_both by (elim UnE) (blast | (drule not_both; blast))+
qed


text \<open>The \<open>Statement\<close> indices a compiled fragment touches.  Sources are always freshly
  allocated, so they lie in the fragment's own counter range; a target may in addition be the
  continuation, which belongs to the enclosing construct.  \<open>kstmt\<close> names that one extra
  index, and is empty when the continuation is not a \<open>Statement\<close> node.\<close>

definition frag_stmts ::
  "(cfg_node \<times> edge_action \<times> cfg_node) set
   \<Rightarrow> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set \<Rightarrow> nat set"
where
  "frag_stmts E K =
     {j. \<exists>a v. (Statement j, a, v) \<in> E} \<union> {j. \<exists>u a. (u, a, Statement j) \<in> E}
   \<union> {j. \<exists>act ce af. (Statement j, act, ce, af) \<in> K}
   \<union> {j. \<exists>u act ce. (u, act, ce, Statement j) \<in> K}"

fun kstmt :: "cfg_node \<Rightarrow> nat set" where
  "kstmt (Statement j) = {j}"
| "kstmt (FunctionEntry q) = {}"
| "kstmt (FunctionResult q) = {}"

lemma kstmt_iff [simp]: "j \<in> kstmt v \<longleftrightarrow> v = Statement j"
  by (cases v) auto

lemma frag_stmts_empty [simp]: "frag_stmts {} {} = {}"
  by (simp add: frag_stmts_def)

lemma frag_stmts_Un:
  "frag_stmts (E1 \<union> E2) (K1 \<union> K2) = frag_stmts E1 K1 \<union> frag_stmts E2 K2"
  by (auto simp: frag_stmts_def)

lemma frag_stmts_E_srcI [intro]:
  "(Statement j, a, v) \<in> E \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

lemma frag_stmts_E_tgtI [intro]:
  "(u, a, Statement j) \<in> E \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

lemma frag_stmts_K_srcI [intro]:
  "(Statement j, act, ce, af) \<in> K \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

lemma frag_stmts_K_tgtI [intro]:
  "(u, act, ce, Statement j) \<in> K \<Longrightarrow> j \<in> frag_stmts E K"
  unfolding frag_stmts_def by blast

lemma compile_frag_stmts_range:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> frag_stmts E K \<subseteq> {n..<n'} \<union> kstmt k"
proof (induction c arbitrary: k n n' en E K rule: com.induct)
  case (Seq c1 c2)
  from Seq.prems obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and n': "n' = n2" and E: "E = E1 \<union> E2" and K: "K = K1 \<union> K2"
    by (auto simp: Let_def split: prod.splits)
  have i1: "n1 = n + csize c1" using compile_next_id[OF c1] .
  have i2: "n2 = n + csize c1 + csize c2" using compile_next_id[OF c2] by simp
  have r1: "frag_stmts E1 K1 \<subseteq> {n..<n1} \<union> {n + csize c1}" using Seq.IH(1)[OF c1] by simp
  have r2: "frag_stmts E2 K2 \<subseteq> {n + csize c1..<n2} \<union> kstmt k" using Seq.IH(2)[OF c2] .
  show ?case
    using r1 r2 i1 i2 csize_pos[of c2]
    unfolding E K n' by (simp only: frag_stmts_Un) auto
next
  case (If b c1 c2)
  from If.prems obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and n': "n' = n2"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                  \<union> (E1 \<union> E2)"
    and K: "K = {} \<union> (K1 \<union> K2)"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  have e2: "en2 = Statement n1" using compile_entry[OF c2] .
  have i1: "n1 = Suc n + csize c1" using compile_next_id[OF c1] .
  have i2: "n2 = n1 + csize c2" using compile_next_id[OF c2] .
  have r1: "frag_stmts E1 K1 \<subseteq> {Suc n..<n1} \<union> kstmt k" using If.IH(1)[OF c1] .
  have r2: "frag_stmts E2 K2 \<subseteq> {n1..<n2} \<union> kstmt k" using If.IH(2)[OF c2] .
  have guard: "frag_stmts {(Statement n, EA_Assume b, en1),
                           (Statement n, EA_AssumeNot b, en2)} {} \<subseteq> {n..<n2}"
    using e1 e2 i1 i2 csize_pos[of c1] csize_pos[of c2] by (auto simp: frag_stmts_def)
  have dec: "frag_stmts E K
               = frag_stmts {(Statement n, EA_Assume b, en1),
                             (Statement n, EA_AssumeNot b, en2)} {}
                 \<union> frag_stmts (E1 \<union> E2) (K1 \<union> K2)"
    unfolding E K by (rule frag_stmts_Un)
  have body: "frag_stmts (E1 \<union> E2) (K1 \<union> K2) \<subseteq> {n..<n2} \<union> kstmt k"
    using r1 r2 i1 i2 csize_pos[of c1] by (simp only: frag_stmts_Un) auto
  show ?case unfolding n' dec using guard body by blast
next
  case (While b c)
  from While.prems obtain n1 en1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and n': "n' = n1"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1"
    and K: "K = {} \<union> K1"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  have i1: "n1 = Suc n + csize c" using compile_next_id[OF c1] .
  have r1: "frag_stmts E1 K1 \<subseteq> {Suc n..<n1} \<union> {n}" using While.IH[OF c1] by simp
  have guard: "frag_stmts {(Statement n, EA_Assume b, en1),
                           (Statement n, EA_AssumeNot b, k)} {} \<subseteq> {n..<n1} \<union> kstmt k"
    using e1 i1 csize_pos[of c] by (auto simp: frag_stmts_def)
  have dec: "frag_stmts E K
               = frag_stmts {(Statement n, EA_Assume b, en1),
                             (Statement n, EA_AssumeNot b, k)} {} \<union> frag_stmts E1 K1"
    unfolding E K by (rule frag_stmts_Un)
  show ?case unfolding n' dec using guard r1 i1 csize_pos[of c] by force 
qed (auto simp: frag_stmts_def split: option.splits)
subsection \<open>Finiteness\<close>

lemma compile_finite:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> finite E \<and> finite K"
  by (induction c arbitrary: k n n' en E K rule: com.induct)
     (auto simp: Let_def split: prod.splits option.splits)

lemma compile_proc_finite:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> finite E \<and> finite K"
  by (auto simp: compile_proc_def Let_def split: prod.splits dest: compile_finite)

lemma compile_procs_finite:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> finite E \<and> finite K"
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases "\<Pi> p")
    case None with Cons show ?thesis by simp
  next
    case (Some decl)
    with Cons.prems obtain n1 E0 K0 n2 E' K' where
      cp: "compile_proc \<Pi> p decl n = (n1, E0, K0)"
      and rest: "compile_procs \<Pi> ps n1 = (n2, E', K')"
      and E: "E = E0 \<union> E'" and K: "K = K0 \<union> K'"
      by (auto split: prod.splits)
    from compile_proc_finite[OF cp] Cons.IH[OF rest] show ?thesis
      unfolding E K by simp
  qed
qed

lemma compile_prog_finite:
  "finite (intra (compile_prog \<Pi> ps main_name main))
   \<and> finite (calls (compile_prog \<Pi> ps main_name main))"
  unfolding compile_prog_def
  by (auto simp: Let_def split: prod.splits
       dest: compile_procs_finite compile_proc_finite)

subsection \<open>Edge shapes for well-formedness\<close>

text \<open>Every emitted call edge targets a \<open>FunctionEntry\<close>; a call is never an intra edge.\<close>
lemma compile_call_ce_entry:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
  by (induction c arbitrary: k n n' en E K)
     (auto simp: Let_def split: prod.splits if_splits option.splits)

text \<open>Edge endpoints: a source is always an allocated \<open>Statement\<close>; a target is an allocated
  \<open>Statement\<close>, the own \<^term>\<open>FunctionResult p\<close>, or the continuation.  The continuation
  disjunct is what continuation passing adds, and it is what lets the two \<^const>\<open>wf_cfg\<close>
  conditions below be discharged without carrying a side condition through the induction.\<close>
lemma compile_E_shape:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, a, v) \<in> E
   \<Longrightarrow> (\<exists>j. u = Statement j)
       \<and> (v = k \<or> v = FunctionResult p \<or> (\<exists>j. v = Statement j))"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  then obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, en2, E2, K2)"
    and E: "E = E1 \<union> E2"
    by (auto simp: Let_def split: prod.splits)
  consider (L) "(u, a, v) \<in> E1" | (R) "(u, a, v) \<in> E2"
    using Seq.prems(2) E by auto
  then show ?case
  proof cases
    case L from Seq.IH(1)[OF c1 L] show ?thesis by auto
  next
    case R from Seq.IH(2)[OF c2 R] show ?thesis by auto
  qed
next
  case (If b c1 c2)
  then obtain n1 en1 E1 K1 n2 en2 E2 K2 where
    c1: "compile \<Pi> p c1 k (Suc n) = (n1, en1, E1, K1)"
    and c2: "compile \<Pi> p c2 k n1 = (n2, en2, E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, en2)}
                  \<union> E1 \<union> E2"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  have e2: "en2 = Statement n1" using compile_entry[OF c2] .
  consider (Guard) "(u, a, v) \<in> {(Statement n, EA_Assume b, en1),
                                 (Statement n, EA_AssumeNot b, en2)}"
    | (L) "(u, a, v) \<in> E1" | (R) "(u, a, v) \<in> E2"
    using If.prems(2) E by auto
  then show ?case
  proof cases
    case Guard then show ?thesis using e1 e2 by auto
  next
    case L from If.IH(1)[OF c1 L] show ?thesis by auto
  next
    case R from If.IH(2)[OF c2 R] show ?thesis by auto
  qed
next
  case (While b c)
  then obtain n1 en1 E1 K1 where
    c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, en1, E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, en1), (Statement n, EA_AssumeNot b, k)} \<union> E1"
    by (auto split: prod.splits)
  have e1: "en1 = Statement (Suc n)" using compile_entry[OF c1] .
  consider (Guard) "(u, a, v) \<in> {(Statement n, EA_Assume b, en1),
                                 (Statement n, EA_AssumeNot b, k)}"
    | (Body) "(u, a, v) \<in> E1"
    using While.prems(2) E by auto
  then show ?case
  proof cases
    case Guard then show ?thesis using e1 by auto
  next
    case Body from While.IH[OF c1 Body] show ?thesis by auto
  qed
qed (auto split: prod.splits option.splits)

text \<open>Every \<open>EA_Ret\<close> edge lands on the matching \<open>FunctionResult\<close> --- the enclosing
  procedure name in the action equals the one in the target node.\<close>
lemma compile_ret_wf:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E
   \<Longrightarrow> \<forall>r. k \<noteq> FunctionResult r \<Longrightarrow> v = FunctionResult q"
  by (induction c arbitrary: k n n' en E K)
     (auto simp: Let_def split: prod.splits if_splits option.splits)

lemma compile_proc_call_ce_entry:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
  by (auto simp: compile_proc_def Let_def split: prod.splits
       dest: compile_call_ce_entry)

lemma compile_proc_intra_tgt_not_entry:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> (u, a, v) \<in> E \<Longrightarrow> v \<noteq> FunctionEntry q"
  by (auto simp: compile_proc_def Let_def split: prod.splits if_splits
       dest: compile_E_shape compile_entry)

lemma compile_proc_ret_wf:
  "compile_proc \<Pi> p decl n = (n', E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E
   \<Longrightarrow> v = FunctionResult q"
  by (auto simp: compile_proc_def Let_def split: prod.splits if_splits
       dest: compile_ret_wf)

lemma compile_procs_call_ce_entry:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, act, ce, af) \<in> K
   \<Longrightarrow> \<exists>q. ce = FunctionEntry q"
  using compile_procs_calls_origin compile_proc_call_ce_entry by blast

lemma compile_procs_intra_tgt_not_entry:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, a, v) \<in> E \<Longrightarrow> v \<noteq> FunctionEntry q"
  using compile_procs_intra_origin compile_proc_intra_tgt_not_entry by blast

lemma compile_procs_ret_wf:
  "compile_procs \<Pi> ps n = (n', E, K) \<Longrightarrow> (u, EA_Ret e q, v) \<in> E \<Longrightarrow> v = FunctionResult q"
  using compile_procs_intra_origin compile_proc_ret_wf by blast

subsection \<open>The compiled program is well-formed\<close>

theorem compile_prog_wf: "wf_cfg (compile_prog \<Pi> ps main_name main)"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> main_name \<lparr>formals = [], body = main\<rparr> n1 = (n2, Emain, Kmain)"
    and g: "intra (compile_prog \<Pi> ps main_name main) = Eprocs \<union> Emain"
           "calls (compile_prog \<Pi> ps main_name main) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  show ?thesis
    unfolding wf_cfg_def g
    using compile_procs_call_ce_entry[OF procs] compile_proc_call_ce_entry[OF mainc]
      compile_procs_intra_tgt_not_entry[OF procs] compile_proc_intra_tgt_not_entry[OF mainc]
      compile_procs_ret_wf[OF procs] compile_proc_ret_wf[OF mainc]
    by (intro conjI allI impI; elim UnE) blast+
qed

end
