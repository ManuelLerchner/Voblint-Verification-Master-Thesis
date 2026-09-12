theory Live_Nodes
  imports Procedure_Ownership
begin

section \<open>Which compiled nodes can still reach their procedure's result\<close>

text \<open>
  A statement compiled after a \<^const>\<open>Return\<close> is still part of the graph, but no
  execution reaches it, and control there may run into a node with no way out.  This theory
  names the statements that are \<^emph>\<open>live\<close>: those not preceded, within their sequence, by a
  command that cannot fall through.  Every edge out of a live node of procedure \<open>q\<close> lands
  on a live node of \<open>q\<close> (\<open>prog_live_intra\<close>, \<open>prog_live_calls\<close>), and every live node
  reaches \<^term>\<open>FunctionResult q\<close> along intra edges and call-site-to-continuation steps
  (\<open>prog_live_reaches\<close>) --- exactly the steps a routed equation reads backwards.
\<close>

subsection \<open>Reachability inside one activation\<close>

definition local_succ_rel :: "cfg \<Rightarrow> (cfg_node \<times> cfg_node) set" where
  "local_succ_rel g =
     {(u, v). \<exists>a. (u, a, v) \<in> intra g}
     \<union> {(u, k). \<exists>ca q. (u, ca, FunctionEntry q, k) \<in> calls g}"

definition local_reaches :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node \<Rightarrow> bool" where
  "local_reaches g u v \<longleftrightarrow> (u, v) \<in> (local_succ_rel g)\<^sup>*"

lemma local_reaches_refl [simp]: "local_reaches g v v"
  by (simp add: local_reaches_def)

lemma local_reaches_trans:
  "local_reaches g u v \<Longrightarrow> local_reaches g v w \<Longrightarrow> local_reaches g u w"
  unfolding local_reaches_def by (rule rtrancl_trans)

lemma local_reaches_intra_step:
  "(u, a, v) \<in> intra g \<Longrightarrow> local_reaches g v w \<Longrightarrow> local_reaches g u w"
  unfolding local_reaches_def local_succ_rel_def
  by (rule converse_rtrancl_into_rtrancl) blast+

lemma local_reaches_comb_step:
  "(u, ca, FunctionEntry q, k) \<in> calls g \<Longrightarrow> local_reaches g k w \<Longrightarrow> local_reaches g u w"
  unfolding local_reaches_def local_succ_rel_def
  by (rule converse_rtrancl_into_rtrancl) blast+

subsection \<open>Source ranges\<close>

text \<open>
  An intra edge of a compiled fragment leaves one of the fragment's own statements, whose
  ids run from the first id the fragment was given up to the next free one.  This keeps
  facts about one fragment's statements from reaching into another's.
\<close>

lemma compile_intra_source_range:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> (u, a, v) \<in> E
   \<Longrightarrow> \<exists>j. u = Statement j \<and> n \<le> j \<and> j < n'"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  have "n1 = n + csize c1" "n2 = n + csize c1 + csize c2" "n' = n + csize (Seq c1 c2)"
    using compile_next_id[OF c1] compile_next_id[OF c2] compile_next_id[OF Seq.prems(1)]
    by simp_all
  then show ?case using Seq.prems(2) E Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] by fastforce
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, if c1 = SKIP then k else Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, if c2 = SKIP then k else Statement (Suc n + csize c1))} \<union> (if c1 = SKIP then {} else E1) \<union> (if c2 = SKIP then {} else E2)"
    by (rule compile_IfE)
  have ids: "n1 = Suc n + csize c1" "n2 = Suc n + csize c1 + csize c2"
    "n' = n + csize (If b c1 c2)"
    using compile_next_id[OF c1] compile_next_id[OF c2] compile_next_id[OF If.prems(1)]
    by simp_all
  have "u = Statement n \<or> (u, a, v) \<in> E1 \<or> (u, a, v) \<in> E2"
    using If.prems(2) E by (auto split: if_splits)
  then show ?case using ids If.IH(1)[OF c1] If.IH(2)[OF c2] by fastforce
next
  case (While b c)
  from While.prems(1) obtain n1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, k)} \<union> E1"
    by (rule compile_WhileE)
  have "n1 = Suc n + csize c" "n' = n + csize (While b c)"
    using compile_next_id[OF c1] compile_next_id[OF While.prems(1)] by simp_all
  then show ?case using While.prems(2) E While.IH[OF c1] by fastforce
qed (auto split: option.splits)

subsection \<open>Live statements\<close>

text \<open>
  The statements of a compiled fragment that control can reach from its entry: a
  sequence reaches its second half only when the first can fall through.  Dead code
  after a \<^const>\<open>Return\<close> is compiled, but it is not live, and it is the one place a
  node can fail to reach its procedure result.
\<close>

fun live_stmts :: "com \<Rightarrow> nat \<Rightarrow> cfg_node set" where
  "live_stmts (Seq c1 c2) n =
     live_stmts c1 n \<union> (if falls_through c1 then live_stmts c2 (n + csize c1) else {})"
| "live_stmts (If b c1 c2) n =
     insert (Statement n) ((if c1 = SKIP then {} else live_stmts c1 (Suc n))
       \<union> (if c2 = SKIP then {} else live_stmts c2 (Suc n + csize c1)))"
| "live_stmts (While b c) n = insert (Statement n) (live_stmts c (Suc n))"
| "live_stmts c n = {Statement n}"

lemma live_stmts_entry: "Statement n \<in> live_stmts c n"
  by (induction c arbitrary: n) auto

lemma live_stmts_range:
  "x \<in> live_stmts c n \<Longrightarrow> \<exists>j. x = Statement j \<and> n \<le> j \<and> j < n + csize c"
proof (induction c arbitrary: n)
  case (Seq c1 c2)
  then show ?case using csize_pos[of c1] csize_pos[of c2] by (fastforce split: if_splits)
qed (fastforce split: if_splits)+

text \<open>Every edge out of a live statement lands on a live statement, on the procedure result,
  or --- only when the fragment can fall through --- on its continuation.\<close>

lemma compile_live_succ_both:
  assumes "compile \<Pi> p c k n = (n', en, E, K)" and "x \<in> live_stmts c n"
  shows "(\<forall>a y. (x, a, y) \<in> E
            \<longrightarrow> y \<in> live_stmts c n \<or> y = FunctionResult p \<or> (y = k \<and> falls_through c))
       \<and> (\<forall>ca ce y. (x, ca, ce, y) \<in> K
            \<longrightarrow> y \<in> live_stmts c n \<or> (y = k \<and> falls_through c))"
  using assms
proof (induction c arbitrary: k n n' en E K x)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2" and K: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  have i1: "n1 = n + csize c1" using compile_next_id[OF c1] .
  have srcE1: "\<And>u a v. (u, a, v) \<in> E1 \<Longrightarrow> \<exists>j. u = Statement j \<and> j < n + csize c1"
    using compile_intra_source_range[OF c1] i1 by blast
  have srcK1: "\<And>u a ce v. (u, a, ce, v) \<in> K1 \<Longrightarrow> \<exists>j. u = Statement j \<and> j < n + csize c1"
    using compile_calls_source_range[OF c1] i1 by blast
  have srcE2: "\<And>u a v. (u, a, v) \<in> E2 \<Longrightarrow> \<exists>j. u = Statement j \<and> n + csize c1 \<le> j"
    using compile_intra_source_range[OF c2] by blast
  have srcK2: "\<And>u a ce v. (u, a, ce, v) \<in> K2 \<Longrightarrow> \<exists>j. u = Statement j \<and> n + csize c1 \<le> j"
    using compile_calls_source_range[OF c2] by blast
  have e2: "Statement (n + csize c1) \<in> live_stmts c2 (n + csize c1)"
    by (rule live_stmts_entry)
  from Seq.prems(2) consider (L) "x \<in> live_stmts c1 n"
    | (R) "falls_through c1" "x \<in> live_stmts c2 (n + csize c1)"
    by (auto split: if_splits)
  then show ?case
  proof cases
    case L
    obtain j where xj: "x = Statement j" "j < n + csize c1"
      using live_stmts_range[OF L] by blast
    have ih: "(\<forall>a y. (x, a, y) \<in> E1 \<longrightarrow> y \<in> live_stmts c1 n \<or> y = FunctionResult p
                 \<or> (y = Statement (n + csize c1) \<and> falls_through c1))
            \<and> (\<forall>ca ce y. (x, ca, ce, y) \<in> K1 \<longrightarrow> y \<in> live_stmts c1 n
                 \<or> (y = Statement (n + csize c1) \<and> falls_through c1))"
      by (rule Seq.IH(1)[OF c1 L])
    show ?thesis
      unfolding E K using ih e2 xj srcE2 srcK2 by fastforce
  next
    case R
    obtain j where xj: "x = Statement j" "n + csize c1 \<le> j"
      using live_stmts_range[OF R(2)] by blast
    have ih: "(\<forall>a y. (x, a, y) \<in> E2 \<longrightarrow> y \<in> live_stmts c2 (n + csize c1)
                 \<or> y = FunctionResult p \<or> (y = k \<and> falls_through c2))
            \<and> (\<forall>ca ce y. (x, ca, ce, y) \<in> K2 \<longrightarrow> y \<in> live_stmts c2 (n + csize c1)
                 \<or> (y = k \<and> falls_through c2))"
      by (rule Seq.IH(2)[OF c2 R(2)])
    show ?thesis
      unfolding E K using ih R(1) xj srcE1 srcK1 by fastforce
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, if c1 = SKIP then k else Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, if c2 = SKIP then k else Statement (Suc n + csize c1))} \<union> (if c1 = SKIP then {} else E1) \<union> (if c2 = SKIP then {} else E2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_IfE)
  have i1: "n1 = Suc n + csize c1" using compile_next_id[OF c1] .
  have srcE1: "\<And>u a v. (u, a, v) \<in> E1 \<Longrightarrow> \<exists>j. u = Statement j \<and> Suc n \<le> j \<and> j < Suc n + csize c1"
    using compile_intra_source_range[OF c1] i1 by blast
  have srcK1: "\<And>u a ce v. (u, a, ce, v) \<in> K1
                 \<Longrightarrow> \<exists>j. u = Statement j \<and> Suc n \<le> j \<and> j < Suc n + csize c1"
    using compile_calls_source_range[OF c1] i1 by blast
  have srcE2: "\<And>u a v. (u, a, v) \<in> E2 \<Longrightarrow> \<exists>j. u = Statement j \<and> Suc n + csize c1 \<le> j"
    using compile_intra_source_range[OF c2] by blast
  have srcK2: "\<And>u a ce v. (u, a, ce, v) \<in> K2 \<Longrightarrow> \<exists>j. u = Statement j \<and> Suc n + csize c1 \<le> j"
    using compile_calls_source_range[OF c2] by blast
  have e1: "Statement (Suc n) \<in> live_stmts c1 (Suc n)" by (rule live_stmts_entry)
  have e2: "Statement (Suc n + csize c1) \<in> live_stmts c2 (Suc n + csize c1)"
    by (rule live_stmts_entry)
  from If.prems(2) consider (H) "x = Statement n" | (L) "c1 \<noteq> SKIP" "x \<in> live_stmts c1 (Suc n)"
    | (R) "c2 \<noteq> SKIP" "x \<in> live_stmts c2 (Suc n + csize c1)"
    by (auto split: if_splits)
  then show ?case
  proof cases
    case H
    show ?thesis unfolding E K H using e1 e2 srcE1 srcE2 srcK1 srcK2 by (fastforce split: if_splits)
  next
    case L
    obtain j where xj: "x = Statement j" "Suc n \<le> j" "j < Suc n + csize c1"
      using live_stmts_range[OF L(2)] by blast
    note ih = If.IH(1)[OF c1 L(2)]
    show ?thesis unfolding E K using ih xj srcE2 srcK2 L(1) by (fastforce split: if_splits)
  next
    case R
    obtain j where xj: "x = Statement j" "Suc n + csize c1 \<le> j"
      using live_stmts_range[OF R(2)] by blast
    note ih = If.IH(2)[OF c2 R(2)]
    show ?thesis unfolding E K using ih xj srcE1 srcK1 R(1) by (fastforce split: if_splits)
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, k)} \<union> E1"
    and K: "K = K1"
    by (rule compile_WhileE)
  have srcE1: "\<And>u a v. (u, a, v) \<in> E1 \<Longrightarrow> \<exists>j. u = Statement j \<and> Suc n \<le> j"
    using compile_intra_source_range[OF c1] by blast
  have srcK1: "\<And>u a ce v. (u, a, ce, v) \<in> K1 \<Longrightarrow> \<exists>j. u = Statement j \<and> Suc n \<le> j"
    using compile_calls_source_range[OF c1] by blast
  have e1: "Statement (Suc n) \<in> live_stmts c (Suc n)" by (rule live_stmts_entry)
  from While.prems(2) consider (H) "x = Statement n" | (B) "x \<in> live_stmts c (Suc n)"
    by auto
  then show ?case
  proof cases
    case H
    show ?thesis unfolding E K H using e1 srcE1 srcK1 by fastforce
  next
    case B
    obtain j where xj: "x = Statement j" "Suc n \<le> j"
      using live_stmts_range[OF B] by blast
    note ih = While.IH[OF c1 B]
    show ?thesis unfolding E K using ih xj by fastforce
  qed
qed (auto split: option.splits)

lemma compile_live_succ_intra:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> x \<in> live_stmts c n \<Longrightarrow> (x, a, y) \<in> E
   \<Longrightarrow> y \<in> live_stmts c n \<or> y = FunctionResult p \<or> (y = k \<and> falls_through c)"
  using compile_live_succ_both by blast

lemma compile_live_succ_calls:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> x \<in> live_stmts c n \<Longrightarrow> (x, ca, ce, y) \<in> K
   \<Longrightarrow> y \<in> live_stmts c n \<or> (y = k \<and> falls_through c)"
  using compile_live_succ_both by blast

text \<open>Every live statement reaches the continuation, when the fragment can fall through, or
  the procedure result, inside the activation.\<close>

lemma compile_live_reaches:
  assumes "compile \<Pi> p c k n = (n', en, E, K)" and "E \<subseteq> intra g" and "K \<subseteq> calls g"
    and "x \<in> live_stmts c n"
  shows "(falls_through c \<and> local_reaches g x k) \<or> local_reaches g x (FunctionResult p)"
  using assms
proof (induction c arbitrary: k n n' en E K x)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2" and K: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  have sub: "E1 \<subseteq> intra g" "K1 \<subseteq> calls g" "E2 \<subseteq> intra g" "K2 \<subseteq> calls g"
    using Seq.prems(2,3) E K by auto
  note ih2 = Seq.IH(2)[OF c2 sub(3,4)]
  from Seq.prems(4) consider (L) "x \<in> live_stmts c1 n"
    | (R) "falls_through c1" "x \<in> live_stmts c2 (n + csize c1)"
    by (auto split: if_splits)
  then show ?case
  proof cases
    case L
    from Seq.IH(1)[OF c1 sub(1,2) L] show ?thesis
    proof
      assume a: "falls_through c1 \<and> local_reaches g x (Statement (n + csize c1))"
      from ih2[OF live_stmts_entry] show ?thesis
      proof
        assume b: "falls_through c2 \<and> local_reaches g (Statement (n + csize c1)) k"
        have "local_reaches g x k"
          by (rule local_reaches_trans[OF a[THEN conjunct2] b[THEN conjunct2]])
        with a b show ?thesis by simp
      next
        assume b: "local_reaches g (Statement (n + csize c1)) (FunctionResult p)"
        have "local_reaches g x (FunctionResult p)"
          by (rule local_reaches_trans[OF a[THEN conjunct2] b])
        then show ?thesis by simp
      qed
    qed simp
  next
    case R
    from ih2[OF R(2)] show ?thesis using R(1) by auto
  qed
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and E: "E = {(Statement n, EA_Assume b, if c1 = SKIP then k else Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, if c2 = SKIP then k else Statement (Suc n + csize c1))} \<union> (if c1 = SKIP then {} else E1) \<union> (if c2 = SKIP then {} else E2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_IfE)
  have sub: "c1 \<noteq> SKIP \<Longrightarrow> E1 \<subseteq> intra g" "K1 \<subseteq> calls g"
    "c2 \<noteq> SKIP \<Longrightarrow> E2 \<subseteq> intra g" "K2 \<subseteq> calls g"
    using If.prems(2,3) E K by auto
  have ih1: "\<And>y. c1 \<noteq> SKIP \<Longrightarrow> y \<in> live_stmts c1 (Suc n) \<Longrightarrow>
      (falls_through c1 \<and> local_reaches g y k) \<or> local_reaches g y (FunctionResult p)"
    using If.IH(1)[OF c1] sub(1,2) by blast
  have ih2: "\<And>y. c2 \<noteq> SKIP \<Longrightarrow> y \<in> live_stmts c2 (Suc n + csize c1) \<Longrightarrow>
      (falls_through c2 \<and> local_reaches g y k) \<or> local_reaches g y (FunctionResult p)"
    using If.IH(2)[OF c2] sub(3,4) by blast
  have edge1: "(Statement n, EA_Assume b,
      if c1 = SKIP then k else Statement (Suc n)) \<in> intra g"
    using If.prems(2) E by auto
  from If.prems(4) consider (H) "x = Statement n"
    | (L) "c1 \<noteq> SKIP" "x \<in> live_stmts c1 (Suc n)"
    | (R) "c2 \<noteq> SKIP" "x \<in> live_stmts c2 (Suc n + csize c1)"
    by (auto split: if_splits)
  then show ?case
  proof cases
    case H
    show ?thesis
    proof (cases "c1 = SKIP")
      case True
      with edge1 H show ?thesis by (auto intro: local_reaches_intra_step)
    next
      case False
      from ih1[OF False live_stmts_entry] show ?thesis
        using edge1 H False local_reaches_intra_step by auto
    qed
  next
    case L from ih1[OF L] show ?thesis by auto
  next
    case R from ih2[OF R] show ?thesis by auto
  qed
next
  case (While b c)
  from While.prems(1) obtain n1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and E: "E = {(Statement n, EA_Assume b, Statement (Suc n)),
                 (Statement n, EA_AssumeNot b, k)} \<union> E1"
    and K: "K = K1"
    by (rule compile_WhileE)
  have sub: "E1 \<subseteq> intra g" "K1 \<subseteq> calls g" using While.prems(2,3) E K by auto
  have exit: "local_reaches g (Statement n) k"
    using While.prems(2) E by (auto intro: local_reaches_intra_step)
  from While.prems(4) consider (H) "x = Statement n" | (B) "x \<in> live_stmts c (Suc n)"
    by auto
  then show ?case
  proof cases
    case H show ?thesis using exit H by simp
  next
    case B
    from While.IH[OF c1 sub B] show ?thesis
      using exit local_reaches_trans by auto
  qed
next
  case (Call dst q actuals)
  then show ?case
    by (auto split: option.splits intro: local_reaches_intra_step local_reaches_comb_step)
next
  case (Return e)
  then show ?case by (auto intro: local_reaches_intra_step)
qed (auto intro: local_reaches_intra_step)

subsection \<open>A procedure's live nodes\<close>

text \<open>
  A procedure's live nodes are its entry, its result, the live statements of its body,
  and the node after the body when the body can fall through.  Each of them reaches the
  result.
\<close>

definition proc_live :: "pname \<Rightarrow> proc_decl \<Rightarrow> nat \<Rightarrow> cfg_node set" where
  "proc_live q d m =
     insert (FunctionEntry q) (insert (FunctionResult q)
       (live_stmts (body d) m
        \<union> (if falls_through (body d) then {Statement (m + csize (body d))} else {})))"

lemma compile_proc_live_reaches:
  assumes cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    and Ep: "Ep \<subseteq> intra g" and Kp: "Kp \<subseteq> calls g"
    and x: "x \<in> proc_live q d m"
  shows "local_reaches g x (FunctionResult q)"
proof -
  let ?r = "Statement (m + csize (body d))"
  from cp obtain Eb where
      cb: "compile \<Pi> q (body d) ?r m = (m + csize (body d), Statement m, Eb, Kp)"
    and E: "Ep = insert (FunctionEntry q, EA_Body q, Statement m)
                  (if falls_through (body d)
                   then insert (?r, EA_Ret None q, FunctionResult q) Eb else Eb)"
    by (rule compile_procE)
  have Eb: "Eb \<subseteq> intra g" using E Ep by (auto split: if_splits)
  have epi: "falls_through (body d) \<Longrightarrow> local_reaches g ?r (FunctionResult q)"
    using E Ep by (auto intro: local_reaches_intra_step)
  have body: "\<And>y. y \<in> live_stmts (body d) m \<Longrightarrow> local_reaches g y (FunctionResult q)"
    using compile_live_reaches[OF cb Eb Kp] epi local_reaches_trans by blast
  have ent: "local_reaches g (FunctionEntry q) (FunctionResult q)"
    using E Ep body[OF live_stmts_entry] by (auto intro: local_reaches_intra_step)
  show ?thesis using x body ent epi by (auto simp: proc_live_def split: if_splits)
qed

lemma compile_proc_live_succ:
  assumes cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)" and x: "x \<in> proc_live q d m"
  shows "(x, a, y) \<in> Ep \<Longrightarrow> y \<in> proc_live q d m"
    and "(x, ca, ce, y) \<in> Kp \<Longrightarrow> y \<in> proc_live q d m"
proof -
  let ?r = "Statement (m + csize (body d))"
  from cp obtain Eb where
      cb: "compile \<Pi> q (body d) ?r m = (m + csize (body d), Statement m, Eb, Kp)"
    and E: "Ep = insert (FunctionEntry q, EA_Body q, Statement m)
                  (if falls_through (body d)
                   then insert (?r, EA_Ret None q, FunctionResult q) Eb else Eb)"
    by (rule compile_procE)
  have live_of_src: "x \<in> live_stmts (body d) m"
    if "x = Statement j" "m \<le> j" "j < m + csize (body d)" for j
    using x that by (auto simp: proc_live_def split: if_splits)
  show "y \<in> proc_live q d m" if e: "(x, a, y) \<in> Ep"
  proof -
    from e E consider (Ent) "x = FunctionEntry q" "y = Statement m"
      | (Epi) "falls_through (body d)" "x = ?r" "y = FunctionResult q"
      | (Body) "(x, a, y) \<in> Eb"
      by (auto split: if_splits)
    then show ?thesis
    proof cases
      case Ent then show ?thesis by (simp add: proc_live_def live_stmts_entry)
    next
      case Epi then show ?thesis by (simp add: proc_live_def)
    next
      case Body
      obtain j where "x = Statement j" "m \<le> j" "j < m + csize (body d)"
        using compile_intra_source_range[OF cb Body] by blast
      from compile_live_succ_intra[OF cb live_of_src[OF this] Body] show ?thesis
        by (auto simp: proc_live_def)
    qed
  qed
  show "y \<in> proc_live q d m" if e: "(x, ca, ce, y) \<in> Kp"
  proof -
    obtain j where "x = Statement j" "m \<le> j" "j < m + csize (body d)"
      using compile_calls_source_range[OF cb e] by blast
    from compile_live_succ_calls[OF cb live_of_src[OF this] e] show ?thesis
      by (auto simp: proc_live_def)
  qed
qed

lemma proc_live_pfn:
  assumes cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)" and x: "x \<in> proc_live q d m"
  shows "x \<in> pfn q m m'"
proof -
  from cp have m': "m' = Suc (m + csize (body d))" by (rule compile_procE)
  show ?thesis
    using x live_stmts_range[of x "body d" m] m'
    by (fastforce simp: proc_live_def pfn_def split: if_splits)
qed

subsection \<open>The whole program\<close>

text \<open>
  Each declared procedure's fragment sits inside the compiled program, so its live nodes,
  their edges and their reachability carry over to the whole graph, with the main
  procedure's entry among them.
\<close>

lemma compile_prog_proc_frag_sub:
  assumes wf: "wf_compile_input gs \<Pi> ps" and decl: "\<Pi> q = Some d"
  obtains m m' Ep Kp where
    "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    "Ep \<subseteq> intra (compile_prog \<Pi> ps)" "Kp \<subseteq> calls (compile_prog \<Pi> ps)"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1
                  = (n2, Emain, Kmain)"
    and EI: "intra (compile_prog \<Pi> ps) = Eprocs \<union> Emain"
    and KC: "calls (compile_prog \<Pi> ps) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  show thesis
  proof (cases "q = prog_main_name")
    case True
    have dd: "d = \<lparr>formals = [], body = (main_body \<Pi>)\<rparr>"
      using decl True wf_compile_inputD(2)[OF wf] by simp
    have "(FunctionEntry q, EA_Body q, Statement n1) \<in> intra (compile_prog \<Pi> ps)"
      using EI compile_proc_entry_edge[OF mainc] True by auto
    then show ?thesis using that[of n1 n2 Emain Kmain] mainc True dd EI KC by simp
  next
    case False
    have rin: "q \<in> set ps" using decl wf_compile_inputD(10)[OF wf] False by auto
    from compile_procs_member_frag[OF procs wf_compile_inputD(9)[OF wf] rin decl]
    obtain m m' Ep Kp where cp0: "compile_proc \<Pi> q d m = (m', Ep, Kp)"
        and sub: "Ep \<subseteq> Eprocs" "Kp \<subseteq> Kprocs"
      by blast
    have "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
      using EI sub compile_proc_entry_edge[OF cp0] by auto
    then show ?thesis using that cp0 sub EI KC by blast
  qed
qed

definition prog_live :: "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> cfg_node \<Rightarrow> bool" where
  "prog_live \<Pi> ps q x \<longleftrightarrow>
     (\<exists>d m m' Ep Kp. \<Pi> q = Some d \<and> compile_proc \<Pi> q d m = (m', Ep, Kp)
        \<and> (FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)
        \<and> Ep \<subseteq> intra (compile_prog \<Pi> ps) \<and> Kp \<subseteq> calls (compile_prog \<Pi> ps)
        \<and> x \<in> proc_live q d m)"

lemma prog_live_entry:
  assumes wf: "wf_compile_input gs \<Pi> ps" and decl: "\<Pi> q = Some d"
  shows "prog_live \<Pi> ps q (FunctionEntry q)"
  using compile_prog_proc_frag_sub[OF wf decl] decl
  unfolding prog_live_def proc_live_def by (metis insertI1)

lemma prog_live_result:
  "prog_live \<Pi> ps q x \<Longrightarrow> prog_live \<Pi> ps q (FunctionResult q)"
  unfolding prog_live_def proc_live_def by blast

lemma prog_live_reaches:
  "prog_live \<Pi> ps q x \<Longrightarrow> local_reaches (compile_prog \<Pi> ps) x (FunctionResult q)"
  unfolding prog_live_def using compile_proc_live_reaches by force

lemma prog_live_intra:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and live: "prog_live \<Pi> ps q u" and e: "(u, a, v) \<in> intra (compile_prog \<Pi> ps)"
  shows "prog_live \<Pi> ps q v"
proof -
  from live obtain d m m' Ep Kp where
      decl: "\<Pi> q = Some d" and cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    and sub: "Ep \<subseteq> intra (compile_prog \<Pi> ps)" "Kp \<subseteq> calls (compile_prog \<Pi> ps)"
    and u: "u \<in> proc_live q d m"
    unfolding prog_live_def by blast
  have "(u, a, v) \<in> Ep"
    using compile_prog_entry_frag[OF wf decl cp ent] proc_live_pfn[OF cp u] e by blast
  then have "v \<in> proc_live q d m" by (rule compile_proc_live_succ(1)[OF cp u])
  then show ?thesis unfolding prog_live_def using decl cp ent sub by blast
qed

lemma prog_live_calls:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and live: "prog_live \<Pi> ps q u" and e: "(u, ca, ce, k) \<in> calls (compile_prog \<Pi> ps)"
  shows "prog_live \<Pi> ps q k"
proof -
  from live obtain d m m' Ep Kp where
      decl: "\<Pi> q = Some d" and cp: "compile_proc \<Pi> q d m = (m', Ep, Kp)"
    and ent: "(FunctionEntry q, EA_Body q, Statement m) \<in> intra (compile_prog \<Pi> ps)"
    and sub: "Ep \<subseteq> intra (compile_prog \<Pi> ps)" "Kp \<subseteq> calls (compile_prog \<Pi> ps)"
    and u: "u \<in> proc_live q d m"
    unfolding prog_live_def by blast
  have "(u, ca, ce, k) \<in> Kp"
    using compile_prog_entry_frag[OF wf decl cp ent] proc_live_pfn[OF cp u] e by blast
  then have "k \<in> proc_live q d m" by (rule compile_proc_live_succ(2)[OF cp u])
  then show ?thesis unfolding prog_live_def using decl cp ent sub by blast
qed

lemma prog_live_main_entry:
  assumes wf: "wf_compile_input gs \<Pi> ps"
  shows "prog_live \<Pi> ps prog_main_name (cfg_entry (compile_prog \<Pi> ps))"
  using prog_live_entry[OF wf wf_compile_inputD(2)[OF wf]] by simp

subsection \<open>Call targets are declared\<close>

text \<open>
  A call edge of a well-formed program enters only a declared procedure, so every callee
  has a fragment, and its entry is live.
\<close>

lemma compile_calls_target_declared:
  "compile \<Pi> p c k n = (n', en, E, K) \<Longrightarrow> wf_source_com \<Pi> c
   \<Longrightarrow> (u, ca, FunctionEntry q, k') \<in> K \<Longrightarrow> \<exists>d. \<Pi> q = Some d"
proof (induction c arbitrary: k n n' en E K)
  case (Seq c1 c2)
  from Seq.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 (Statement (n + csize c1)) n = (n1, Statement n, E1, K1)"
    and c2: "compile \<Pi> p c2 k (n + csize c1) = (n2, Statement (n + csize c1), E2, K2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  show ?case using Seq.IH(1)[OF c1] Seq.IH(2)[OF c2] Seq.prems(2,3) K by auto
next
  case (If b c1 c2)
  from If.prems(1) obtain n1 E1 K1 n2 E2 K2 where
      c1: "compile \<Pi> p c1 k (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and c2: "compile \<Pi> p c2 k (Suc n + csize c1) = (n2, Statement (Suc n + csize c1), E2, K2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_IfE)
  show ?case using If.IH(1)[OF c1] If.IH(2)[OF c2] If.prems(2,3) K by auto
next
  case (While b c)
  from While.prems(1) obtain n1 E1 K1 where
      c1: "compile \<Pi> p c (Statement n) (Suc n) = (n1, Statement (Suc n), E1, K1)"
    and K: "K = K1"
    by (rule compile_WhileE)
  show ?case using While.IH[OF c1] While.prems(2,3) K by auto
qed (auto split: option.splits)

lemma compile_prog_calls_target_declared:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and e: "(u, ca, FunctionEntry q, k) \<in> calls (compile_prog \<Pi> ps)"
  shows "\<exists>d. \<Pi> q = Some d"
proof -
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = (main_body \<Pi>)\<rparr> n1
                  = (n2, Emain, Kmain)"
    and KC: "calls (compile_prog \<Pi> ps) = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  from e KC consider (P) "(u, ca, FunctionEntry q, k) \<in> Kprocs"
    | (M) "(u, ca, FunctionEntry q, k) \<in> Kmain"
    by auto
  then show ?thesis
  proof cases
    case P
    from compile_procs_calls_origin[OF procs P] obtain r decl m m' Ep Kp where
        decl: "\<Pi> r = Some decl" and cp: "compile_proc \<Pi> r decl m = (m', Ep, Kp)"
      and eK: "(u, ca, FunctionEntry q, k) \<in> Kp"
      by blast
    from cp obtain Eb where
        cb: "compile \<Pi> r (body decl) (Statement (m + csize (body decl))) m
               = (m + csize (body decl), Statement m, Eb, Kp)"
      by (rule compile_procE)
    have "wf_source_com \<Pi> (body decl)"
      using wf_compile_inputD(5)[OF wf decl] by (simp add: wf_proc_decl_def)
    from compile_calls_target_declared[OF cb this eK] show ?thesis .
  next
    case M
    from mainc obtain Eb where
        cb: "compile \<Pi> prog_main_name (main_body \<Pi>) (Statement (n1 + csize (main_body \<Pi>))) n1
               = (n1 + csize (main_body \<Pi>), Statement n1, Eb, Kmain)"
      by (rule compile_procE) simp
    from compile_calls_target_declared[OF cb wf_compile_inputD(3)[OF wf] M] show ?thesis .
  qed
qed

lemma prog_live_callee_entry:
  assumes wf: "wf_compile_input gs \<Pi> ps"
    and e: "(u, ca, FunctionEntry q, k) \<in> calls (compile_prog \<Pi> ps)"
  shows "prog_live \<Pi> ps q (FunctionEntry q)"
  using compile_prog_calls_target_declared[OF wf e] prog_live_entry[OF wf] by blast

end
