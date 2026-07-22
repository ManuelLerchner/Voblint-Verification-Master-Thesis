theory Control_Simulation
  imports Located_Exec
begin

section \<open>Source-to-CFG located simulation\<close>

text \<open>
  The compiled execution \<^const>\<open>cstep\<close> simulates the source small-step \<^const>\<open>pstep\<close>.
  Both run an activation stack: a source frame carries the caller store and destination,
  a \<open>cframe\<close> additionally records the CFG continuation node.  The simulation relation
  is direct --- literal store equality, \<^const>\<open>control_at\<close> locating the active residual at the
  CFG node, and \<^const>\<open>frames_match\<close> tying the two stacks one-for-one.

  This layer proves the static \<^emph>\<open>compiler-location\<close> facts: a located residual whose head is a
  base command emits exactly the CFG edge the compiler generated for it, and the head's source
  step re-locates the successor residual.  The intra, call, and return step simulations are
  built on these.
\<close>

subsection \<open>Located base residuals emit their compiled edge\<close>

text \<open>A located assignment sits on the compiled \<^term>\<open>EA_Assign\<close> edge, and its source step
  re-locates the residual \<^const>\<open>SKIP\<close> at the successor node.\<close>
lemma control_at_assign_edge:
  "control_at \<Pi> p c0 n r v \<Longrightarrow> r = Assign x a \<Longrightarrow>
   compile \<Pi> p c0 n = (n', en, ex, E, K) \<Longrightarrow>
   \<exists>k. v = Statement k \<and> (Statement k, EA_Assign x a, Statement (Suc k)) \<in> E
       \<and> control_at \<Pi> p c0 n SKIP (Statement (Suc k))"
proof (induction arbitrary: n' en ex E K rule: control_at.induct)
  case (Assign x' a' n0)
  then show ?case by (auto intro: control_at.AssignDone)
next
  case (SeqRight c1 n n1 en1 ex1 E1 K1 c2 r v)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] obtain k where
    k: "v = Statement k" "(Statement k, EA_Assign x a, Statement (Suc k)) \<in> E2"
       "control_at \<Pi> p c2 n1 SKIP (Statement (Suc k))" by blast
  from SeqRight.prems(2) SeqRight.hyps(1) c2c have "E2 \<subseteq> E" by (auto split: prod.splits)
  moreover have "control_at \<Pi> p (Seq c1 c2) n SKIP (Statement (Suc k))"
    using control_at.SeqRight[OF SeqRight.hyps(1) k(3)] .
  ultimately show ?case using k by blast
next
  case (IfLeft c1 n r v b c2)
  obtain n1 en1 ex1 E1 K1 where c1c: "compile \<Pi> p c1 (Suc n) = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  from IfLeft.IH[OF IfLeft.prems(1) c1c] obtain k where
    k: "v = Statement k" "(Statement k, EA_Assign x a, Statement (Suc k)) \<in> E1"
       "control_at \<Pi> p c1 (Suc n) SKIP (Statement (Suc k))" by blast
  from IfLeft.prems(2) c1c have "E1 \<subseteq> E" by (auto split: prod.splits)
  moreover have "control_at \<Pi> p (If b c1 c2) n SKIP (Statement (Suc k))"
    using control_at.IfLeft[OF k(3)] .
  ultimately show ?case using k by blast
next
  case (IfRight c1 n n1 en1 ex1 E1 K1 c2 r v b)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  from IfRight.IH[OF IfRight.prems(1) c2c] obtain k where
    k: "v = Statement k" "(Statement k, EA_Assign x a, Statement (Suc k)) \<in> E2"
       "control_at \<Pi> p c2 n1 SKIP (Statement (Suc k))" by blast
  from IfRight.prems(2) IfRight.hyps(1) c2c have "E2 \<subseteq> E" by (auto split: prod.splits)
  moreover have "control_at \<Pi> p (If b c1 c2) n SKIP (Statement (Suc k))"
    using control_at.IfRight[OF IfRight.hyps(1) k(3)] .
  ultimately show ?case using k by blast
qed simp_all

text \<open>A located call sits on the compiled \<^term>\<open>CallEdge\<close> into the callee entry, and its source
  step re-locates \<^const>\<open>SKIP\<close> at the continuation node.\<close>
lemma control_at_call_edge:
  "control_at \<Pi> p c0 n r v \<Longrightarrow> r = Call dst q actuals \<Longrightarrow>
   compile \<Pi> p c0 n = (n', en, ex, E, K) \<Longrightarrow>
   \<exists>k. v = Statement k
       \<and> (Statement k, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
          FunctionEntry q, Statement (Suc k)) \<in> K
       \<and> control_at \<Pi> p c0 n SKIP (Statement (Suc k))"
proof (induction arbitrary: n' en ex E K rule: control_at.induct)
  case (CallHead dst' q' actuals' n0)
  then show ?case by (auto intro: control_at.CallDone)
next
  case (SeqRight c1 n n1 en1 ex1 E1 K1 c2 r v)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] obtain k where
    k: "v = Statement k"
       "(Statement k, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
         FunctionEntry q, Statement (Suc k)) \<in> K2"
       "control_at \<Pi> p c2 n1 SKIP (Statement (Suc k))" by blast
  from SeqRight.prems(2) SeqRight.hyps(1) c2c have "K2 \<subseteq> K" by (auto split: prod.splits)
  moreover have "control_at \<Pi> p (Seq c1 c2) n SKIP (Statement (Suc k))"
    using control_at.SeqRight[OF SeqRight.hyps(1) k(3)] .
  ultimately show ?case using k by blast
next
  case (IfLeft c1 n r v b c2)
  obtain n1 en1 ex1 E1 K1 where c1c: "compile \<Pi> p c1 (Suc n) = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  from IfLeft.IH[OF IfLeft.prems(1) c1c] obtain k where
    k: "v = Statement k"
       "(Statement k, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
         FunctionEntry q, Statement (Suc k)) \<in> K1"
       "control_at \<Pi> p c1 (Suc n) SKIP (Statement (Suc k))" by blast
  from IfLeft.prems(2) c1c have "K1 \<subseteq> K" by (auto split: prod.splits)
  moreover have "control_at \<Pi> p (If b c1 c2) n SKIP (Statement (Suc k))"
    using control_at.IfLeft[OF k(3)] .
  ultimately show ?case using k by blast
next
  case (IfRight c1 n n1 en1 ex1 E1 K1 c2 r v b)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  from IfRight.IH[OF IfRight.prems(1) c2c] obtain k where
    k: "v = Statement k"
       "(Statement k, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
         FunctionEntry q, Statement (Suc k)) \<in> K2"
       "control_at \<Pi> p c2 n1 SKIP (Statement (Suc k))" by blast
  from IfRight.prems(2) IfRight.hyps(1) c2c have "K2 \<subseteq> K" by (auto split: prod.splits)
  moreover have "control_at \<Pi> p (If b c1 c2) n SKIP (Statement (Suc k))"
    using control_at.IfRight[OF IfRight.hyps(1) k(3)] .
  ultimately show ?case using k by blast
qed simp_all

text \<open>A located \<^const>\<open>Return\<close> sits on the compiled \<^term>\<open>EA_Ret\<close> edge into
  \<^term>\<open>FunctionResult p\<close> --- the enclosing procedure's result node.\<close>
lemma control_at_return_edge:
  "control_at \<Pi> p c0 n r v \<Longrightarrow> r = Return e \<Longrightarrow>
   compile \<Pi> p c0 n = (n', en, ex, E, K) \<Longrightarrow>
   \<exists>k. v = Statement k \<and> (Statement k, EA_Ret e p, FunctionResult p) \<in> E"
proof (induction arbitrary: n' en ex E K rule: control_at.induct)
  case (ReturnHead e' n0)
  then show ?case by auto
next
  case (SeqRight c1 n n1 en1 ex1 E1 K1 c2 r v)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] obtain k where
    k: "v = Statement k" "(Statement k, EA_Ret e p, FunctionResult p) \<in> E2" by blast
  from SeqRight.prems(2) SeqRight.hyps(1) c2c have "E2 \<subseteq> E" by (auto split: prod.splits)
  then show ?case using k by blast
next
  case (IfLeft c1 n r v b c2)
  obtain n1 en1 ex1 E1 K1 where c1c: "compile \<Pi> p c1 (Suc n) = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  from IfLeft.IH[OF IfLeft.prems(1) c1c] obtain k where
    k: "v = Statement k" "(Statement k, EA_Ret e p, FunctionResult p) \<in> E1" by blast
  from IfLeft.prems(2) c1c have "E1 \<subseteq> E" by (auto split: prod.splits)
  then show ?case using k by blast
next
  case (IfRight c1 n n1 en1 ex1 E1 K1 c2 r v b)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  from IfRight.IH[OF IfRight.prems(1) c2c] obtain k where
    k: "v = Statement k" "(Statement k, EA_Ret e p, FunctionResult p) \<in> E2" by blast
  from IfRight.prems(2) IfRight.hyps(1) c2c have "E2 \<subseteq> E" by (auto split: prod.splits)
  then show ?case using k by blast
qed simp_all

text \<open>A located conditional sits on both compiled assume edges; each branch re-locates its
  operand at the branch entry (the source \<open>IfTrue\<close> / \<open>IfFalse\<close> targets).  The residual also
  arises from a loop unfolding (\<^const>\<open>While\<close> steps to \<open>If b (Seq c (While b c)) SKIP\<close>), so the
  \<open>WhileUnfolded\<close> case is real: the true branch re-locates the loop body followed by the
  loop, the false branch re-locates \<^const>\<open>SKIP\<close> at the loop exit.\<close>
lemma control_at_if_edges:
  "control_at \<Pi> p c0 n r v \<Longrightarrow> r = If b c1 c2 \<Longrightarrow> source_com r \<Longrightarrow>
   compile \<Pi> p c0 n = (n', en, ex, E, K) \<Longrightarrow>
   \<exists>k en1 en2. v = Statement k
       \<and> (Statement k, EA_Assume b, en1) \<in> E \<and> (Statement k, EA_AssumeNot b, en2) \<in> E
       \<and> control_at \<Pi> p c0 n c1 en1 \<and> control_at \<Pi> p c0 n c2 en2"
proof (induction arbitrary: n' en ex E K rule: control_at.induct)
  case (IfHead b' c1' c2' n0)
  obtain n1 en1 ex1 E1 K1 where c1c: "compile \<Pi> p c1' (Suc n0) = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2' n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  from IfHead.prems(1) have r: "b' = b" "c1' = c1" "c2' = c2" by auto
  have en1v: "en1 = Statement (Suc n0)" using compile_entry_node[OF c1c] .
  have en2v: "en2 = Statement n1" using compile_entry_node[OF c2c] .
  from IfHead.prems(2) r have src: "source_com c1'" "source_com c2'" by auto
  have a1: "(Statement n0, EA_Assume b', en1) \<in> E"
   and a2: "(Statement n0, EA_AssumeNot b', en2) \<in> E"
    using IfHead.prems(3) c1c c2c by (auto split: prod.splits)
  have ca1: "control_at \<Pi> p (If b' c1' c2') n0 c1' en1"
    using control_at.IfLeft[OF control_at_initial[OF src(1), of \<Pi> p "Suc n0"]] en1v by simp
  have ca2: "control_at \<Pi> p (If b' c1' c2') n0 c2' en2"
    using control_at.IfRight[OF c1c control_at_initial[OF src(2), of \<Pi> p n1]] en2v by simp
  from a1 a2 ca1 ca2 r show ?case by auto
next
  case (SeqRight c1' n n1 en1 ex1 E1 K1 c2' r v)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2' n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  from SeqRight.IH[OF SeqRight.prems(1) SeqRight.prems(2) c2c] obtain k e1 e2 where
    k: "v = Statement k" "(Statement k, EA_Assume b, e1) \<in> E2"
       "(Statement k, EA_AssumeNot b, e2) \<in> E2"
       "control_at \<Pi> p c2' n1 c1 e1" "control_at \<Pi> p c2' n1 c2 e2" by blast
  from SeqRight.prems(3) SeqRight.hyps(1) c2c have "E2 \<subseteq> E" by (auto split: prod.splits)
  moreover have "control_at \<Pi> p (Seq c1' c2') n c1 e1" "control_at \<Pi> p (Seq c1' c2') n c2 e2"
    using control_at.SeqRight[OF SeqRight.hyps(1) k(4)] control_at.SeqRight[OF SeqRight.hyps(1) k(5)] .
  ultimately show ?case using k by blast
next
  case (IfLeft c1' n r v b' c2')
  obtain n1 en1 ex1 E1 K1 where c1c: "compile \<Pi> p c1' (Suc n) = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  from IfLeft.IH[OF IfLeft.prems(1) IfLeft.prems(2) c1c] obtain k e1 e2 where
    k: "v = Statement k" "(Statement k, EA_Assume b, e1) \<in> E1"
       "(Statement k, EA_AssumeNot b, e2) \<in> E1"
       "control_at \<Pi> p c1' (Suc n) c1 e1" "control_at \<Pi> p c1' (Suc n) c2 e2" by blast
  from IfLeft.prems(3) c1c have "E1 \<subseteq> E" by (auto split: prod.splits)
  moreover have "control_at \<Pi> p (If b' c1' c2') n c1 e1" "control_at \<Pi> p (If b' c1' c2') n c2 e2"
    using control_at.IfLeft[OF k(4)] control_at.IfLeft[OF k(5)] .
  ultimately show ?case using k by blast
next
  case (IfRight c1' n n1 en1 ex1 E1 K1 c2' r v b')
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2' n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  from IfRight.IH[OF IfRight.prems(1) IfRight.prems(2) c2c] obtain k e1 e2 where
    k: "v = Statement k" "(Statement k, EA_Assume b, e1) \<in> E2"
       "(Statement k, EA_AssumeNot b, e2) \<in> E2"
       "control_at \<Pi> p c2' n1 c1 e1" "control_at \<Pi> p c2' n1 c2 e2" by blast
  from IfRight.prems(3) IfRight.hyps(1) c2c have "E2 \<subseteq> E" by (auto split: prod.splits)
  moreover have "control_at \<Pi> p (If b' c1' c2') n c1 e1" "control_at \<Pi> p (If b' c1' c2') n c2 e2"
    using control_at.IfRight[OF IfRight.hyps(1) k(4)] control_at.IfRight[OF IfRight.hyps(1) k(5)] .
  ultimately show ?case using k by blast
next
  case (WhileUnfolded b'' c'' n0)
  obtain n1 en1 ex1 E1 K1 where cc: "compile \<Pi> p c'' (Suc n0) = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  from WhileUnfolded.prems(1) have r: "b'' = b" "Seq c'' (While b'' c'') = c1" "SKIP = c2" by auto
  have en1v: "en1 = Statement (Suc n0)" using compile_entry_node[OF cc] .
  from WhileUnfolded.prems(2) have src: "source_com c''" by auto
  have a1: "(Statement n0, EA_Assume b'', en1) \<in> E"
   and a2: "(Statement n0, EA_AssumeNot b'', Statement n1) \<in> E"
   and exv: "ex = Statement n1"
    using WhileUnfolded.prems(3) cc by (auto split: prod.splits)
  have ca1: "control_at \<Pi> p (While b'' c'') n0 (Seq c'' (While b'' c'')) en1"
    using control_at.WhileBody[OF control_at_initial[OF src, of \<Pi> p "Suc n0"]] en1v by simp
  have ca2: "control_at \<Pi> p (While b'' c'') n0 SKIP (Statement n1)"
    using control_at.WhileDone[OF WhileUnfolded.prems(3)] exv by simp
  from a1 a2 ca1 ca2 r show ?case by auto
qed simp_all

subsection \<open>SKIP relocation to the fragment exit\<close>

text \<open>A located \<^const>\<open>SKIP\<close> --- a completed sub-command --- reaches its fragment's normal-exit
  node by the compiler's \<^term>\<open>EA_Nop\<close> edges (branch joins and empty sequencing).  This is the
  reusable relocation primitive under \<^const>\<open>Seq\<close> completion.\<close>
lemma control_at_skip_to_exit:
  "control_at \<Pi> p c0 n r v \<Longrightarrow> r = SKIP \<Longrightarrow>
   compile \<Pi> p c0 n = (n', en, ex, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow>
   star (cstep g) (v, s, stk) (ex, s, stk)"
proof (induction arbitrary: n' en ex E K rule: control_at.induct)
  case (Skip n0)
  then show ?case by (auto intro: star.refl)
next
  case (AssignDone x a n0)
  then show ?case by (auto intro: star.refl)
next
  case (CallDone dst q actuals n0)
  then show ?case by (auto intro: star.refl)
next
  case (IfDone b c1 c2 n0 mn men mex mE mK)
  have "mex = ex" using IfDone.hyps IfDone.prems(2) by simp
  then show ?case by (auto intro: star.refl)
next
  case (WhileDone b c n0 mn men mex mE mK)
  have "mex = ex" using WhileDone.hyps WhileDone.prems(2) by simp
  then show ?case by (auto intro: star.refl)
next
  case (SeqRight c1 n0 n1 en1 ex1 E1 K1 c2 r v)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  have sub: "E2 \<subseteq> E" and exeq: "ex = ex2"
    using SeqRight.prems(2) SeqRight.hyps(1) c2c by (auto split: prod.splits)
  have "star (cstep g) (v, s, stk) (ex2, s, stk)"
    using SeqRight.IH[OF SeqRight.prems(1) c2c subset_trans[OF sub SeqRight.prems(3)]] .
  then show ?case using exeq by simp
next
  case (IfLeft c1 n0 r v b c2)
  obtain n1 en1 ex1 E1 K1 where c1c: "compile \<Pi> p c1 (Suc n0) = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  have sub1: "E1 \<subseteq> E" and nop: "(ex1, EA_Nop, Statement n2) \<in> E" and exeq: "ex = Statement n2"
    using IfLeft.prems(2) c1c c2c by (auto split: prod.splits)
  have s1: "star (cstep g) (v, s, stk) (ex1, s, stk)"
    using IfLeft.IH[OF IfLeft.prems(1) c1c subset_trans[OF sub1 IfLeft.prems(3)]] .
  have "(ex1, EA_Nop, Statement n2) \<in> intra g" using nop IfLeft.prems(3) by blast
  then have "cstep g (ex1, s, stk) (Statement n2, s, stk)" by (rule cstep_nop)
  with s1 exeq show ?case by (meson star_trans cstep_star_single)
next
  case (IfRight c1 n0 n1 en1 ex1 E1 K1 c2 r v b)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  have sub2: "E2 \<subseteq> E" and nop: "(ex2, EA_Nop, Statement n2) \<in> E" and exeq: "ex = Statement n2"
    using IfRight.prems(2) IfRight.hyps(1) c2c by (auto split: prod.splits)
  have s2: "star (cstep g) (v, s, stk) (ex2, s, stk)"
    using IfRight.IH[OF IfRight.prems(1) c2c subset_trans[OF sub2 IfRight.prems(3)]] .
  have "(ex2, EA_Nop, Statement n2) \<in> intra g" using nop IfRight.prems(3) by blast
  then have "cstep g (ex2, s, stk) (Statement n2, s, stk)" by (rule cstep_nop)
  with s2 exeq show ?case by (meson star_trans cstep_star_single)
qed simp_all

subsection \<open>Completed-head sequence relocation\<close>

text \<open>When a sequence's head has completed (\<^term>\<open>Seq SKIP c2\<close>), control relocates to the
  continuation \<^term>\<open>c2\<close> at its entry: the head reaches its exit (\<open>control_at_skip_to_exit\<close>) and
  the compiler's sequencing \<^term>\<open>EA_Nop\<close> --- or the loop back-edge, when the continuation is the
  enclosing \<^const>\<open>While\<close> --- carries control to the continuation entry.\<close>
lemma control_at_seq_skip_reloc:
  "control_at \<Pi> p c0 n r v \<Longrightarrow> r = Seq SKIP c2 \<Longrightarrow>
   compile \<Pi> p c0 n = (n', en, ex, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> source_com c0 \<Longrightarrow>
   \<exists>v'. control_at \<Pi> p c0 n c2 v' \<and> star (cstep g) (v, s, stk) (v', s, stk)"
proof (induction arbitrary: n' en ex E K rule: control_at.induct)
  case (SeqLeft c1 n0 r_in v c2r)
  from SeqLeft.prems(1) have ri: "r_in = SKIP" and c2eq: "c2r = c2" by auto
  obtain n1 en1 ex1 E1 K1 where c1c: "compile \<Pi> p c1 n0 = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2r n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  have E1sub: "E1 \<subseteq> E" using SeqLeft.prems(2) c1c c2c by (auto split: prod.splits)
  have en2v: "en2 = Statement n1" using compile_entry_node[OF c2c] .
  have src2: "source_com c2r" using SeqLeft.prems(4) by simp
  have "control_at \<Pi> p c1 n0 SKIP v" using SeqLeft.hyps ri by simp
  from control_at_skip_to_exit[OF this refl c1c subset_trans[OF E1sub SeqLeft.prems(3)]]
  have sk: "star (cstep g) (v, s, stk) (ex1, s, stk)" .
  have step2: "star (cstep g) (ex1, s, stk) (en2, s, stk)"
  proof (cases "ex1 = en2")
    case True then show ?thesis by simp
  next
    case False
    then have "(ex1, EA_Nop, en2) \<in> E" using SeqLeft.prems(2) c1c c2c by (auto split: prod.splits)
    then have "(ex1, EA_Nop, en2) \<in> intra g" using SeqLeft.prems(3) by blast
    then show ?thesis using cstep_nop cstep_star_single by blast
  qed
  have "control_at \<Pi> p (Seq c1 c2r) n0 c2r en2"
    using control_at.SeqRight[OF c1c control_at_initial[OF src2, of \<Pi> p n1]] en2v by simp
  then have "control_at \<Pi> p (Seq c1 c2r) n0 c2 en2" using c2eq by simp
  moreover have "star (cstep g) (v, s, stk) (en2, s, stk)" using sk step2 by (meson star_trans)
  ultimately show ?case by blast
next
  case (WhileBody c n0 r_in v b)
  from WhileBody.prems(1) have ri: "r_in = SKIP" and c2eq: "c2 = While b c" by auto
  obtain n1 en1 ex1 E1 K1 where cc: "compile \<Pi> p c (Suc n0) = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  have E1sub: "E1 \<subseteq> E" and backnop: "(ex1, EA_Nop, Statement n0) \<in> E"
    using WhileBody.prems(2) cc by (auto split: prod.splits)
  have "control_at \<Pi> p c (Suc n0) SKIP v" using WhileBody.hyps ri by simp
  from control_at_skip_to_exit[OF this refl cc subset_trans[OF E1sub WhileBody.prems(3)]]
  have sk: "star (cstep g) (v, s, stk) (ex1, s, stk)" .
  have "(ex1, EA_Nop, Statement n0) \<in> intra g" using backnop WhileBody.prems(3) by blast
  then have "cstep g (ex1, s, stk) (Statement n0, s, stk)" by (rule cstep_nop)
  with sk have star_head: "star (cstep g) (v, s, stk) (Statement n0, s, stk)"
    by (meson star_trans cstep_star_single)
  have "control_at \<Pi> p (While b c) n0 (While b c) (Statement n0)" by (rule control_at.WhileHead)
  then have "control_at \<Pi> p (While b c) n0 c2 (Statement n0)" using c2eq by simp
  with star_head show ?case by blast
next
  case (SeqRight c1 n0 n1 en1 ex1 E1 K1 c2' r v)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2' n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  have sub: "E2 \<subseteq> E" using SeqRight.prems(2) SeqRight.hyps(1) c2c by (auto split: prod.splits)
  have src2: "source_com c2'" using SeqRight.prems(4) by simp
  from SeqRight.IH[OF SeqRight.prems(1) c2c subset_trans[OF sub SeqRight.prems(3)] src2]
  obtain v' where v': "control_at \<Pi> p c2' n1 c2 v'" "star (cstep g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (Seq c1 c2') n0 c2 v'" using control_at.SeqRight[OF SeqRight.hyps(1) v'(1)] .
  with v'(2) show ?case by blast
next
  case (IfLeft c1 n0 r v b c2')
  obtain n1 en1 ex1 E1 K1 where c1c: "compile \<Pi> p c1 (Suc n0) = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  have sub1: "E1 \<subseteq> E" using IfLeft.prems(2) c1c by (auto split: prod.splits)
  have src1: "source_com c1" using IfLeft.prems(4) by simp
  from IfLeft.IH[OF IfLeft.prems(1) c1c subset_trans[OF sub1 IfLeft.prems(3)] src1]
  obtain v' where v': "control_at \<Pi> p c1 (Suc n0) c2 v'" "star (cstep g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (If b c1 c2') n0 c2 v'" using control_at.IfLeft[OF v'(1)] .
  with v'(2) show ?case by blast
next
  case (IfRight c1 n0 n1 en1 ex1 E1 K1 c2' r v b)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2' n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  have sub2: "E2 \<subseteq> E" using IfRight.prems(2) IfRight.hyps(1) c2c by (auto split: prod.splits)
  have src2: "source_com c2'" using IfRight.prems(4) by simp
  from IfRight.IH[OF IfRight.prems(1) c2c subset_trans[OF sub2 IfRight.prems(3)] src2]
  obtain v' where v': "control_at \<Pi> p c2' n1 c2 v'" "star (cstep g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (If b c1 c2') n0 c2 v'" using control_at.IfRight[OF IfRight.hyps(1) v'(1)] .
  with v'(2) show ?case by blast
qed simp_all

subsection \<open>The intra-procedural source steps\<close>

text \<open>\<open>intra_step\<close> is the fragment of \<^const>\<open>pstep\<close> that stays inside one activation without
  initiating a return: assignment, sequencing (head execution and head completion), both
  conditionals, and the loop unfolding.  It excludes \<^const>\<open>Call\<close> (pushes a frame),
  \<^const>\<open>Return\<close> (produces \<^const>\<open>Unwind\<close>), and the runtime-only \<^const>\<open>Restore\<close> / \<^const>\<open>Unwind\<close>
  steps.  Every intra step preserves the frame stack and keeps the residual source-shaped.\<close>

inductive intra_step ::
  "proc_table \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool" for \<Pi> where
  IAssign: "intra_step \<Pi> (Assign x a, s, frs) (SKIP, s(x := aval a s), frs)"
| ISeq1:   "intra_step \<Pi> (Seq SKIP c2, s, frs) (c2, s, frs)"
| ISeq2:   "intra_step \<Pi> (c1, s, frs) (c1', s', frs) \<Longrightarrow>
            intra_step \<Pi> (Seq c1 c2, s, frs) (Seq c1' c2, s', frs)"
| IIfTrue: "bval b s \<Longrightarrow> intra_step \<Pi> (If b c1 c2, s, frs) (c1, s, frs)"
| IIfFalse:"\<not> bval b s \<Longrightarrow> intra_step \<Pi> (If b c1 c2, s, frs) (c2, s, frs)"
| IWhile:  "intra_step \<Pi> (While b c, s, frs) (If b (Seq c (While b c)) SKIP, s, frs)"

inductive_cases intra_SkipE:   "intra_step \<Pi> (SKIP, s, frs) y"
inductive_cases intra_AssignE: "intra_step \<Pi> (Assign x a, s, frs) y"
inductive_cases intra_SeqE:    "intra_step \<Pi> (Seq c1 c2, s, frs) y"
inductive_cases intra_IfE:     "intra_step \<Pi> (If b c1 c2, s, frs) y"
inductive_cases intra_WhileE:  "intra_step \<Pi> (While b c, s, frs) y"
inductive_cases intra_CallE:   "intra_step \<Pi> (Call dst q actuals, s, frs) y"
inductive_cases intra_ReturnE: "intra_step \<Pi> (Return e, s, frs) y"

text \<open>Every intra step is a source small step.\<close>
lemma intra_step_pstep: "intra_step \<Pi> x y \<Longrightarrow> pstep \<Pi> x y"
  by (induction rule: intra_step.induct) (auto intro: pstep.intros pstep.Seq2)

text \<open>Destructured inversions: each intra step of a compound has exactly the expected outcomes.\<close>

lemma intra_Assign_case:
  "intra_step \<Pi> (Assign x a, s, frs) (c', s', frs') \<Longrightarrow>
   c' = SKIP \<and> s' = s(x := aval a s) \<and> frs' = frs"
  by (auto elim: intra_AssignE)

lemma intra_Seq_cases:
  "intra_step \<Pi> (Seq c1 c2, s, frs) (c', s', frs') \<Longrightarrow>
   (c1 = SKIP \<and> c' = c2 \<and> s' = s \<and> frs' = frs) \<or>
   (\<exists>c1'. c' = Seq c1' c2 \<and> frs' = frs \<and> intra_step \<Pi> (c1, s, frs) (c1', s', frs))"
  by (auto elim: intra_SeqE)

lemma intra_If_cases:
  "intra_step \<Pi> (If b c1 c2, s, frs) (c', s', frs') \<Longrightarrow>
   (bval b s \<and> c' = c1 \<and> s' = s \<and> frs' = frs) \<or> (\<not> bval b s \<and> c' = c2 \<and> s' = s \<and> frs' = frs)"
  by (auto elim: intra_IfE)

lemma intra_While_case:
  "intra_step \<Pi> (While b c, s, frs) (c', s', frs') \<Longrightarrow>
   c' = If b (Seq c (While b c)) SKIP \<and> s' = s \<and> frs' = frs"
  by (auto elim: intra_WhileE)

subsection \<open>Intra-step simulation\<close>

text \<open>
  The assembled intra simulation: an \<^const>\<open>intra_step\<close> of a located source residual is matched by
  a (possibly empty) run of \<^const>\<open>cstep\<close> along compiled edges, preserving literal store equality
  and relocating the residual by  \<^const>\<open>control_at\<close>.  The frame stack is untouched.  Inducting on
  \<^const>\<open>control_at\<close> supplies the sequencing recursion (the \<open>ISeq2\<close> case reuses the derivation
  hypothesis for the head) and routes the base commands through the emit and relocation lemmas.
\<close>
theorem intra_step_simulation:
  "control_at \<Pi> p c0 n c v \<Longrightarrow>
   intra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   compile \<Pi> p c0 n = (n', en, ex, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> source_com c0 \<Longrightarrow>
   frs' = frs \<and> (\<exists>v'. control_at \<Pi> p c0 n c' v' \<and> star (cstep g) (v, s, stk) (v', s', stk))"
proof (induction arbitrary: c' s' frs' n' en ex E K rule: control_at.induct)
  case (Skip n0) then show ?case by (blast elim: intra_SkipE)
next
  case (Assign x a n0)
  from Assign.prems(1) have out: "c' = SKIP" "s' = s(x := aval a s)" "frs' = frs"
    by (auto elim: intra_AssignE)
  have ca: "control_at \<Pi> p (Assign x a) n0 (Assign x a) (Statement n0)" by (rule control_at.Assign)
  from control_at_assign_edge[OF ca refl Assign.prems(2)] obtain k where
    k: "Statement n0 = Statement k" "(Statement k, EA_Assign x a, Statement (Suc k)) \<in> E"
       "control_at \<Pi> p (Assign x a) n0 SKIP (Statement (Suc k))" by blast
  have "(Statement k, EA_Assign x a, Statement (Suc k)) \<in> intra g"
    using k(2) Assign.prems(3) by blast
  from cstep_assign[OF this]
  have "cstep g (Statement k, s, stk) (Statement (Suc k), s(x := aval a s), stk)" by simp
  then have "star (cstep g) (Statement n0, s, stk) (Statement (Suc k), s', stk)"
    using k(1) out(2) by (simp add: cstep_star_single)
  then show ?case using out(1,3) k(3) by auto
next
  case (AssignDone x a n0) then show ?case by (blast elim: intra_SkipE)
next
  case (SeqLeft c1 n0 r v c2)
  from intra_Seq_cases[OF SeqLeft.prems(1)] consider
      (s1) "r = SKIP" "c' = c2" "s' = s" "frs' = frs"
    | (s2) r' where "c' = Seq r' c2" "frs' = frs" "intra_step \<Pi> (r, s, frs) (r', s', frs)"
    by blast
  then show ?case
  proof cases
    case s1
    have loc: "control_at \<Pi> p (Seq c1 c2) n0 (Seq SKIP c2) v"
      using control_at.SeqLeft[OF SeqLeft.hyps] s1(1) by simp
    from control_at_seq_skip_reloc[OF loc refl SeqLeft.prems(2,3,4)]
    obtain v' where "control_at \<Pi> p (Seq c1 c2) n0 c2 v'"
      "star (cstep g) (v, s, stk) (v', s, stk)" by blast
    then show ?thesis using s1 by auto
  next
    case s2
    obtain n1 en1 ex1 E1 K1 where c1c: "compile \<Pi> p c1 n0 = (n1, en1, ex1, E1, K1)"
      by (metis prod_cases5)
    obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
      by (metis prod_cases5)
    have sub: "E1 \<subseteq> E" using SeqLeft.prems(2) c1c c2c by (auto split: prod.splits)
    have src1: "source_com c1" using SeqLeft.prems(4) by simp
    from SeqLeft.IH[OF s2(3) c1c subset_trans[OF sub SeqLeft.prems(3)] src1]
    obtain v' where v': "control_at \<Pi> p c1 n0 r' v'"
      "star (cstep g) (v, s, stk) (v', s', stk)" by auto
    have "control_at \<Pi> p (Seq c1 c2) n0 (Seq r' c2) v'"
      using control_at.SeqLeft[OF v'(1)] .
    then show ?thesis using s2 v'(2) by auto
  qed
next
  case (SeqRight c1 n0 n1 en1 ex1 E1 K1 c2 r v)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  have sub: "E2 \<subseteq> E" using SeqRight.prems(2) SeqRight.hyps(1) c2c by (auto split: prod.splits)
  have src2: "source_com c2" using SeqRight.prems(4) by simp
  from SeqRight.IH[OF SeqRight.prems(1) c2c subset_trans[OF sub SeqRight.prems(3)] src2]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c2 n1 c' v' \<and> star (cstep g) (v, s, stk) (v', s', stk)" by auto
  then obtain v' where v': "control_at \<Pi> p c2 n1 c' v'"
    "star (cstep g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (Seq c1 c2) n0 c' v'" using control_at.SeqRight[OF SeqRight.hyps(1) v'(1)] .
  with fr v'(2) show ?case by blast
next
  case (IfHead b c1 c2 n0)
  have ca: "control_at \<Pi> p (If b c1 c2) n0 (If b c1 c2) (Statement n0)" by (rule control_at.IfHead)
  from control_at_if_edges[OF ca refl IfHead.prems(4) IfHead.prems(2)] obtain k en1 en2 where
    k: "Statement n0 = Statement k"
       "(Statement k, EA_Assume b, en1) \<in> E" "(Statement k, EA_AssumeNot b, en2) \<in> E"
       "control_at \<Pi> p (If b c1 c2) n0 c1 en1" "control_at \<Pi> p (If b c1 c2) n0 c2 en2" by blast
  from intra_If_cases[OF IfHead.prems(1)] consider
      (t) "bval b s" "c' = c1" "s' = s" "frs' = frs"
    | (f) "\<not> bval b s" "c' = c2" "s' = s" "frs' = frs" by blast
  then show ?case
  proof cases
    case t
    have "(Statement k, EA_Assume b, en1) \<in> intra g" using k(2) IfHead.prems(3) by blast
    from cstep_assume[OF this] t(1)
    have "star (cstep g) (Statement n0, s, stk) (en1, s, stk)"
      using k(1) by (simp add: cstep_star_single)
    then show ?thesis using t k(4) by auto
  next
    case f
    have "(Statement k, EA_AssumeNot b, en2) \<in> intra g" using k(3) IfHead.prems(3) by blast
    from cstep_assume_not[OF this] f(1)
    have "star (cstep g) (Statement n0, s, stk) (en2, s, stk)"
      using k(1) by (simp add: cstep_star_single)
    then show ?thesis using f k(5) by auto
  qed
next
  case (IfLeft c1 n0 r v b c2)
  obtain n1 en1 ex1 E1 K1 where c1c: "compile \<Pi> p c1 (Suc n0) = (n1, en1, ex1, E1, K1)"
    by (metis prod_cases5)
  have sub1: "E1 \<subseteq> E" using IfLeft.prems(2) c1c by (auto split: prod.splits)
  have src1: "source_com c1" using IfLeft.prems(4) by simp
  from IfLeft.IH[OF IfLeft.prems(1) c1c subset_trans[OF sub1 IfLeft.prems(3)] src1]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c1 (Suc n0) c' v' \<and> star (cstep g) (v, s, stk) (v', s', stk)" by auto
  then obtain v' where v': "control_at \<Pi> p c1 (Suc n0) c' v'"
    "star (cstep g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (If b c1 c2) n0 c' v'" using control_at.IfLeft[OF v'(1)] .
  with fr v'(2) show ?case by blast
next
  case (IfRight c1 n0 n1 en1 ex1 E1 K1 c2 r v b)
  obtain n2 en2 ex2 E2 K2 where c2c: "compile \<Pi> p c2 n1 = (n2, en2, ex2, E2, K2)"
    by (metis prod_cases5)
  have sub2: "E2 \<subseteq> E" using IfRight.prems(2) IfRight.hyps(1) c2c by (auto split: prod.splits)
  have src2: "source_com c2" using IfRight.prems(4) by simp
  from IfRight.IH[OF IfRight.prems(1) c2c subset_trans[OF sub2 IfRight.prems(3)] src2]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c2 n1 c' v' \<and> star (cstep g) (v, s, stk) (v', s', stk)" by auto
  then obtain v' where v': "control_at \<Pi> p c2 n1 c' v'"
    "star (cstep g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (If b c1 c2) n0 c' v'" using control_at.IfRight[OF IfRight.hyps(1) v'(1)] .
  with fr v'(2) show ?case by blast
next
  case (IfDone b c1 c2 n0 mn men mex mE mK) then show ?case by (blast elim: intra_SkipE)
next
  case (WhileHead b cW n0)
  from WhileHead.prems(1) have out: "c' = If b (Seq cW (While b cW)) SKIP" "s' = s" "frs' = frs"
    by (auto elim: intra_WhileE)
  have "control_at \<Pi> p (While b cW) n0 (If b (Seq cW (While b cW)) SKIP) (Statement n0)"
    by (rule control_at.WhileUnfolded)
  then show ?case using out by (auto intro: star.refl)
next
  case (WhileUnfolded b cW n0)
  have ca: "control_at \<Pi> p (While b cW) n0 (If b (Seq cW (While b cW)) SKIP) (Statement n0)"
    by (rule control_at.WhileUnfolded)
  have srcif: "source_com (If b (Seq cW (While b cW)) SKIP)" using WhileUnfolded.prems(4) by simp
  from control_at_if_edges[OF ca refl srcif WhileUnfolded.prems(2)]
  obtain k en1 en2 where
    k: "Statement n0 = Statement k"
       "(Statement k, EA_Assume b, en1) \<in> E" "(Statement k, EA_AssumeNot b, en2) \<in> E"
       "control_at \<Pi> p (While b cW) n0 (Seq cW (While b cW)) en1"
       "control_at \<Pi> p (While b cW) n0 SKIP en2" by blast
  from intra_If_cases[OF WhileUnfolded.prems(1)] consider
      (t) "bval b s" "c' = Seq cW (While b cW)" "s' = s" "frs' = frs"
    | (f) "\<not> bval b s" "c' = SKIP" "s' = s" "frs' = frs" by blast
  then show ?case
  proof cases
    case t
    have "(Statement k, EA_Assume b, en1) \<in> intra g" using k(2) WhileUnfolded.prems(3) by blast
    from cstep_assume[OF this] t(1)
    have "star (cstep g) (Statement n0, s, stk) (en1, s, stk)"
      using k(1) by (simp add: cstep_star_single)
    then show ?thesis using t k(4) by auto
  next
    case f
    have "(Statement k, EA_AssumeNot b, en2) \<in> intra g" using k(3) WhileUnfolded.prems(3) by blast
    from cstep_assume_not[OF this] f(1)
    have "star (cstep g) (Statement n0, s, stk) (en2, s, stk)"
      using k(1) by (simp add: cstep_star_single)
    then show ?thesis using f k(5) by auto
  qed
next
  case (WhileBody cW n0 r v b)
  from intra_Seq_cases[OF WhileBody.prems(1)] consider
      (s1) "r = SKIP" "c' = While b cW" "s' = s" "frs' = frs"
    | (s2) r' where "c' = Seq r' (While b cW)" "frs' = frs" "intra_step \<Pi> (r, s, frs) (r', s', frs)"
    by blast
  then show ?case
  proof cases
    case s1
    have loc: "control_at \<Pi> p (While b cW) n0 (Seq SKIP (While b cW)) v"
      using control_at.WhileBody[OF WhileBody.hyps] s1(1) by simp
    from control_at_seq_skip_reloc[OF loc refl WhileBody.prems(2,3,4)]
    obtain v' where "control_at \<Pi> p (While b cW) n0 (While b cW) v'"
      "star (cstep g) (v, s, stk) (v', s, stk)" by blast
    then show ?thesis using s1 by auto
  next
    case s2
    obtain n1 en1 ex1 E1 K1 where cc: "compile \<Pi> p cW (Suc n0) = (n1, en1, ex1, E1, K1)"
      by (metis prod_cases5)
    have sub: "E1 \<subseteq> E" using WhileBody.prems(2) cc by (auto split: prod.splits)
    have srcW: "source_com cW" using WhileBody.prems(4) by simp
    from WhileBody.IH[OF s2(3) cc subset_trans[OF sub WhileBody.prems(3)] srcW]
    obtain v' where v': "control_at \<Pi> p cW (Suc n0) r' v'"
      "star (cstep g) (v, s, stk) (v', s', stk)" by auto
    have "control_at \<Pi> p (While b cW) n0 (Seq r' (While b cW)) v'"
      using control_at.WhileBody[OF v'(1)] .
    then show ?thesis using s2 v'(2) by auto
  qed
next
  case (WhileDone b cW n0 mn men mex mE mK) then show ?case by (blast elim: intra_SkipE)
next
  case (CallHead dst q actuals n0) then show ?case by (blast elim: intra_CallE)
next
  case (CallDone dst q actuals n0) then show ?case by (blast elim: intra_SkipE)
next
  case (ReturnHead e n0) then show ?case by (blast elim: intra_ReturnE)
qed

subsection \<open>Frame-stack inversions\<close>

text \<open>The source and CFG activation stacks are one-for-one on caller store and destination.
  These head/tail inversions expose the top frame in both directions; the CFG frame additionally
  carries a continuation node \<open>cont\<close>, unconstrained by \<^const>\<open>frames_match\<close> alone (the
  continuation-control correspondence is a separate invariant clause, established at the call and
  consumed at the return).\<close>

lemma frames_match_NilD: "frames_match [] stk \<Longrightarrow> stk = []"
  by (cases stk) (auto simp: frames_match_def)

lemma frames_match_cfg_NilD: "frames_match frs [] \<Longrightarrow> frs = []"
  by (cases frs rule: act_frames.cases) (auto simp: frames_match_def)

text \<open>Source-side head inversion: a source frame on top forces a CFG frame with equal caller store
  and destination, some continuation node, and matching tails.\<close>
lemma frames_match_src_ConsD:
  assumes "frames_match (Frame s dst # frs) stk"
  shows "\<exists>cont stk'. stk = (cont, dst, s) # stk' \<and> frames_match frs stk'"
  using assms
  by (cases stk) (auto simp: frames_match_def cframe_act_def split: prod.splits)

text \<open>CFG-side head inversion: a CFG frame on top forces a source \<^const>\<open>Frame\<close> with equal caller
  store and destination and matching tails.\<close>
lemma frames_match_cfg_ConsD:
  assumes "frames_match frs ((cont, dst, s) # stk')"
  shows "\<exists>frs'. frs = Frame s dst # frs' \<and> frames_match frs' stk'"
  using assms
  by (cases frs rule: act_frames.cases) (auto simp: frames_match_def cframe_act_def)

text \<open>Constructor form of the frame-match step, tying the two head inversions to the call push
  (mirrors \<open>frames_match_call\<close> but exposed as a bidirectional equality).\<close>
lemma frames_match_Cons_iff:
  "frames_match (Frame s dst # frs) ((cont, dst, s) # stk) = frames_match frs stk"
  by (simp add: frames_match_def cframe_act_def)

subsection \<open>Continuation-node correspondence\<close>

text \<open>The continuation node recorded on a CFG call frame is exactly where \<^const>\<open>control_at\<close>
  locates the caller's post-call residual (the call replaced by \<^const>\<open>SKIP\<close>).  This is read off
  \<open>control_at_call_edge\<close>: the same \<open>Statement (Suc k)\<close> both carries the emitted call edge's
  continuation and locates the caller residual \<^const>\<open>SKIP\<close>.\<close>
lemma call_continuation_control:
  assumes "control_at \<Pi> p c0 n (Call dst q actuals) v"
      and "compile \<Pi> p c0 n = (n', en, ex, E, K)"
  shows "\<exists>k. v = Statement k
          \<and> (Statement k, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
             FunctionEntry q, Statement (Suc k)) \<in> K
          \<and> control_at \<Pi> p c0 n SKIP (Statement (Suc k))"
  using control_at_call_edge[OF assms(1) refl assms(2)] .

subsection \<open>Call transition\<close>

text \<open>
  A source \<^const>\<open>Call\<close> step is simulated by exactly one interprocedural \<^const>\<open>cstep\<close> along the
  compiled call edge.  The four conclusions are the required call correspondences:
    \<^enum> the source \<^const>\<open>pstep\<close> evaluates the actuals in the caller store \<open>s\<close>, resets callee locals
      with \<^const>\<open>enter_state\<close>, and pushes \<^term>\<open>Frame s dst\<close>;
    \<^enum> the CFG \<^const>\<open>cstep\<close> traverses the call edge, applies \<^const>\<open>call_enter\<close>, reaches
      \<^term>\<open>FunctionEntry q\<close>, and pushes \<^term>\<open>(cont, dst, s)\<close>;
    \<^enum> the CFG callee-entry store equals the source callee-entry store literally
      (\<open>call_enter_eq_source_call_store\<close>);
    \<^enum> the pushed frames correspond and the tails stay matched (\<open>frames_match_Cons_iff\<close>).
\<close>
lemma call_transition:
  assumes decl: "\<Pi> q = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct: "distinct (formals decl)"
      and dstok: "\<forall>x. dst = Some x \<longrightarrow> result decl \<noteq> None"
      and edge: "(u, CallEdge dst (formals decl) actuals, FunctionEntry q, cont) \<in> calls g"
      and fm: "frames_match frs stk"
  shows "pstep \<Pi> (Call dst q actuals, s, frs)
           (Seq (with_result (body decl) (result decl)) Restore,
            bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state s),
            Frame s dst # frs)"       (is ?src)
    and "cstep g (u, s, stk)
           (FunctionEntry q,
            call_enter (CallEdge dst (formals decl) actuals) s, (cont, dst, s) # stk)"  (is ?cfg)
    and "call_enter (CallEdge dst (formals decl) actuals) s
           = bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state s)"  (is ?store)
    and "frames_match (Frame s dst # frs) ((cont, dst, s) # stk)"                        (is ?frames)
proof -
  show ?src
    using decl arity distinct dstok
    by (intro pstep.Call[where vals = "map (\<lambda>e. aval e s) actuals"]) auto
  show ?cfg by (rule cstep.Call[OF edge])
  show ?store by (rule call_enter_eq_source_call_store)
  show ?frames using fm by (simp add: frames_match_Cons_iff)
qed

text \<open>Located form: when the caller residual is the call at node \<open>v\<close>, the call edge of the transition
  is the compiler-emitted one and the continuation node locates the caller's post-call residual.\<close>
lemma call_transition_located:
  assumes loc: "control_at \<Pi> p c0 n (Call dst q actuals) v"
      and comp: "compile \<Pi> p c0 n = (n', en, ex, E, K)"
      and Ksub: "K \<subseteq> calls g"
      and decl: "\<Pi> q = Some decl"
  obtains k where "v = Statement k"
    and "cstep g (Statement k, s, stk)
           (FunctionEntry q, call_enter (CallEdge dst (formals decl) actuals) s,
            (Statement (Suc k), dst, s) # stk)"
    and "control_at \<Pi> p c0 n SKIP (Statement (Suc k))"
proof -
  from control_at_call_edge[OF loc refl comp] obtain k where
    k: "v = Statement k"
       "(Statement k, CallEdge dst (case \<Pi> q of Some d \<Rightarrow> formals d | None \<Rightarrow> []) actuals,
         FunctionEntry q, Statement (Suc k)) \<in> K"
       "control_at \<Pi> p c0 n SKIP (Statement (Suc k))" by blast
  have kd: "(Statement k, CallEdge dst (formals decl) actuals, FunctionEntry q, Statement (Suc k))
              \<in> K"
    using k(2) by (simp add: decl)
  have edge: "(Statement k, CallEdge dst (formals decl) actuals, FunctionEntry q, Statement (Suc k))
                \<in> calls g"
    using kd Ksub by blast
  show ?thesis
    by (rule that[OF k(1) cstep.Call[OF edge] k(3)])
qed

subsection \<open>Return initiation\<close>

text \<open>The store published by a return: the callee's \<^const>\<open>ret_var\<close> is set to the evaluated
  return value (\<^term>\<open>Some e\<close>) or left untouched (\<^term>\<open>None\<close>).  It is the common store reached
  by both the source \<^const>\<open>Return\<close> step and the compiled \<^term>\<open>EA_Ret\<close> edge.\<close>
definition ret_store :: "aexp option \<Rightarrow> store \<Rightarrow> store" where
  "ret_store e s = s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))"

lemma ret_store_None [simp]: "ret_store None s = s"
  by (simp add: ret_store_def)

lemma ret_store_Some [simp]: "ret_store (Some e) s = s(ret_var := aval e s)"
  by (simp add: ret_store_def)

lemma edge_step_EA_Ret_ret_store: "edge_step (EA_Ret e p) s = Some (ret_store e s)"
  by (simp add: ret_store_def)

text \<open>
  Return initiation: a source \<^const>\<open>Return\<close> and the emitted \<^term>\<open>EA_Ret e p\<close> edge both evaluate
  \<open>e\<close> in the same store \<open>s\<close> and enter the returning phase, the source at \<^const>\<open>Unwind\<close> and the CFG
  at \<^term>\<open>FunctionResult p\<close>, with the identical published store \<^const>\<open>ret_store\<close> and the frame
  stack untouched.  Neither semantics pops a frame here; the returning-mode invariant is
  established at \<^term>\<open>FunctionResult p\<close>.
\<close>
lemma return_initiation:
  assumes loc: "control_at \<Pi> p c0 n (Return e) v"
      and comp: "compile \<Pi> p c0 n = (n', en, ex, E, K)"
      and sub: "E \<subseteq> intra g"
  obtains k where "v = Statement k"
    and "pstep \<Pi> (Return e, s, frs) (Unwind, ret_store e s, frs)"
    and "cstep g (Statement k, s, stk) (FunctionResult p, ret_store e s, stk)"
proof -
  from control_at_return_edge[OF loc refl comp] obtain k where
    k: "v = Statement k" "(Statement k, EA_Ret e p, FunctionResult p) \<in> E" by blast
  have edge: "(Statement k, EA_Ret e p, FunctionResult p) \<in> intra g" using k(2) sub by blast
  have src: "pstep \<Pi> (Return e, s, frs) (Unwind, ret_store e s, frs)"
    by (cases e) (auto simp: ret_store_def)
  have cfg: "cstep g (Statement k, s, stk) (FunctionResult p, ret_store e s, stk)"
    using cstep.Intra[OF edge edge_step_EA_Ret_ret_store] .
  show ?thesis by (rule that[OF k(1) src cfg])
qed

subsection \<open>Return completion and normal fall-through\<close>

text \<open>
  Return completion: from the returning-mode invariant (source at \<^const>\<open>Restore\<close> with the
  callee store, CFG at \<^term>\<open>FunctionResult p\<close>) and a matching top frame, both semantics pop
  exactly the immediate caller frame and resume at the same store \<^const>\<open>combine_collect\<close> --- the
  callee globals kept, caller locals restored, the return value written to the destination.  The
  resumed source residual is \<^const>\<open>SKIP\<close> and the resumed CFG node is the frame's continuation
  \<open>cont\<close>; the tails stay matched.  This is the normal fall-through form (the callee body has
  reduced to \<^const>\<open>SKIP\<close>, so the runtime step is a bare \<^const>\<open>Restore\<close>).
\<close>
lemma return_completion_restore:
  assumes fm: "frames_match (Frame caller dst # frs) ((cont, dst, caller) # stk)"
  shows "pstep \<Pi> (Restore, callee, Frame caller dst # frs)
           (SKIP, combine_collect dst caller callee, frs)"
    and "cstep g (FunctionResult p, callee, (cont, dst, caller) # stk)
           (cont, combine_collect dst caller callee, stk)"
    and "frames_match frs stk"
proof -
  show "pstep \<Pi> (Restore, callee, Frame caller dst # frs)
          (SKIP, combine_collect dst caller callee, frs)"
    using pstep.RestoreStep by (simp add: combine_collect_def)
  show "cstep g (FunctionResult p, callee, (cont, dst, caller) # stk)
          (cont, combine_collect dst caller callee, stk)"
    by (rule cstep.Return)
  show "frames_match frs stk" using fm by (simp add: frames_match_Cons_iff)
qed

text \<open>
  Explicit-return completion: the same pop, reached through a \<^term>\<open>Seq Unwind Restore\<close> step ---
  a source \<^const>\<open>Return\<close> has already produced \<^const>\<open>Unwind\<close> and the dead code after it is
  discarded.  The resumed store and the matched CFG return are identical to the fall-through case,
  so a single \<^const>\<open>cstep\<close> return serves both.
\<close>
lemma return_completion_unwind:
  assumes fm: "frames_match (Frame caller dst # frs) ((cont, dst, caller) # stk)"
  shows "pstep \<Pi> (Seq Unwind Restore, callee, Frame caller dst # frs)
           (SKIP, combine_collect dst caller callee, frs)"
    and "cstep g (FunctionResult p, callee, (cont, dst, caller) # stk)
           (cont, combine_collect dst caller callee, stk)"
    and "frames_match frs stk"
proof -
  show "pstep \<Pi> (Seq Unwind Restore, callee, Frame caller dst # frs)
          (SKIP, combine_collect dst caller callee, frs)"
    using pstep.UnwindAct by (simp add: combine_collect_def)
  show "cstep g (FunctionResult p, callee, (cont, dst, caller) # stk)
          (cont, combine_collect dst caller callee, stk)"
    by (rule cstep.Return)
  show "frames_match frs stk" using fm by (simp add: frames_match_Cons_iff)
qed

text \<open>The resumed CFG node \<open>cont\<close> is an ordinary caller location: it is where \<^const>\<open>control_at\<close>
  locates the caller's post-call \<^const>\<open>SKIP\<close> residual (from the originating call).  Combined with
  the completion lemmas, the return resumes the caller in ordinary mode with the combined store.\<close>
lemma return_resumes_ordinary:
  assumes call: "control_at \<Pi> p_caller c0 n (Call dst q actuals) (Statement kc)"
      and comp: "compile \<Pi> p_caller c0 n = (n', en, ex, E, K)"
  shows "control_at \<Pi> p_caller c0 n SKIP (Statement (Suc kc))"
proof -
  from control_at_call_edge[OF call refl comp] show ?thesis by blast
qed

subsection \<open>Top-level completion and the empty-stack guard\<close>

text \<open>
  A completed whole-program run is \<^const>\<open>SKIP\<close> with an empty source frame stack; it corresponds
  to the compiled main-exit node with an empty CFG frame stack.  The frame correspondence is the
  empty match.  Completion is a boundary condition, kept out of the frame-pop lemmas.
\<close>
lemma toplevel_completion_frames:
  "frames_match [] []"
  by (rule frames_match_Nil)

text \<open>The returning-mode markers cannot complete on an empty frame stack: a \<^const>\<open>Restore\<close> or a
  bare \<^const>\<open>Unwind\<close> with no activation to pop is stuck, so a return never escapes its nearest
  activation into successful whole-program completion.  This is the guard that a \<^const>\<open>Return\<close> or
  unwind configuration with an empty stack is not a good exit.\<close>

lemma pstep_Restore_empty_stuck: "\<not> pstep \<Pi> (Restore, s, []) x"
  by (auto elim: RestoreSE)

lemma pstep_Unwind_stuck: "\<not> pstep \<Pi> (Unwind, s, frs) x"
  by (auto elim: UnwindSE)

text \<open>Consequently a bare \<^const>\<open>Unwind\<close> is never a completing configuration, and a source
  \<^const>\<open>Return\<close> on the empty (whole-program) stack cannot complete: it steps to \<^const>\<open>Unwind\<close>,
  which is stuck.  A returning configuration with an empty stack is excluded from successful
  completion.\<close>
lemma Unwind_not_pcompletes: "\<not> pcompletes \<Pi> Unwind s t"
  unfolding pcompletes_def
proof
  assume "star (pstep \<Pi>) (Unwind, s, []) (SKIP, t, [])"
  then show False
    by (cases rule: star.cases) (auto simp: pstep_Unwind_stuck)
qed

lemma Return_empty_not_pcompletes: "\<not> pcompletes \<Pi> (Return e) s t"
  unfolding pcompletes_def
proof
  assume "star (pstep \<Pi>) (Return e, s, []) (SKIP, t, [])"
  then obtain y where step: "pstep \<Pi> (Return e, s, []) y"
      and rest: "star (pstep \<Pi>) y (SKIP, t, [])"
    by (cases rule: star.cases) auto
  from step have "y = (Unwind, ret_store e s, [])"
    by (cases e) (auto elim: ReturnSE simp: ret_store_def)
  with rest have "star (pstep \<Pi>) (Unwind, ret_store e s, []) (SKIP, t, [])" by simp
  then show False
    by (cases rule: star.cases) (auto simp: pstep_Unwind_stuck)
qed

end

