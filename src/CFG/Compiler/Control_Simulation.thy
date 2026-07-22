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

end

