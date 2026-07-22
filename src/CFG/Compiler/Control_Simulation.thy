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

end

