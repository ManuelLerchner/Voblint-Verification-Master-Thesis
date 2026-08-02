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
  re-locates the residual \<^const>\<open>SKIP\<close> at that edge's target --- the continuation of the
  fragment the assignment belongs to, which is where the next command starts.\<close>
lemma control_at_assign_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = Assign x a \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j w. v = Statement j \<and> (Statement j, EA_Assign x a, w) \<in> E
       \<and> control_at \<Pi> p c0 k n SKIP w"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (Assign x' a' k n0)
  then show ?case by (auto intro: control_at.AssignDone)
next
  case (SeqRight c1 c2 k n0 r v)
  from SeqRight.prems(2) obtain n2 E2 K2 n1 E1 K1 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] obtain j w where
    jw: "v = Statement j" "(Statement j, EA_Assign x a, w) \<in> E2"
        "control_at \<Pi> p c2 k (n0 + csize c1) SKIP w" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 SKIP w"
    using control_at.SeqRight[OF SeqRight.hyps(1) jw(3)] .

  then show ?case using jw E by blast
next
  case (IfLeft c1 k n0 r v b c2)
  from IfLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and E: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  from IfLeft.IH[OF IfLeft.prems(1) c1c] obtain j w where
    jw: "v = Statement j" "(Statement j, EA_Assign x a, w) \<in> E1"
        "control_at \<Pi> p c1 k (Suc n0) SKIP w" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 SKIP w" using control_at.IfLeft[OF jw(3)] .
  then show ?case using jw E by blast
next
  case (IfRight c2 k n0 c1 r v b)
  from IfRight.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and E: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  from IfRight.IH[OF IfRight.prems(1) c2c] obtain j w where
    jw: "v = Statement j" "(Statement j, EA_Assign x a, w) \<in> E2"
        "control_at \<Pi> p c2 k (Suc n0 + csize c1) SKIP w" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 SKIP w" using control_at.IfRight[OF jw(3)] .
  then show ?case using jw E by blast
qed simp_all

text \<open>A located call sits on the compiled \<^term>\<open>CallEdge\<close> into the callee entry, and its source
  step re-locates \<^const>\<open>SKIP\<close> at the call's continuation node.\<close>
lemma control_at_call_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = Call dst q actuals \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j w. v = Statement j
       \<and> (Statement j, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
          FunctionEntry q, w) \<in> K
       \<and> control_at \<Pi> p c0 k n SKIP w"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (CallHead dst' q' actuals' k n0)
  then show ?case by (auto intro: control_at.CallDone)
next
  case (SeqRight c1 c2 k n0 r v)
  from SeqRight.prems(2) obtain n2 E2 K2 n1 E1 K1 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] obtain j w where
    jw: "v = Statement j"
        "(Statement j, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
          FunctionEntry q, w) \<in> K2"
        "control_at \<Pi> p c2 k (n0 + csize c1) SKIP w" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 SKIP w"
    using control_at.SeqRight[OF SeqRight.hyps(1) jw(3)] .

  then show ?case using jw K by blast
next
  case (IfLeft c1 k n0 r v b c2)
  from IfLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and K: "K = K1 \<union> K2"
    by (rule compile_IfE)
  from IfLeft.IH[OF IfLeft.prems(1) c1c] obtain j w where
    jw: "v = Statement j"
        "(Statement j, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
          FunctionEntry q, w) \<in> K1"
        "control_at \<Pi> p c1 k (Suc n0) SKIP w" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 SKIP w" using control_at.IfLeft[OF jw(3)] .
  then show ?case using jw K by blast
next
  case (IfRight c2 k n0 c1 r v b)
  from IfRight.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and K: "K = K1 \<union> K2"
    by (rule compile_IfE)
  from IfRight.IH[OF IfRight.prems(1) c2c] obtain j w where
    jw: "v = Statement j"
        "(Statement j, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
          FunctionEntry q, w) \<in> K2"
        "control_at \<Pi> p c2 k (Suc n0 + csize c1) SKIP w" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 SKIP w" using control_at.IfRight[OF jw(3)] .
  then show ?case using jw K by blast
qed simp_all


text \<open>A located \<^const>\<open>Return\<close> sits on the compiled \<^term>\<open>EA_Ret\<close> edge into
  \<^term>\<open>FunctionResult p\<close> --- the enclosing procedure's result node.  The continuation is not
  mentioned, which is the whole point of the return clause.\<close>
lemma control_at_return_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = Return e \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j. v = Statement j \<and> (Statement j, EA_Ret e p, FunctionResult p) \<in> E"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (ReturnHead e' k n0)
  then show ?case by auto
next
  case (SeqRight c1 c2 k n0 r v)

  from SeqRight.prems(2) obtain n2 E2 K2 n1 E1 K1 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] show ?case using E by blast
next
  case (IfLeft c1 k n0 r v b c2)
  from IfLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and E: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  from IfLeft.IH[OF IfLeft.prems(1) c1c] show ?case using E by blast
next
  case (IfRight c2 k n0 c1 r v b)
  from IfRight.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and E: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  from IfRight.IH[OF IfRight.prems(1) c2c] show ?case using E by blast
qed simp_all

text \<open>A located conditional sits on both compiled assume edges; each branch re-locates its
  operand at the branch entry (the source \<open>IfTrue\<close> / \<open>IfFalse\<close> targets).  The residual also
  arises from a loop unfolding (\<^const>\<open>While\<close> steps to \<open>If b (Seq c (While b c)) SKIP\<close>), so the
  \<open>WhileUnfolded\<close> case is real: the true branch re-locates the loop body followed by the
  loop, the false branch re-locates \<^const>\<open>SKIP\<close> at the loop's continuation.\<close>
lemma control_at_if_edges:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = If b c1 c2 \<Longrightarrow> source_com r \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j en1 en2. v = Statement j
       \<and> (Statement j, EA_Assume b, en1) \<in> E \<and> (Statement j, EA_AssumeNot b, en2) \<in> E
       \<and> control_at \<Pi> p c0 k n c1 en1 \<and> control_at \<Pi> p c0 k n c2 en2"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (IfHead b' c1' c2' k n0)
  from IfHead.prems(1) have r: "b' = b" "c1' = c1" "c2' = c2" by auto
  from IfHead.prems(3) obtain m1 E1 K1 m2 E2 K2 where
    E: "E = {(Statement n0, EA_Assume b', Statement (Suc n0)),
             (Statement n0, EA_AssumeNot b', Statement (Suc n0 + csize c1'))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  from IfHead.prems(2) r have src: "source_com c1'" "source_com c2'" by auto
  have ca1: "control_at \<Pi> p (If b' c1' c2') k n0 c1' (Statement (Suc n0))"
    by (rule control_at.IfLeft[OF control_at_initial[OF src(1)]])
  have ca2: "control_at \<Pi> p (If b' c1' c2') k n0 c2' (Statement (Suc n0 + csize c1'))"
    by (rule control_at.IfRight[OF control_at_initial[OF src(2)]])
  from E ca1 ca2 r show ?case by auto
next
  case (SeqRight c1' c2' k n0 r v)
  from SeqRight.prems(3) obtain n2 E2 K2 n1 E1 K1 where
    c2c: "compile \<Pi> p c2' k (n0 + csize c1') = (n2, Statement (n0 + csize c1'), E2, K2)"
    and E: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  from SeqRight.IH[OF SeqRight.prems(1) SeqRight.prems(2) c2c] obtain j e1 e2 where
    jw: "v = Statement j" "(Statement j, EA_Assume b, e1) \<in> E2"
        "(Statement j, EA_AssumeNot b, e2) \<in> E2"
        "control_at \<Pi> p c2' k (n0 + csize c1') c1 e1"
        "control_at \<Pi> p c2' k (n0 + csize c1') c2 e2" by blast
  have "control_at \<Pi> p (Seq c1' c2') k n0 c1 e1" "control_at \<Pi> p (Seq c1' c2') k n0 c2 e2"
    using control_at.SeqRight[OF SeqRight.hyps(1) jw(4)]
          control_at.SeqRight[OF SeqRight.hyps(1) jw(5)] .

  then show ?case using jw E by blast
next
  case (IfLeft c1' k n0 r v b' c2')
  from IfLeft.prems(3) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1' k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and E: "E = {(Statement n0, EA_Assume b', Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b', Statement (Suc n0 + csize c1'))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  from IfLeft.IH[OF IfLeft.prems(1) IfLeft.prems(2) c1c] obtain j e1 e2 where
    jw: "v = Statement j" "(Statement j, EA_Assume b, e1) \<in> E1"
        "(Statement j, EA_AssumeNot b, e2) \<in> E1"
        "control_at \<Pi> p c1' k (Suc n0) c1 e1" "control_at \<Pi> p c1' k (Suc n0) c2 e2" by blast
  have "control_at \<Pi> p (If b' c1' c2') k n0 c1 e1" "control_at \<Pi> p (If b' c1' c2') k n0 c2 e2"
    using control_at.IfLeft[OF jw(4)] control_at.IfLeft[OF jw(5)] .
  then show ?case using jw E by blast
next
  case (IfRight c2' k n0 c1' r v b')
  from IfRight.prems(3) obtain n1 E1 K1 n2 E2 K2 where
    c2c: "compile \<Pi> p c2' k (Suc n0 + csize c1')
            = (n2, Statement (Suc n0 + csize c1'), E2, K2)"
    and E: "E = {(Statement n0, EA_Assume b', Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b', Statement (Suc n0 + csize c1'))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  from IfRight.IH[OF IfRight.prems(1) IfRight.prems(2) c2c] obtain j e1 e2 where
    jw: "v = Statement j" "(Statement j, EA_Assume b, e1) \<in> E2"
        "(Statement j, EA_AssumeNot b, e2) \<in> E2"
        "control_at \<Pi> p c2' k (Suc n0 + csize c1') c1 e1"
        "control_at \<Pi> p c2' k (Suc n0 + csize c1') c2 e2" by blast
  have "control_at \<Pi> p (If b' c1' c2') k n0 c1 e1" "control_at \<Pi> p (If b' c1' c2') k n0 c2 e2"
    using control_at.IfRight[OF jw(4)] control_at.IfRight[OF jw(5)] .
  then show ?case using jw E by blast
next
  case (WhileUnfolded b'' c'' k n0)
  from WhileUnfolded.prems(1)
  have r: "b'' = b" "Seq c'' (While b'' c'') = c1" "SKIP = c2" by auto
  from WhileUnfolded.prems(3) obtain n1 E1 K1 where
    E: "E = {(Statement n0, EA_Assume b'', Statement (Suc n0)),
             (Statement n0, EA_AssumeNot b'', k)} \<union> E1"
    by (rule compile_WhileE)
  from WhileUnfolded.prems(2) have src: "source_com c''" by auto
  have ca1: "control_at \<Pi> p (While b'' c'') k n0 (Seq c'' (While b'' c'')) (Statement (Suc n0))"
    by (rule control_at.WhileBody[OF control_at_initial[OF src]])
  have ca2: "control_at \<Pi> p (While b'' c'') k n0 SKIP k"
    by (rule control_at.WhileDone)
  from E ca1 ca2 r show ?case by auto
qed simp_all
subsection \<open>SKIP relocation to the continuation\<close>

text \<open>A located \<^const>\<open>SKIP\<close> --- a completed sub-command --- is at its fragment's continuation
  already, except for a source \<^const>\<open>SKIP\<close>, which still has its own node and one
  \<^term>\<open>EA_Nop\<close> edge.  This is the reusable relocation primitive under \<^const>\<open>Seq\<close>
  completion; the branch-join and back-edge hops of the previous layout are gone.\<close>
lemma control_at_skip_to_exit:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = SKIP \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow>
   star (cstep source_global g) (v, s, stk) (k, s, stk)"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (Skip k n0)
  have "(Statement n0, EA_Nop, k) \<in> intra g" using Skip.prems(2,3) by auto
  then show ?case by (meson cstep_nop cstep_star_single)
next
  case (AssignDone x a k n0)
  then show ?case by (auto intro: star.refl)
next
  case (CallDone dst q actuals k n0)
  then show ?case by (auto intro: star.refl)
next
  case (IfDone b c1 c2 k n0)
  then show ?case by (auto intro: star.refl)
next
  case (WhileDone b c k n0)
  then show ?case by (auto intro: star.refl)
next
  case (SeqRight c1 c2 k n0 r v)

  from SeqRight.prems(2) obtain n2 E2 K2 n1 E1 K1 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  have sub: "E2 \<subseteq> E" using E by blast
  show ?case
    using SeqRight.IH[OF SeqRight.prems(1) c2c subset_trans[OF sub SeqRight.prems(3)]] .
next
  case (IfLeft c1 k n0 r v b c2)
  from IfLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and E: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  have sub: "E1 \<subseteq> E" using E by blast
  show ?case
    using IfLeft.IH[OF IfLeft.prems(1) c1c subset_trans[OF sub IfLeft.prems(3)]] .
next
  case (IfRight c2 k n0 c1 r v b)
  from IfRight.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and E: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  have sub: "E2 \<subseteq> E" using E by blast
  show ?case
    using IfRight.IH[OF IfRight.prems(1) c2c subset_trans[OF sub IfRight.prems(3)]] .
qed simp_all

subsection \<open>Completed-head sequence relocation\<close>

text \<open>When a sequence's head has completed (\<^term>\<open>Seq SKIP c2\<close>), control relocates to the
  continuation \<^term>\<open>c2\<close> at its entry.  Under continuation passing the head's own last edge
  already targets that entry --- and, when the continuation is the enclosing \<^const>\<open>While\<close>,
  the loop head --- so relocation is exactly \<open>control_at_skip_to_exit\<close>.\<close>
lemma control_at_seq_skip_reloc:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = Seq SKIP c2 \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> source_com c0 \<Longrightarrow>
   \<exists>v'. control_at \<Pi> p c0 k n c2 v' \<and> star (cstep source_global g) (v, s, stk) (v', s, stk)"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (SeqLeft c1 n0 r_in v c2r k)
  from SeqLeft.prems(1) have ri: "r_in = SKIP" and c2eq: "c2r = c2" by auto
  from SeqLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
    and E: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  have sub: "E1 \<subseteq> E" using E by blast
  have src2: "source_com c2r" using SeqLeft.prems(4) by simp
  have skipc1: "control_at \<Pi> p c1 (Statement (n0 + csize c1)) n0 SKIP v"
    using SeqLeft.hyps ri by simp
  from control_at_skip_to_exit[OF skipc1 refl c1c subset_trans[OF sub SeqLeft.prems(3)]]
  have sk: "star (cstep source_global g) (v, s, stk) (Statement (n0 + csize c1), s, stk)" .
  have ft: "falls_through c1" by (rule control_at_SKIP_imp_falls_through[OF skipc1])
  have "control_at \<Pi> p (Seq c1 c2r) k n0 c2r (Statement (n0 + csize c1))"
    by (rule control_at.SeqRight[OF ft control_at_initial[OF src2]])

  then have "control_at \<Pi> p (Seq c1 c2r) k n0 c2 (Statement (n0 + csize c1))" using c2eq by simp
  with sk show ?case by blast
next
  case (WhileBody c n0 r_in v b k)
  from WhileBody.prems(1) have ri: "r_in = SKIP" and c2eq: "c2 = While b c" by auto
  from WhileBody.prems(2) obtain n1 E1 K1 where
    cc: "compile \<Pi> p c (Statement n0) (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and E: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b, k)} \<union> E1"
    by (rule compile_WhileE)
  have sub: "E1 \<subseteq> E" using E by blast
  have "control_at \<Pi> p c (Statement n0) (Suc n0) SKIP v" using WhileBody.hyps ri by simp
  from control_at_skip_to_exit[OF this refl cc subset_trans[OF sub WhileBody.prems(3)]]
  have sk: "star (cstep source_global g) (v, s, stk) (Statement n0, s, stk)" .
  have "control_at \<Pi> p (While b c) k n0 (While b c) (Statement n0)" by (rule control_at.WhileHead)
  then have "control_at \<Pi> p (While b c) k n0 c2 (Statement n0)" using c2eq by simp
  with sk show ?case by blast
next
  case (SeqRight c1 c2' k n0 r v)
  from SeqRight.prems(2) obtain n2 E2 K2 n1 E1 K1 where
    c2c: "compile \<Pi> p c2' k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and E: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  have sub: "E2 \<subseteq> E" using E by blast
  have src2: "source_com c2'" using SeqRight.prems(4) by simp
  from SeqRight.IH[OF SeqRight.prems(1) c2c subset_trans[OF sub SeqRight.prems(3)] src2]
  obtain v' where v': "control_at \<Pi> p c2' k (n0 + csize c1) c2 v'"
    "star (cstep source_global g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (Seq c1 c2') k n0 c2 v'"
    using control_at.SeqRight[OF SeqRight.hyps(1) v'(1)] .

  with v'(2) show ?case by blast
next
  case (IfLeft c1 k n0 r v b c2')
  from IfLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and E: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  have sub: "E1 \<subseteq> E" using E by blast
  have src1: "source_com c1" using IfLeft.prems(4) by simp
  from IfLeft.IH[OF IfLeft.prems(1) c1c subset_trans[OF sub IfLeft.prems(3)] src1]
  obtain v' where v': "control_at \<Pi> p c1 k (Suc n0) c2 v'"
    "star (cstep source_global g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (If b c1 c2') k n0 c2 v'" using control_at.IfLeft[OF v'(1)] .
  with v'(2) show ?case by blast
next
  case (IfRight c2' k n0 c1 r v b)
  from IfRight.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c2c: "compile \<Pi> p c2' k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and E: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                 (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  have sub: "E2 \<subseteq> E" using E by blast
  have src2: "source_com c2'" using IfRight.prems(4) by simp
  from IfRight.IH[OF IfRight.prems(1) c2c subset_trans[OF sub IfRight.prems(3)] src2]
  obtain v' where v': "control_at \<Pi> p c2' k (Suc n0 + csize c1) c2 v'"
    "star (cstep source_global g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (If b c1 c2') k n0 c2 v'" using control_at.IfRight[OF v'(1)] .
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


text \<open>Destructured inversions: each intra step of a compound has exactly the expected outcomes.\<close>


lemma intra_Seq_cases:
  "intra_step \<Pi> (Seq c1 c2, s, frs) (c', s', frs') \<Longrightarrow>
   (c1 = SKIP \<and> c' = c2 \<and> s' = s \<and> frs' = frs) \<or>
   (\<exists>c1'. c' = Seq c1' c2 \<and> frs' = frs \<and> intra_step \<Pi> (c1, s, frs) (c1', s', frs))"
  by (auto elim: intra_SeqE)

lemma intra_If_cases:
  "intra_step \<Pi> (If b c1 c2, s, frs) (c', s', frs') \<Longrightarrow>
   (bval b s \<and> c' = c1 \<and> s' = s \<and> frs' = frs) \<or> (\<not> bval b s \<and> c' = c2 \<and> s' = s \<and> frs' = frs)"
  by (auto elim: intra_IfE)


subsection \<open>Intra-step simulation\<close>

text \<open>
  The assembled intra simulation: an \<^const>\<open>intra_step\<close> of a located source residual is matched by
  a (possibly empty) run of \<^const>\<open>cstep\<close> along compiled edges, preserving literal store equality
  and relocating the residual by  \<^const>\<open>control_at\<close>.  The frame stack is untouched.  Inducting on
  \<^const>\<open>control_at\<close> supplies the sequencing recursion (the \<open>ISeq2\<close> case reuses the derivation
  hypothesis for the head) and routes the base commands through the emit and relocation lemmas.
\<close>
theorem intra_step_simulation:
  "control_at \<Pi> p c0 k n c v \<Longrightarrow>
   intra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> source_com c0 \<Longrightarrow>
   frs' = frs \<and> (\<exists>v'. control_at \<Pi> p c0 k n c' v' \<and> star (cstep source_global g) (v, s, stk) (v', s', stk))"
proof (induction arbitrary: c' s' frs' n' en E K rule: control_at.induct)
  case (Skip k n0) then show ?case by (blast elim: intra_SkipE)
next
  case (Assign x a k n0)
  from Assign.prems(1) have out: "c' = SKIP" "s' = s(x := aval a s)" "frs' = frs"
    by (auto elim: intra_AssignE)
  have ca: "control_at \<Pi> p (Assign x a) k n0 (Assign x a) (Statement n0)" by (rule control_at.Assign)
  from control_at_assign_edge[OF ca refl Assign.prems(2)] obtain j w where
    jw: "Statement n0 = Statement j" "(Statement j, EA_Assign x a, w) \<in> E"
        "control_at \<Pi> p (Assign x a) k n0 SKIP w" by blast
  have "(Statement j, EA_Assign x a, w) \<in> intra g"
    using jw(2) Assign.prems(3) by blast
  from cstep_assign[OF this]
  have "cstep source_global g (Statement j, s, stk) (w, s(x := aval a s), stk)" by simp
  then have "star (cstep source_global g) (Statement n0, s, stk) (w, s', stk)"
    using jw(1) out(2) by (simp add: cstep_star_single)
  then show ?case using out(1,3) jw(3) by auto
next
  case (AssignDone x a k n0) then show ?case by (blast elim: intra_SkipE)
next
  case (SeqLeft c1 n0 r v c2 k)
  from intra_Seq_cases[OF SeqLeft.prems(1)] consider
      (s1) "r = SKIP" "c' = c2" "s' = s" "frs' = frs"
    | (s2) r' where "c' = Seq r' c2" "frs' = frs" "intra_step \<Pi> (r, s, frs) (r', s', frs)"
    by blast
  then show ?case
  proof cases
    case s1
    have loc: "control_at \<Pi> p (Seq c1 c2) k n0 (Seq SKIP c2) v"
      using control_at.SeqLeft[OF SeqLeft.hyps] s1(1) by simp
    from control_at_seq_skip_reloc[OF loc refl SeqLeft.prems(2,3,4)]
    obtain v' where "control_at \<Pi> p (Seq c1 c2) k n0 c2 v'"
      "star (cstep source_global g) (v, s, stk) (v', s, stk)" by blast
    then show ?thesis using s1 by auto
  next
    case s2
    from SeqLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
      c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
      and Eeq: "E = E1 \<union> E2"
      by (rule compile_SeqE)
    have sub: "E1 \<subseteq> E" using Eeq by blast
    have src1: "source_com c1" using SeqLeft.prems(4) by simp
    from SeqLeft.IH[OF s2(3) c1c subset_trans[OF sub SeqLeft.prems(3)] src1]
    obtain v' where v': "control_at \<Pi> p c1 (Statement (n0 + csize c1)) n0 r' v'"
      "star (cstep source_global g) (v, s, stk) (v', s', stk)" by auto
    have "control_at \<Pi> p (Seq c1 c2) k n0 (Seq r' c2) v'"
      using control_at.SeqLeft[OF v'(1)] .
    then show ?thesis using s2 v'(2) by auto
  qed
next
  case (SeqRight c1 c2 k n0 r v)
  from SeqRight.prems(2) obtain n2 E2 K2 n1 E1 K1 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and Eeq: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  have sub: "E2 \<subseteq> E" using Eeq by blast
  have src2: "source_com c2" using SeqRight.prems(4) by simp
  from SeqRight.IH[OF SeqRight.prems(1) c2c subset_trans[OF sub SeqRight.prems(3)] src2]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c2 k (n0 + csize c1) c' v' \<and> star (cstep source_global g) (v, s, stk) (v', s', stk)"
    by auto
  then obtain v' where v': "control_at \<Pi> p c2 k (n0 + csize c1) c' v'"
    "star (cstep source_global g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 c' v'"
    using control_at.SeqRight[OF SeqRight.hyps(1) v'(1)] .

  with fr v'(2) show ?case by blast
next
  case (IfHead b c1 c2 k n0)
  have ca: "control_at \<Pi> p (If b c1 c2) k n0 (If b c1 c2) (Statement n0)" by (rule control_at.IfHead)
  from control_at_if_edges[OF ca refl IfHead.prems(4) IfHead.prems(2)] obtain j en1 en2 where
    jj: "Statement n0 = Statement j"
       "(Statement j, EA_Assume b, en1) \<in> E" "(Statement j, EA_AssumeNot b, en2) \<in> E"
       "control_at \<Pi> p (If b c1 c2) k n0 c1 en1" "control_at \<Pi> p (If b c1 c2) k n0 c2 en2" by blast
  from intra_If_cases[OF IfHead.prems(1)] consider
      (t) "bval b s" "c' = c1" "s' = s" "frs' = frs"
    | (f) "\<not> bval b s" "c' = c2" "s' = s" "frs' = frs" by blast
  then show ?case
  proof cases
    case t
    have "(Statement j, EA_Assume b, en1) \<in> intra g" using jj(2) IfHead.prems(3) by blast
    from cstep_assume[OF this] t(1)
    have "star (cstep source_global g) (Statement n0, s, stk) (en1, s, stk)"
      using jj(1) by (simp add: cstep_star_single)
    then show ?thesis using t jj(4) by auto
  next
    case f
    have "(Statement j, EA_AssumeNot b, en2) \<in> intra g" using jj(3) IfHead.prems(3) by blast
    from cstep_assume_not[OF this] f(1)
    have "star (cstep source_global g) (Statement n0, s, stk) (en2, s, stk)"
      using jj(1) by (simp add: cstep_star_single)
    then show ?thesis using f jj(5) by auto
  qed
next
  case (IfLeft c1 k n0 r v b c2)
  from IfLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and Eeq: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                   (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  have sub1: "E1 \<subseteq> E" using Eeq by blast
  have src1: "source_com c1" using IfLeft.prems(4) by simp
  from IfLeft.IH[OF IfLeft.prems(1) c1c subset_trans[OF sub1 IfLeft.prems(3)] src1]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c1 k (Suc n0) c' v' \<and> star (cstep source_global g) (v, s, stk) (v', s', stk)" by auto
  then obtain v' where v': "control_at \<Pi> p c1 k (Suc n0) c' v'"
    "star (cstep source_global g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 c' v'" using control_at.IfLeft[OF v'(1)] .
  with fr v'(2) show ?case by blast
next
  case (IfRight c2 k n0 c1 r v b)
  from IfRight.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and Eeq: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                   (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  have sub2: "E2 \<subseteq> E" using Eeq by blast
  have src2: "source_com c2" using IfRight.prems(4) by simp
  from IfRight.IH[OF IfRight.prems(1) c2c subset_trans[OF sub2 IfRight.prems(3)] src2]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c2 k (Suc n0 + csize c1) c' v'
          \<and> star (cstep source_global g) (v, s, stk) (v', s', stk)" by auto
  then obtain v' where v': "control_at \<Pi> p c2 k (Suc n0 + csize c1) c' v'"
    "star (cstep source_global g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 c' v'" using control_at.IfRight[OF v'(1)] .
  with fr v'(2) show ?case by blast
next
  case (IfDone b c1 c2 k n0) then show ?case by (blast elim: intra_SkipE)
next
  case (WhileHead b cW k n0)
  from WhileHead.prems(1) have out: "c' = If b (Seq cW (While b cW)) SKIP" "s' = s" "frs' = frs"
    by (auto elim: intra_WhileE)
  have "control_at \<Pi> p (While b cW) k n0 (If b (Seq cW (While b cW)) SKIP) (Statement n0)"
    by (rule control_at.WhileUnfolded)
  then show ?case using out by (auto intro: star.refl)
next
  case (WhileUnfolded b cW k n0)
  have ca: "control_at \<Pi> p (While b cW) k n0 (If b (Seq cW (While b cW)) SKIP) (Statement n0)"
    by (rule control_at.WhileUnfolded)
  have srcif: "source_com (If b (Seq cW (While b cW)) SKIP)" using WhileUnfolded.prems(4) by simp
  from control_at_if_edges[OF ca refl srcif WhileUnfolded.prems(2)]
  obtain j en1 en2 where
    jj: "Statement n0 = Statement j"
       "(Statement j, EA_Assume b, en1) \<in> E" "(Statement j, EA_AssumeNot b, en2) \<in> E"
       "control_at \<Pi> p (While b cW) k n0 (Seq cW (While b cW)) en1"
       "control_at \<Pi> p (While b cW) k n0 SKIP en2" by blast
  from intra_If_cases[OF WhileUnfolded.prems(1)] consider
      (t) "bval b s" "c' = Seq cW (While b cW)" "s' = s" "frs' = frs"
    | (f) "\<not> bval b s" "c' = SKIP" "s' = s" "frs' = frs" by blast
  then show ?case
  proof cases
    case t
    have "(Statement j, EA_Assume b, en1) \<in> intra g" using jj(2) WhileUnfolded.prems(3) by blast
    from cstep_assume[OF this] t(1)
    have "star (cstep source_global g) (Statement n0, s, stk) (en1, s, stk)"
      using jj(1) by (simp add: cstep_star_single)
    then show ?thesis using t jj(4) by auto
  next
    case f
    have "(Statement j, EA_AssumeNot b, en2) \<in> intra g" using jj(3) WhileUnfolded.prems(3) by blast
    from cstep_assume_not[OF this] f(1)
    have "star (cstep source_global g) (Statement n0, s, stk) (en2, s, stk)"
      using jj(1) by (simp add: cstep_star_single)
    then show ?thesis using f jj(5) by auto
  qed
next
  case (WhileBody cW n0 r v b k)
  from intra_Seq_cases[OF WhileBody.prems(1)] consider
      (s1) "r = SKIP" "c' = While b cW" "s' = s" "frs' = frs"
    | (s2) r' where "c' = Seq r' (While b cW)" "frs' = frs" "intra_step \<Pi> (r, s, frs) (r', s', frs)"
    by blast
  then show ?case
  proof cases
    case s1
    have loc: "control_at \<Pi> p (While b cW) k n0 (Seq SKIP (While b cW)) v"
      using control_at.WhileBody[OF WhileBody.hyps] s1(1) by simp
    from control_at_seq_skip_reloc[OF loc refl WhileBody.prems(2,3,4)]
    obtain v' where "control_at \<Pi> p (While b cW) k n0 (While b cW) v'"
      "star (cstep source_global g) (v, s, stk) (v', s, stk)" by blast
    then show ?thesis using s1 by auto
  next
    case s2
    from WhileBody.prems(2) obtain n1 E1 K1 where
      cc: "compile \<Pi> p cW (Statement n0) (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
      and Eeq: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                     (Statement n0, EA_AssumeNot b, k)} \<union> E1"
      by (rule compile_WhileE)
    have sub: "E1 \<subseteq> E" using Eeq by blast
    have srcW: "source_com cW" using WhileBody.prems(4) by simp
    from WhileBody.IH[OF s2(3) cc subset_trans[OF sub WhileBody.prems(3)] srcW]
    obtain v' where v': "control_at \<Pi> p cW (Statement n0) (Suc n0) r' v'"
      "star (cstep source_global g) (v, s, stk) (v', s', stk)" by auto
    have "control_at \<Pi> p (While b cW) k n0 (Seq r' (While b cW)) v'"
      using control_at.WhileBody[OF v'(1)] .
    then show ?thesis using s2 v'(2) by auto
  qed
next
  case (WhileDone b cW k n0) then show ?case by (blast elim: intra_SkipE)
next
  case (CallHead dst q actuals k n0) then show ?case by (blast elim: intra_CallE)
next
  case (CallDone dst q actuals k n0) then show ?case by (blast elim: intra_SkipE)
next
  case (ReturnHead e k n0) then show ?case by (blast elim: intra_ReturnE)
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



subsection \<open>The empty-stack return guard\<close>

text \<open>A bare \<^const>\<open>Unwind\<close> is stuck --- a return with no activation to pop cannot step.\<close>

lemma pstep_Unwind_stuck: "\<not> pstep source_global \<Pi> (Unwind, s, frs) x"
  by (auto elim: UnwindSE)


section \<open>The recursive source-command / CFG-stack relation\<close>

subsection \<open>Real-procedure activation identity\<close>

text \<open>
  \<open>proc_activation \<Pi> p c0\<close> pins an activation's fragment origin \<open>c0\<close> to a genuine procedure body:
  \<open>p\<close> is declared in \<open>\<Pi>\<close> and \<open>c0\<close> is exactly its body.  \<open>csim\<close> carries it on every activation so
  that preservation is stated only over real procedures --- \<^const>\<open>control_at\<close>'s fragment parameter
  \<open>c0\<close> is otherwise free and would admit spurious (non-procedure) activations for which ordinary
  fall-through preservation is false.  This is the \<^emph>\<open>only\<close> thing added to \<open>csim\<close>; all compile
  tuples, edge inclusions, and graph wiring stay in \<open>procs_compiled\<close>.
\<close>

definition proc_activation :: "proc_table \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> bool" where
  "proc_activation \<Pi> p c0 \<longleftrightarrow> (\<exists>decl. \<Pi> p = Some decl \<and> c0 = body decl)"

lemma proc_activationD [elim]:
  assumes "proc_activation \<Pi> p c0"
  obtains decl where "\<Pi> p = Some decl" "c0 = body decl"
  using assms unfolding proc_activation_def by blast

subsection \<open>The caller continuation after a call\<close>

text \<open>
  A call site's caller has, after the call, a finite left-spine of residual continuations
  \<^term>\<open>afters\<close>: the source commands sequenced after the call, in execution order, collected while
  descending the current activation's left-associated \<^const>\<open>Seq\<close> spine.  \<^term>\<open>seq_after c afters\<close>
  wraps them around the active head \<open>c\<close>, appending each in order:
  \<^term>\<open>seq_after c [s3, s4] = Seq (Seq c s3) s4\<close>.  A \<^emph>\<open>tail-position\<close> call (the call is the caller's
  last command, including the top-level entry call) has no continuation --- \<^term>\<open>afters = []\<close> ---
  and the caller resumes at bare \<open>c\<close>; a call with pending commands carries them in \<open>afters\<close> and the
  caller resumes at \<^term>\<open>seq_after SKIP afters\<close>.  Every case runs through the same activation
  machinery (the frame is pushed and popped identically); only the caller's leftover source differs.
  The continuation list is orthogonal to \<open>csim\<close>'s recursive nesting: \<open>afters\<close> holds pending commands
  \<^emph>\<open>inside one activation\<close>, while recursive nesting holds suspended \<^emph>\<open>caller activations\<close>.
\<close>
fun seq_after :: "com \<Rightarrow> com list \<Rightarrow> com" where
  "seq_after c [] = c"
| "seq_after c (a # as) = seq_after (Seq c a) as"

text \<open>Appending continuation lists composes the wrappers.\<close>
lemma seq_after_append: "seq_after (seq_after c xs) ys = seq_after c (xs @ ys)"
  by (induction xs arbitrary: c) auto

text \<open>A single trailing continuation is one \<^const>\<open>Seq\<close> layer; a nonempty list exposes its outermost
  \<^const>\<open>Seq\<close> at the last element.\<close>
lemma seq_after_singleton [simp]: "seq_after c [a] = Seq c a"
  by simp

lemma seq_after_snoc: "seq_after c (xs @ [a]) = Seq (seq_after c xs) a"
  by (simp add: seq_after_append[symmetric])

text \<open>\<^const>\<open>seq_after\<close> heads with a bare atom only in the empty-continuation shape: a nonempty
  continuation list always exposes an outermost \<^const>\<open>Seq\<close>.  These discriminators drive the
  returning inversions.\<close>
lemma seq_after_eq_SKIP_iff [simp]:
  "(seq_after c afters = SKIP) = (c = SKIP \<and> afters = [])"
  "(SKIP = seq_after c afters) = (c = SKIP \<and> afters = [])"
  by (induction afters arbitrary: c; auto)+

lemma seq_after_eq_Restore_iff [simp]:
  "(seq_after c afters = Restore) = (c = Restore \<and> afters = [])"
  "(Restore = seq_after c afters) = (c = Restore \<and> afters = [])"
  by (induction afters arbitrary: c; auto)+

lemma seq_after_eq_Unwind_iff [simp]:
  "(seq_after c afters = Unwind) = (c = Unwind \<and> afters = [])"
  "(Unwind = seq_after c afters) = (c = Unwind \<and> afters = [])"
  by (induction afters arbitrary: c; auto)+

text \<open>\<^const>\<open>seq_after\<close> heads with any non-\<^const>\<open>Seq\<close> atom only in the empty-continuation shape:
  a nonempty continuation always exposes an outermost \<^const>\<open>Seq\<close>.  These drive the leaf cases of the
  located-call induction.\<close>
lemma seq_after_eq_Assign_iff [simp]:
  "(seq_after c afters = Assign x a) = (c = Assign x a \<and> afters = [])"
  "(Assign x a = seq_after c afters) = (c = Assign x a \<and> afters = [])"
  by (induction afters arbitrary: c; auto)+

lemma seq_after_eq_If_iff [simp]:
  "(seq_after c afters = If b c1 c2) = (c = If b c1 c2 \<and> afters = [])"
  "(If b c1 c2 = seq_after c afters) = (c = If b c1 c2 \<and> afters = [])"
  by (induction afters arbitrary: c; auto)+

lemma seq_after_eq_While_iff [simp]:
  "(seq_after c afters = While b cw) = (c = While b cw \<and> afters = [])"
  "(While b cw = seq_after c afters) = (c = While b cw \<and> afters = [])"
  by (induction afters arbitrary: c; auto)+

lemma seq_after_eq_Return_iff [simp]:
  "(seq_after c afters = Return e) = (c = Return e \<and> afters = [])"
  "(Return e = seq_after c afters) = (c = Return e \<and> afters = [])"
  by (induction afters arbitrary: c; auto)+

lemma seq_after_eq_Call_iff [simp]:
  "(seq_after c afters = Call dst q actuals) = (c = Call dst q actuals \<and> afters = [])"
  "(Call dst q actuals = seq_after c afters) = (c = Call dst q actuals \<and> afters = [])"
  by (induction afters arbitrary: c; auto)+


lemma source_com_seq_afterD:
  "source_com (seq_after c afters) \<Longrightarrow>
   source_com c \<and> (\<forall>a \<in> set afters. source_com a)"
proof (induction afters arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons a afters)
  have h: "source_com (seq_after (Seq c a) afters)"
    using Cons.prems by simp
  from Cons.IH[OF h] have h1: "source_com (Seq c a)"
    and h2: "\<forall>b \<in> set afters. source_com b" by blast+
  from h1 h2 show ?case by auto
qed

lemma control_at_head_return_afters_no_Restore:
  assumes "control_at \<Pi> p c0 k n (seq_after (Return e) afters) v"
      and "source_com c0"
  shows "\<forall>a \<in> set afters. a \<noteq> Restore"
proof (rule ballI)
  fix a
  assume ain: "a \<in> set afters"
  from control_at_source_com[OF assms] source_com_seq_afterD
  have "source_com a" using ain by blast
  then show "a \<noteq> Restore" by (rule source_com_no_Restore)
qed

text \<open>Located call with pending continuations: when the caller's active residual is a \<^const>\<open>Call\<close>
  at the bottom-left of a \<^const>\<open>seq_after\<close> spine (the call site with its right-siblings \<open>afters\<close>),
  the compiled call edge is still the one the compiler emitted at the call node, and the source step
  re-locates \<^term>\<open>seq_after SKIP afters\<close> --- \<^const>\<open>SKIP\<close> followed by the same pending continuations
  --- at the call's continuation node.  Generalises \<open>control_at_call_edge\<close> (its \<^term>\<open>afters = []\<close>
  instance): the \<open>SeqLeft\<close> / \<open>WhileBody\<close> cases peel the outermost continuation, the passthrough
  cases keep it, and the leaf cases are impossible (a \<^const>\<open>seq_after\<close> spine never equals a
  non-\<^const>\<open>Seq\<close> atom unless its head does and the list is empty).\<close>
lemma control_at_seq_after_call_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = seq_after (Call dst q actuals) afters \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j w. v = Statement j
       \<and> (Statement j, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
          FunctionEntry q, w) \<in> K
       \<and> control_at \<Pi> p c0 k n (seq_after SKIP afters) w"
proof (induction arbitrary: afters n' en E K rule: control_at.induct)
  case (CallHead dst' q' actuals' k n0 afters)
  then show ?case by (auto intro: control_at.CallDone)
next
  case (SeqLeft c1 n0 r v c2 k afters)
  obtain xs where afx: "afters = xs @ [c2]" and req: "r = seq_after (Call dst q actuals) xs"
    using SeqLeft.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from SeqLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
    and Keq: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  from SeqLeft.IH[OF req c1c] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
         FunctionEntry q, w) \<in> K1"
       "control_at \<Pi> p c1 (Statement (n0 + csize c1)) n0 (seq_after SKIP xs) w" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 (seq_after SKIP afters) w"
    using control_at.SeqLeft[OF jw(3)] by (simp add: afx seq_after_snoc)
  then show ?case using jw Keq by blast
next
  case (SeqRight c1 c2 k n0 r v afters)
  from SeqRight.prems(2) obtain n2 E2 K2 n1 E1 K1 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and Keq: "K = K1 \<union> K2"
    by (rule compile_SeqE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
         FunctionEntry q, w) \<in> K2"
       "control_at \<Pi> p c2 k (n0 + csize c1) (seq_after SKIP afters) w" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 (seq_after SKIP afters) w"
    using control_at.SeqRight[OF SeqRight.hyps(1) jw(3)] .

  then show ?case using jw Keq by blast
next
  case (IfLeft c1 k n0 r v b c2 afters)
  from IfLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and Keq: "K = K1 \<union> K2"
    by (rule compile_IfE)
  from IfLeft.IH[OF IfLeft.prems(1) c1c] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
         FunctionEntry q, w) \<in> K1"
       "control_at \<Pi> p c1 k (Suc n0) (seq_after SKIP afters) w" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 (seq_after SKIP afters) w"
    using control_at.IfLeft[OF jw(3)] .
  then show ?case using jw Keq by blast
next
  case (IfRight c2 k n0 c1 r v b afters)
  from IfRight.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and Keq: "K = K1 \<union> K2"
    by (rule compile_IfE)
  from IfRight.IH[OF IfRight.prems(1) c2c] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
         FunctionEntry q, w) \<in> K2"
       "control_at \<Pi> p c2 k (Suc n0 + csize c1) (seq_after SKIP afters) w" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 (seq_after SKIP afters) w"
    using control_at.IfRight[OF jw(3)] .
  then show ?case using jw Keq by blast
next
  case (WhileBody c n0 r v b k afters)
  obtain xs where afx: "afters = xs @ [While b c]"
      and req: "r = seq_after (Call dst q actuals) xs"
    using WhileBody.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from WhileBody.prems(2) obtain n1 E1 K1 where
    cc: "compile \<Pi> p c (Statement n0) (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and Keq: "K = K1"
    by (rule compile_WhileE)
  from WhileBody.IH[OF req cc] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (case \<Pi> q of Some decl \<Rightarrow> formals decl | None \<Rightarrow> []) actuals,
         FunctionEntry q, w) \<in> K1"
       "control_at \<Pi> p c (Statement n0) (Suc n0) (seq_after SKIP xs) w" by blast
  have "control_at \<Pi> p (While b c) k n0 (seq_after SKIP afters) w"
    using control_at.WhileBody[OF jw(3)] by (simp add: afx seq_after_snoc)
  then show ?case using jw Keq by blast
qed simp_all

text \<open>Located return with pending continuations: a source \<^const>\<open>Return\<close> at the bottom-left of a
  \<^const>\<open>seq_after\<close> spine sits on the compiled \<^term>\<open>EA_Ret e p\<close> edge the compiler emitted at the
  return node.  Generalises \<open>control_at_return_edge\<close> (its \<^term>\<open>afters = []\<close> instance); the
  \<open>SeqLeft\<close> / \<open>WhileBody\<close> cases peel the outermost continuation and the passthrough cases keep it.\<close>
lemma control_at_seq_after_return_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = seq_after (Return e) afters \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j. v = Statement j \<and> (Statement j, EA_Ret e p, FunctionResult p) \<in> E"
proof (induction arbitrary: afters n' en E K rule: control_at.induct)
  case (ReturnHead e' k n0 afters)
  then show ?case by auto
next
  case (SeqLeft c1 n0 r v c2 k afters)
  obtain xs where afx: "afters = xs @ [c2]" and req: "r = seq_after (Return e) xs"
    using SeqLeft.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from SeqLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
    and Eeq: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  from SeqLeft.IH[OF req c1c] show ?case using Eeq by blast
next
  case (SeqRight c1 c2 k n0 r v afters)

  from SeqRight.prems(2) obtain n2 E2 K2 n1 E1 K1 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and Eeq: "E = E1 \<union> E2"
    by (rule compile_SeqE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] show ?case using Eeq by blast
next
  case (IfLeft c1 k n0 r v b c2 afters)
  from IfLeft.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and Eeq: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                   (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  from IfLeft.IH[OF IfLeft.prems(1) c1c] show ?case using Eeq by blast
next
  case (IfRight c2 k n0 c1 r v b afters)
  from IfRight.prems(2) obtain n1 E1 K1 n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and Eeq: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                   (Statement n0, EA_AssumeNot b, Statement (Suc n0 + csize c1))} \<union> E1 \<union> E2"
    by (rule compile_IfE)
  from IfRight.IH[OF IfRight.prems(1) c2c] show ?case using Eeq by blast
next
  case (WhileBody c n0 r v b k afters)
  obtain xs where afx: "afters = xs @ [While b c]" and req: "r = seq_after (Return e) xs"
    using WhileBody.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from WhileBody.prems(2) obtain n1 E1 K1 where
    cc: "compile \<Pi> p c (Statement n0) (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and Eeq: "E = {(Statement n0, EA_Assume b, Statement (Suc n0)),
                   (Statement n0, EA_AssumeNot b, k)} \<union> E1"
    by (rule compile_WhileE)
  from WhileBody.IH[OF req cc] show ?case using Eeq by blast
qed simp_all
subsection \<open>The returning (frame-pop) source shapes\<close>

text \<open>
  Once a callee finishes, the CFG is already at \<^term>\<open>FunctionResult p\<close> while the source propagates
  toward the frame-pop rule.  \<open>unwinding\<close> describes an \<^const>\<open>Unwind\<close> travelling up through the
  callee's residual, dropping the dead code it skips (never the activation's own \<^const>\<open>Restore\<close>);
  \<open>pop_ready\<close> describes the whole activation body in that phase --- either the normal
  fall-through \<^const>\<open>Restore\<close> or an \<^const>\<open>Unwind\<close> spine \<open>Seq u Restore\<close> from an explicit
  \<^const>\<open>Return\<close>.  Both pop the single caller frame with one \<open>cstep\<close> return; \<open>unwinding\<close>
  propagation is matched by \<^emph>\<open>no\<close> CFG step (the CFG waits at \<^term>\<open>FunctionResult p\<close>).
\<close>
fun unwinding :: "com \<Rightarrow> bool" where
  "unwinding Unwind = True"
| "unwinding (Seq u c2) = (unwinding u \<and> c2 \<noteq> Restore)"
| "unwinding _ = False"

fun pop_ready :: "com \<Rightarrow> bool" where
  "pop_ready Restore = True"
| "pop_ready (Seq u Restore) = unwinding u"
| "pop_ready _ = False"

lemma unwinding_not_SKIP: "unwinding u \<Longrightarrow> u \<noteq> SKIP"
  by (cases u) auto

lemma pop_ready_not_SKIP: "pop_ready w \<Longrightarrow> w \<noteq> SKIP"
  by (cases w rule: pop_ready.cases) auto

lemma pop_ready_not_Unwind: "pop_ready w \<Longrightarrow> w \<noteq> Unwind"
  by (cases w rule: pop_ready.cases) auto

subsection \<open>Compile-into-\<open>g\<close> evidence for an active fragment\<close>

text \<open>
  \<open>compiled_at Pi g p c0 k n\<close> witnesses that the fragment \<open>c0\<close>, compiled at the exact offset
  \<open>n\<close> with continuation \<open>k\<close>, is embedded in the target graph \<open>g\<close>: its intra edges lie in
  \<^term>\<open>intra g\<close> and its call edges in \<^term>\<open>calls g\<close>.  \<open>csim\<close> carries it on every activation at
  the \<^emph>\<open>same\<close> \<open>k\<close> and \<open>n\<close> that \<^const>\<open>control_at\<close> uses, so the located node and the fragment's
  edges are genuinely present in \<open>g\<close>.  Compilation is shift-parametric --- neither the offset
  nor the continuation is fixed by the syntax --- so graph membership at the chosen offset is
  the missing fact, and this predicate supplies it.

  The continuation of a procedure body is its epilogue node, which is why the fall-through
  return edge is stated from \<open>k\<close>.  That edge exists only when the body can actually fall through
  to it, so the requirement is guarded by \<^const>\<open>falls_through\<close>; \<open>control_at_SKIP_imp_falls_through\<close>
  discharges the guard wherever a completed (\<^const>\<open>SKIP\<close>) residual needs the edge.
\<close>
definition compiled_at ::
  "proc_table \<Rightarrow> cfg \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> nat \<Rightarrow> bool" where
  "compiled_at \<Pi> g p c0 k n \<longleftrightarrow>
     (\<exists>n' en E K. compile \<Pi> p c0 k n = (n', en, E, K)
        \<and> E \<subseteq> intra g \<and> K \<subseteq> calls g
        \<and> (falls_through c0 \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g))"

lemma compiled_atI:
  "compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> K \<subseteq> calls g \<Longrightarrow>
   (falls_through c0 \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g) \<Longrightarrow>
   compiled_at \<Pi> g p c0 k n"
  unfolding compiled_at_def by blast


lemma compiled_atE [elim]:
  assumes "compiled_at \<Pi> g p c0 k n"
  obtains n' en E K where
    "compile \<Pi> p c0 k n = (n', en, E, K)" "E \<subseteq> intra g" "K \<subseteq> calls g"
    "falls_through c0 \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g"
  using assms unfolding compiled_at_def by blast

text \<open>Focused exit projection: read the fall-through \<^term>\<open>EA_Ret None p\<close> edge into
  \<^term>\<open>FunctionResult p\<close> off a \<^const>\<open>compiled_at\<close> witness.  This is the edge the
  callee-completion path needs but which otherwise lives only in \<open>procs_compiled\<close> at the
  procedure's compile offset.  It is available exactly when the fragment can complete normally,
  which a located \<^const>\<open>SKIP\<close> residual witnesses.\<close>

lemma compiled_at_exit:
  "compiled_at \<Pi> g p c0 k n \<Longrightarrow> falls_through c0 \<Longrightarrow>
   (k, EA_Ret None p, FunctionResult p) \<in> intra g"
  unfolding compiled_at_def by auto


text \<open>
  \<open>csim\<close> relates a source configuration \<^term>\<open>(c, s, frs)\<close> to a CFG configuration
  \<^term>\<open>(v, s, stk)\<close> with literal store equality (the same \<open>s\<close>).  It bridges the two
  continuation representations: the source keeps every suspended caller's continuation nested
  inside the single command \<open>c\<close> (defunctionalized as \<^term>\<open>Seq (Seq inner Restore) after\<close>
  wrappings, one per activation), while the CFG keeps them as continuation nodes on the frame
  stack.

  The nesting runs outermost-first: after \<open>main\<close> calls \<open>f\<close> calls \<open>g\<close>, the command is
  \<open>Seq (Seq (Seq (Seq C Restore) B) Restore) A\<close> with \<open>A\<close> the outermost (main's) continuation and
  \<open>C\<close> the active (g's) residual.  So the \<^emph>\<open>top\<close> command layer pairs with the \<^emph>\<open>last\<close> (outermost)
  frame, and the active node/store thread unchanged down to the \<open>Base\<close> case.
    \<^item> \<open>Base\<close> --- one activation: the active residual \<open>c\<close> is located at \<open>v\<close> and the frame
      stacks are empty.
    \<^item> \<open>Nested\<close> --- peel the outermost caller: the command's top layer
      \<^term>\<open>Seq (Seq inner Restore) after\<close> and the last frame \<^term>\<open>Frame caller dst\<close> pair with the
      CFG's last frame \<^term>\<open>(cont, dst, caller)\<close>; the caller's post-call residual
      \<^term>\<open>Seq SKIP after\<close> is located at the continuation node \<open>cont\<close>; and the remaining inner
      structure is related recursively.

  \<open>csim\<close> has three constructors --- one per source phase.  \<open>Base\<close> and \<open>Nested\<close>
  cover \<^emph>\<open>ordinary\<close> execution (residuals located by \<^const>\<open>control_at\<close> at \<^term>\<open>Statement\<close>
  nodes).  \<open>Returning\<close> covers the \<^emph>\<open>return-in-progress\<close> phase: once a callee's body has
  completed (fall-through), the innermost source layer is \<^term>\<open>Seq Restore after\<close> and the CFG
  sits at \<^term>\<open>FunctionResult p\<close>, one \<^const>\<open>cstep\<close> return away from resuming the caller.  Like
  \<open>Base\<close> it is an innermost constructor (an alternative to it), wrapped by any number of
  outer \<open>Nested\<close> layers.  It carries exactly the \<^emph>\<open>one\<close> frame the return pops (the immediate
  caller's save); the outer callers' frames are consumed by the wrapping \<open>Nested\<close> layers.  Its
  premise locates the \<^emph>\<open>resumed caller\<close> --- the ordinary residual \<^term>\<open>Seq SKIP after\<close> the return
  will land in, at the continuation node \<open>cont\<close> --- so return completion pops the single frame and
  the caller resumes as a \<open>Base\<close> activation (the outer \<open>Nested\<close> wrapping is untouched).  The active
  store is a free rider (\<^const>\<open>control_at\<close> is store-independent).
\<close>
inductive csim :: "proc_table \<Rightarrow> cfg \<Rightarrow> com \<times> store \<times> frame list
                    \<Rightarrow> cfg_node \<times> store \<times> cframe list \<Rightarrow> bool" for \<Pi> g where
  Base:
    "control_at \<Pi> p c0 k n c v \<Longrightarrow> compiled_at \<Pi> g p c0 k n \<Longrightarrow> proc_activation \<Pi> p c0 \<Longrightarrow>
     csim \<Pi> g (c, s, []) (v, s, [])"
| Nested:
    "csim \<Pi> g (inner, s, frs) (v, s, stk) \<Longrightarrow>
     control_at \<Pi> pc c0c kc nc (seq_after SKIP afters) cont \<Longrightarrow>
     compiled_at \<Pi> g pc c0c kc nc \<Longrightarrow>
     proc_activation \<Pi> pc c0c \<Longrightarrow>
     csim \<Pi> g (seq_after (Seq inner Restore) afters, s, frs @ [Frame caller dst])
              (v, s, stk @ [(cont, dst, caller)])"
| Returning:
    "pop_ready w \<Longrightarrow>
     control_at \<Pi> pc c0c kc nc (seq_after SKIP afters) cont \<Longrightarrow>
     compiled_at \<Pi> g pc c0c kc nc \<Longrightarrow>
     proc_activation \<Pi> pc c0c \<Longrightarrow>
     csim \<Pi> g (seq_after w afters, callee, [Frame caller dst])
              (FunctionResult p, callee, [(cont, dst, caller)])"
inductive_cases csim_NilE: "csim \<Pi> g (c, s, []) cfgc"
inductive_cases csim_cfg_NilE: "csim \<Pi> g srcc (v, t, [])"

subsection \<open>Derived structural facts\<close>

text \<open>The relation forces literal store equality (encoded by the shared \<open>s\<close>).\<close>
lemma csim_store_eq:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> s = t"
  by (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c frs v stk rule: csim.induct) auto

text \<open>\<^const>\<open>act_frames\<close> distributes over append (single frame constructor).\<close>
lemma act_frames_append:
  "act_frames (xs @ ys) = act_frames xs @ act_frames ys"
  by (induction xs rule: act_frames.induct) auto

lemma frames_match_snoc:
  "frames_match frs stk \<Longrightarrow>
   frames_match (frs @ [Frame caller dst]) (stk @ [(cont, dst, caller)])"
  by (simp add: frames_match_def act_frames_append cframe_act_def)



subsection \<open>Empty-stack inversions\<close>


text \<open>An empty source stack forces an empty CFG stack and a located base activation.\<close>
lemma csim_Nil_baseD:
  "csim \<Pi> g (c, s, []) (v, t, stk) \<Longrightarrow>
   stk = [] \<and> s = t \<and> (\<exists>p c0 k n. control_at \<Pi> p c0 k n c v)"
  by (blast elim: csim_NilE)

subsection \<open>Real-procedure projections\<close>

text \<open>A base activation's active residual originates from a real procedure body: the located
  fragment \<open>c0\<close> is exactly \<^term>\<open>body decl\<close> for the declared procedure \<open>p\<close>.  This is the identity
  the ordinary and fall-through preservation cases read off to reach \<open>procs_compiled\<close>.\<close>
lemma csim_base_procD:
  assumes "csim \<Pi> g (c, s, []) (v, t, stk)"
  obtains p c0 k n where
    "control_at \<Pi> p c0 k n c v" "compiled_at \<Pi> g p c0 k n" "proc_activation \<Pi> p c0"
  using assms by (blast elim: csim_NilE)

subsection \<open>Returning-mode inversions\<close>

text \<open>Ordinary location never produces a \<^const>\<open>Restore\<close>-headed residual: \<^const>\<open>control_at\<close>
  locates only source residuals, and \<^const>\<open>Restore\<close> is a runtime-only marker.  This is what
  distinguishes an ordinary \<open>Base\<close> from the returning phase.\<close>
lemma control_at_no_restore:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r \<noteq> Restore \<and> (\<forall>after. r \<noteq> Seq Restore after)"
  by (induction rule: control_at.induct) auto

text \<open>A bare \<^const>\<open>Restore\<close> residual can only come from the \<open>Returning\<close> constructor with an empty
  caller continuation (\<^term>\<open>ao = None\<close> --- a tail-position or top-level call): \<open>Base\<close> is excluded
  (ordinary location never heads with \<^const>\<open>Restore\<close>) and \<open>Nested\<close> heads with a \<^term>\<open>Seq inner Restore\<close>.
  The inversion exposes the single returning frame, the callee store, the procedure result node, and
  the resumed-caller relation (resuming at bare \<^const>\<open>SKIP\<close>).\<close>
lemma csim_bare_restore_exists:
  "csim \<Pi> g (Restore, callee, frs) (v, t, stk) \<Longrightarrow>
   (\<exists>cont caller dst p pc c0c kc nc.
      frs = [Frame caller dst] \<and> stk = [(cont, dst, caller)] \<and>
      v = FunctionResult p \<and> t = callee \<and>
      control_at \<Pi> pc c0c kc nc SKIP cont \<and> proc_activation \<Pi> pc c0c)"
  by (erule csim.cases) (auto dest: control_at_no_restore)

lemma csim_bare_restoreD [elim]:
  assumes "csim \<Pi> g (Restore, callee, frs) (v, t, stk)"
  obtains cont caller dst p pc c0c kc nc where
    "frs = [Frame caller dst]" "stk = [(cont, dst, caller)]"
    "v = FunctionResult p" "t = callee"
    "control_at \<Pi> pc c0c kc nc SKIP cont" "proc_activation \<Pi> pc c0c"
  using csim_bare_restore_exists[OF assms] by blast
subsection \<open>Returning commands and the frame-pop phase\<close>

text \<open>\<open>is_returning c\<close> holds when the leftmost-innermost of \<open>c\<close> is \<^const>\<open>Restore\<close> or \<^const>\<open>Unwind\<close>:
  the shape of every returning-phase command --- normal fall-through or an explicit-return
  \<^const>\<open>Unwind\<close> spine, ordinary or \<open>Nested\<close>-wrapped.\<close>
fun is_returning :: "com \<Rightarrow> bool" where
  "is_returning Restore = True"
| "is_returning Unwind = True"
| "is_returning (Seq c1 c2) = is_returning c1"
| "is_returning _ = False"

text \<open>Pending continuations do not affect the returning classifier: it descends the leftmost spine
  to the active head, which \<^const>\<open>seq_after\<close> leaves untouched.\<close>
lemma is_returning_seq_after [simp]:
  "is_returning (seq_after c afters) = is_returning c"
  by (induction afters arbitrary: c) auto

subsection \<open>The call-redex source shape\<close>

text \<open>\<open>head_call c\<close> holds when the leftmost-innermost of \<open>c\<close> is a \<^const>\<open>Call\<close>: the shape of an
  active residual whose next \<^const>\<open>pstep\<close> fires the call.  Like \<^const>\<open>is_returning\<close> it descends the
  leftmost \<^const>\<open>Seq\<close> spine and so is insensitive to \<^const>\<open>seq_after\<close> wrapping and to whether the
  activation is a \<open>Base\<close> or a \<open>Nested\<close> inner.\<close>
fun head_call :: "com \<Rightarrow> bool" where
  "head_call (Call dst q actuals) = True"
| "head_call (Seq c1 c2) = head_call c1"
| "head_call _ = False"

lemma head_call_seq_after [simp]:
  "head_call (seq_after c afters) = head_call c"
  by (induction afters arbitrary: c) auto

lemma head_call_not_SKIP: "head_call c \<Longrightarrow> c \<noteq> SKIP"
  by (cases c) auto

lemma head_call_not_Unwind: "head_call c \<Longrightarrow> c \<noteq> Unwind"
  by (cases c) auto

text \<open>A call-headed residual is exactly a \<^const>\<open>Call\<close> at the bottom-left of a \<^const>\<open>seq_after\<close>
  spine; the spine is the pending continuations collected up the leftmost path.\<close>
lemma head_call_seq_after_form:
  "head_call c \<Longrightarrow> \<exists>dst q actuals afters. c = seq_after (Call dst q actuals) afters"
proof (induction c)
  case (Seq c1 c2)
  from Seq.prems have "head_call c1" by simp
  from Seq.IH(1)[OF this] obtain dst q actuals afters where
    "c1 = seq_after (Call dst q actuals) afters" by blast
  then have "Seq c1 c2 = seq_after (Call dst q actuals) (afters @ [c2])"
    by (simp add: seq_after_snoc)
  then show ?case by blast
qed auto

text \<open>The returning phase is never call-headed: an \<^const>\<open>unwinding\<close> spine heads with \<^const>\<open>Unwind\<close>
  and a \<^const>\<open>pop_ready\<close> body with \<^const>\<open>Restore\<close> or that spine --- neither is a \<^const>\<open>Call\<close>.\<close>
lemma unwinding_not_head_call: "unwinding u \<Longrightarrow> \<not> head_call u"
  by (induction u rule: unwinding.induct) auto

lemma pop_ready_not_head_call: "pop_ready w \<Longrightarrow> \<not> head_call w"
  by (cases w rule: pop_ready.cases) (auto simp: unwinding_not_head_call)

subsection \<open>The return-initiation source shape\<close>

text \<open>\<open>head_return c\<close> holds when the leftmost-innermost of \<open>c\<close> is a source \<^const>\<open>Return\<close>: the shape
  whose next \<^const>\<open>pstep\<close> initiates a return (\<^const>\<open>Return\<close> \<open>-->\<close> \<^const>\<open>Unwind\<close>).  Like the other head
  classifiers it descends the leftmost \<^const>\<open>Seq\<close> spine.\<close>
fun head_return :: "com \<Rightarrow> bool" where
  "head_return (Return e) = True"
| "head_return (Seq c1 c2) = head_return c1"
| "head_return _ = False"

lemma head_return_seq_after [simp]:
  "head_return (seq_after c afters) = head_return c"
  by (induction afters arbitrary: c) auto

lemma head_return_not_SKIP: "head_return c \<Longrightarrow> c \<noteq> SKIP"
  by (cases c) auto

lemma head_return_seq_after_form:
  "head_return c \<Longrightarrow> \<exists>e afters. c = seq_after (Return e) afters"
proof (induction c)
  case (Seq c1 c2)
  from Seq.prems have "head_return c1" by simp
  from Seq.IH(1)[OF this] obtain e afters where "c1 = seq_after (Return e) afters" by blast
  then have "Seq c1 c2 = seq_after (Return e) (afters @ [c2])" by (simp add: seq_after_snoc)
  then show ?case by blast
qed auto

lemma unwinding_not_head_return: "unwinding u \<Longrightarrow> \<not> head_return u"
  by (induction u rule: unwinding.induct) auto

lemma pop_ready_not_head_return: "pop_ready w \<Longrightarrow> \<not> head_return w"
  by (cases w rule: pop_ready.cases) (auto simp: unwinding_not_head_return)

subsection \<open>Source well-formedness: the base-activation return guard\<close>

text \<open>\<open>ret_guarded rok c\<close> is the deep source-only well-formedness check: an explicit \<^const>\<open>Return\<close>
  (or an in-flight \<^const>\<open>Unwind\<close>) is admissible only where \<open>rok\<close> holds --- inside a called
  activation.  Permission is \<^emph>\<open>granted by the activation tail\<close>: the right child \<^const>\<open>Restore\<close> of a
  \<^const>\<open>Seq\<close> marks a callee body, so its left child is checked with \<open>rok = True\<close>, whereas ordinary
  continuations inherit the ambient \<open>rok\<close>.  A bare \<^const>\<open>Restore\<close> (the transient tail after the
  callee body reduces to \<^const>\<open>SKIP\<close>) is always admissible.  Crucially this looks \<^emph>\<open>behind\<close>
  \<^const>\<open>Restore\<close> boundaries: a \<^const>\<open>Return\<close> hidden in a base-activation continuation is rejected,
  which a head-only check misses --- exactly the configuration a frame pop would later surface at
  the base.\<close>
fun ret_guarded :: "bool \<Rightarrow> com \<Rightarrow> bool" where
  "ret_guarded rok SKIP = True"
| "ret_guarded rok (Assign x a) = True"
| "ret_guarded rok (Seq c1 c2) =
     (if c2 = Restore then ret_guarded True c1
      else ret_guarded rok c1 \<and> ret_guarded rok c2)"
| "ret_guarded rok (If b c1 c2) = (ret_guarded rok c1 \<and> ret_guarded rok c2)"
| "ret_guarded rok (While b c) = ret_guarded rok c"
| "ret_guarded rok (Call dst p actuals) = True"
| "ret_guarded rok (Return e) = rok"
| "ret_guarded rok Restore = True"
| "ret_guarded rok Unwind = rok"

text \<open>A source command permits returns everywhere once \<open>rok\<close> holds (no \<^const>\<open>Restore\<close> tails and no
  bare \<^const>\<open>Unwind\<close> occur), so a compiled procedure body is admissible the instant it is entered.\<close>
lemma ret_guarded_True_source: "source_com c \<Longrightarrow> ret_guarded True c"
  by (induction c) (auto split: if_splits)

text \<open>At the base activation (\<open>rok = False\<close>) a source command with no return is not \<^const>\<open>head_return\<close>:
  the leftmost-innermost redex is never \<^const>\<open>Return\<close>.\<close>
lemma ret_guarded_False_source_not_head_return:
  "source_com c \<Longrightarrow> ret_guarded False c \<Longrightarrow> \<not> head_return c"
  by (induction c) (auto split: if_splits)

text \<open>The runtime invariant: the active command is \<^const>\<open>ret_guarded\<close> at the base activation (returns
  forbidden until a call opens one).  Unlike a head-only guard this is preserved by \<^const>\<open>pstep\<close>,
  because it already forbids the base-activation returns that a frame pop would expose.\<close>
definition source_wf :: "com \<times> store \<times> frame list \<Rightarrow> bool" where
  "source_wf cfg \<longleftrightarrow> (case cfg of (c, s, frs) \<Rightarrow> ret_guarded False c)"

text \<open>A well-formed root command establishes the runtime return guard because it contains
  neither runtime markers nor a source return.\<close>
lemma source_com_no_return_source_wf:
  assumes "source_com c" and "no_return c"
  shows "source_wf (c, s, frs)"
  using assms
  unfolding source_wf_def
  by (induction c) (auto split: if_splits)

text \<open>Base discharge: a \<^const>\<open>source_com\<close> active command of a \<open>source_wf\<close> configuration never heads with
  \<^const>\<open>Return\<close>.  In \<open>csim_step\<close> the \<open>Base\<close> case supplies \<^const>\<open>source_com\<close> (a located residual),
  so a return-headed \<open>Base\<close> is impossible and any return initiation runs with a nonempty frame.\<close>
lemma source_wf_source_not_head_return:
  "source_wf (c, s, frs) \<Longrightarrow> source_com c \<Longrightarrow> \<not> head_return c"
  by (auto simp: source_wf_def ret_guarded_False_source_not_head_return)

text \<open>\<^const>\<open>ret_guarded\<close> is preserved by every \<^const>\<open>pstep\<close> at any permission level: a rule induction
  where \<open>Call\<close> enters a source body (admissible by \<open>ret_guarded_True_source\<close>) and \<open>Seq2\<close> descends the
  active spine, re-permitting the callee side across a \<^const>\<open>Restore\<close> tail.  Hence \<open>source_wf\<close> holds
  of the successor configuration.\<close>
lemma ret_guarded_pstep:
  assumes bodies: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
      and step: "pstep source_global \<Pi> (c, s, frs) (c', s', frs')"
  shows "\<forall>rok. ret_guarded rok c \<longrightarrow> ret_guarded rok c'"
  using step
proof (induction "(c, s, frs)" "(c', s', frs')"
       arbitrary: c s frs c' s' frs' rule: pstep.induct)
  case Call
  then show ?case using bodies ret_guarded_True_source by auto
next
  case (Seq2 c1 s1 f1 c1' s1' f1' c2)
  have ih: "\<forall>rok. ret_guarded rok c1 \<longrightarrow> ret_guarded rok c1'" by (rule Seq2.hyps(2))
  show ?case using ih by (auto split: if_splits)
qed (auto split: if_splits)

lemma source_wf_pstep:
  assumes bodies: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
      and step: "pstep source_global \<Pi> (c, s, frs) (c', s', frs')"
      and wf: "source_wf (c, s, frs)"
  shows "source_wf (c', s', frs')"
  using ret_guarded_pstep[OF bodies step] wf by (simp add: source_wf_def)

text \<open>\<^const>\<open>unwinding\<close> of an \<^const>\<open>Unwind\<close> spine holds exactly when the pending continuations carry
  no \<^const>\<open>Restore\<close> marker --- true for the source continuations of a \<^const>\<open>control_at\<close> residual, so
  an explicit return's \<^const>\<open>Unwind\<close> is genuinely a \<^const>\<open>pop_ready\<close> frame-pop.\<close>
lemma unwinding_seq_after_Unwind:
  "(\<forall>a \<in> set afters. a \<noteq> Restore) \<Longrightarrow> unwinding (seq_after Unwind afters)"
  by (induction afters rule: rev_induct) (auto simp: seq_after_snoc)

subsection \<open>Source-step classification\<close>

text \<open>Every \<^const>\<open>pstep\<close> of a command that is neither call-, return-, nor returning-headed is an
  \<^const>\<open>intra_step\<close>: the four head classifiers exhaust the redex kinds a source step can fire.
  The \<open>Seq2\<close> case descends the leftmost spine (all four classifiers agree with their head).\<close>
text \<open>\<^const>\<open>intra_step\<close> ignores the frame stack: no intra rule inspects or changes frames, so a step
  holds under any frame stack.  This lets a \<open>Nested\<close> descent restrict an inner intra step to the
  inner frames even when they are empty.\<close>
lemma intra_step_any_frame:
  "intra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> intra_step \<Pi> (c, s, fr) (c', s', fr)"
  by (induction "(c, s, frs)" "(c', s', frs')" arbitrary: c s frs c' s' frs'
      rule: intra_step.induct) (auto intro: intra_step.intros)

lemma intra_step_frame_eq:
  "intra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> frs' = frs"
  by (induction "(c, s, frs)" "(c', s', frs')" arbitrary: c s frs c' s' frs'
      rule: intra_step.induct) auto

lemma intra_step_not_returning:
  "intra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> \<not> is_returning c"
  by (induction "(c, s, frs)" "(c', s', frs')" arbitrary: c s frs c' s' frs'
      rule: intra_step.induct) auto

lemma pstep_intra_classify:
  "pstep source_global \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> \<not> head_call c \<Longrightarrow> \<not> head_return c \<Longrightarrow> \<not> is_returning c \<Longrightarrow>
   intra_step \<Pi> (c, s, frs) (c', s', frs')"
proof (induction "(c, s, frs)" "(c', s', frs')"
       arbitrary: c s frs c' s' frs' rule: pstep.induct)
  case (Seq2 c1 s1 f1 c1' s1' f1' c2)
  from Seq2.prems have "\<not> head_call c1" "\<not> head_return c1" "\<not> is_returning c1" by auto
  from Seq2.hyps(2)[OF this] have ih: "intra_step \<Pi> (c1, s1, f1) (c1', s1', f1')" .
  from intra_step_frame_eq[OF ih] ih show ?case by (auto intro: intra_step.ISeq2)
qed (auto intro: intra_step.intros)

text \<open>Ordinary location never produces a returning command: \<^const>\<open>control_at\<close> locates only source
  residuals, never \<^const>\<open>Restore\<close> or \<^const>\<open>Unwind\<close> at any depth of leftmost nesting.\<close>
lemma control_at_not_returning:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> \<not> is_returning r"
  by (induction rule: control_at.induct) auto

text \<open>\<open>is_returning\<close> classifies the active head.  The \<open>unwinding\<close> and
  \<open>pop_ready\<close> predicates refine that class with the nested residual shape needed by frame-pop
  proofs; they deliberately overlap instead of forming a phase partition.\<close>
lemma unwinding_is_returning: "unwinding u \<Longrightarrow> is_returning u"
  by (induction u rule: unwinding.induct) auto

lemma pop_ready_is_returning: "pop_ready w \<Longrightarrow> is_returning w"
  by (cases w rule: pop_ready.cases) (auto simp: unwinding_is_returning)

subsection \<open>Stepping the frame-pop phase\<close>

text \<open>An \<^const>\<open>unwinding\<close> command only fires the \<open>UnwindDead\<close> rule: it drops the dead code it meets
  and reduces to another \<^const>\<open>unwinding\<close> command, leaving store and frames untouched (the dropped
  code never runs).\<close>
lemma pstep_unwinding:
  assumes "unwinding u" and "pstep source_global \<Pi> (u, s, frs) (u', s', frs')"
  shows "s' = s \<and> frs' = frs \<and> unwinding u'"
  using assms
proof (induction u arbitrary: u' s' frs')
  case (Seq u1 c2)
  from Seq.prems(1) have u1w: "unwinding u1" and c2R: "c2 \<noteq> Restore" by auto
  from Seq.prems(2) consider
      (dead) "u' = Unwind" "s' = s" "frs' = frs"
    | (step) c1' where "u' = Seq c1' c2" "pstep source_global \<Pi> (u1, s, frs) (c1', s', frs')"
    using c2R unwinding_not_SKIP[OF u1w] by (auto elim!: SeqSE)
  then show ?case
  proof cases
    case dead then show ?thesis by simp
  next
    case (step c1')
    from Seq.IH(1)[OF u1w step(2)] have "s' = s" "frs' = frs" "unwinding c1'" by simp_all
    then show ?thesis using step(1) c2R by simp
  qed
next
  case SKIP    from SKIP.prems(1)   show ?case by simp
next
  case Assign  from Assign.prems(1) show ?case by simp
next
  case If      from If.prems(1)     show ?case by simp
next
  case While   from While.prems(1)  show ?case by simp
next
  case Call    from Call.prems(1)   show ?case by simp
next
  case Return  from Return.prems(1) show ?case by simp
next
  case Restore from Restore.prems(1) show ?case by simp
next
  case Unwind
  from Unwind.prems(2) show ?case using pstep_Unwind_stuck by blast
qed

text \<open>One \<^const>\<open>pstep\<close> of a \<^const>\<open>pop_ready\<close> activation body (framed by exactly the caller frame)
  either pops that frame --- resuming at \<^const>\<open>SKIP\<close> with the combined store --- or propagates the
  unwind, staying \<^const>\<open>pop_ready\<close> with store and frame unchanged.\<close>
lemma pstep_pop_ready_head:
  assumes "pop_ready w" and "pstep source_global \<Pi> (w, s, Frame fr dst # frs) x"
  shows "x = (SKIP, combine_assign dst (s ret_var) (combine_states source_global fr s), frs)
       \<or> (\<exists>w'. x = (w', s, Frame fr dst # frs) \<and> pop_ready w')"
  using assms
proof (cases w rule: pop_ready.cases)
  case 1
  with assms(2) show ?thesis by (auto elim!: RestoreSE)
next
  case (2 u)
  hence uw: "unwinding u" using assms(1) by simp
  from assms(2) 2 show ?thesis
    using uw unwinding_not_SKIP[OF uw] by (auto elim!: SeqSE dest: pstep_unwinding[OF uw])
qed (use assms(1) in auto)

text \<open>A step of a \<^const>\<open>seq_after\<close> spine whose active head \<open>w\<close> is neither \<^const>\<open>SKIP\<close> nor
  \<^const>\<open>Unwind\<close> descends to a step of \<open>w\<close>, with the pending continuations \<open>afters\<close> riding along
  unchanged.  Proved by \<open>rev_induct\<close>: the outermost \<^const>\<open>Seq\<close> peels off (its left component, a
  \<^const>\<open>seq_after\<close> with active head \<open>w\<close>, is never \<^const>\<open>SKIP\<close> / \<^const>\<open>Unwind\<close>) and the induction
  hypothesis descends the remaining spine.\<close>
lemma pstep_seq_after_headD:
  assumes step: "pstep source_global \<Pi> (seq_after w afters, s, frs) src'"
      and wsk: "w \<noteq> SKIP" and wunw: "w \<noteq> Unwind"
  obtains h' s' fz where
    "src' = (seq_after h' afters, s', fz)"
    "pstep source_global \<Pi> (w, s, frs) (h', s', fz)"
proof -
  have "\<exists>h' s' fz. src' = (seq_after h' afters, s', fz) \<and> pstep source_global \<Pi> (w, s, frs) (h', s', fz)"
    using step
  proof (induction afters arbitrary: src' rule: rev_induct)
    case Nil
    then obtain h' s' fz where "src' = (h', s', fz)" "pstep source_global \<Pi> (w, s, frs) (h', s', fz)"
      by (cases src') auto
    then show ?case by auto
  next
    case (snoc a xs)
    from snoc.prems have "pstep source_global \<Pi> (Seq (seq_after w xs) a, s, frs) src'"
      by (simp add: seq_after_snoc)
    then obtain B' s' fz where
      A: "src' = (Seq B' a, s', fz)"
        and B: "pstep source_global \<Pi> (seq_after w xs, s, frs) (B', s', fz)"
      using wsk wunw by (auto elim!: SeqSE)
    from snoc.IH[OF B] obtain h' where
      "B' = seq_after h' xs" "pstep source_global \<Pi> (w, s, frs) (h', s', fz)" by auto
    then show ?case using A by (auto simp: seq_after_snoc)
  qed
  then show ?thesis using that by blast
qed

subsection \<open>Base return completion (frame pop or unwind propagation)\<close>

text \<open>
  One \<^const>\<open>pstep\<close> of a base returning activation \<^term>\<open>seq_after w afters\<close> (\<^term>\<open>pop_ready w\<close>, framed by
  the single caller frame, CFG at \<^term>\<open>FunctionResult p\<close>) is matched by a \<^const>\<open>star\<close> of \<^const>\<open>cstep\<close>:
    \<^enum> \<^emph>\<open>pop\<close>: the frame is popped, source resumes at \<^term>\<open>seq_after SKIP ao\<close> with the combined store,
      and the CFG performs exactly one return \<^const>\<open>cstep\<close> to \<open>cont\<close>, rebuilt as a \<open>Base\<close> activation;
    \<^enum> \<^emph>\<open>propagate\<close>: an \<^const>\<open>Unwind\<close> advances one dead-code layer, the source stays \<^term>\<open>pop_ready\<close>
      with the frame intact, and the CFG stays at \<^term>\<open>FunctionResult p\<close> (\<^emph>\<open>zero\<close> \<^const>\<open>cstep\<close>),
      rebuilt as a \<open>Returning\<close> activation.
  Both sides land on \<^const>\<open>combine_collect\<close> at the pop.
\<close>
lemma csim_returning_base_completion:
  assumes pr: "pop_ready w"
      and loc: "control_at \<Pi> pc c0c kc nc (seq_after SKIP afters) cont"
      and cacc: "compiled_at \<Pi> g pc c0c kc nc"      and pa: "proc_activation \<Pi> pc c0c"
      and step: "pstep source_global \<Pi> (seq_after w afters, callee, [Frame caller dst]) src'"
  shows "\<exists>cfg'. star (cstep source_global g) (FunctionResult p, callee, [(cont, dst, caller)]) cfg'
              \<and> csim \<Pi> g src' cfg'"
proof -
  have wsk: "w \<noteq> SKIP" using pr by (rule pop_ready_not_SKIP)
  have wunw: "w \<noteq> Unwind" using pr by (rule pop_ready_not_Unwind)
  obtain h' s' frs' where
    src': "src' = (seq_after h' afters, s', frs')"
      and hstep: "pstep source_global \<Pi> (w, callee, [Frame caller dst]) (h', s', frs')"
    by (rule pstep_seq_after_headD[OF step wsk wunw])
  let ?rs = "combine_collect source_global dst caller callee"
  from pstep_pop_ready_head[OF pr hstep] show ?thesis
  proof (rule disjE)
    assume "(h', s', frs') =
              (SKIP, combine_assign dst (callee ret_var) (combine_states source_global caller callee), [])"
    hence h': "h' = SKIP" "s' = ?rs" "frs' = []" by (auto simp: combine_collect_def)
    have "cstep source_global g (FunctionResult p, callee, [(cont, dst, caller)]) (cont, ?rs, [])"
      by (rule cstep.Return)
    moreover have "csim \<Pi> g (seq_after SKIP afters, ?rs, []) (cont, ?rs, [])"
      by (rule csim.Base[OF loc cacc pa])
    ultimately show ?thesis using src' h' by (auto intro: cstep_star_single)
  next
    assume "\<exists>w'. (h', s', frs') = (w', callee, [Frame caller dst]) \<and> pop_ready w'"
    then obtain w' where h': "h' = w'" "s' = callee" "frs' = [Frame caller dst]"
        and pr': "pop_ready w'" by auto
    have "csim \<Pi> g (seq_after w' afters, callee, [Frame caller dst])
                   (FunctionResult p, callee, [(cont, dst, caller)])"
      by (rule csim.Returning[OF pr' loc cacc pa])
    with src' h' show ?thesis by (auto intro: star.refl)
  qed
qed

text \<open>Frame restriction: a single \<^const>\<open>pstep\<close> touches only the head region of the frame stack,
  so a bottom segment \<open>extra\<close> rides along unchanged when the active part \<open>frs\<close> is non-empty.  This
  bridges the \<open>Nested\<close> snoc (the inner step threads all frames) to the induction hypothesis
  (stated on the inner frames alone).\<close>
lemma pstep_frame_restrict:
  "pstep source_global \<Pi> (c, s, fr) (c', s', frs') \<Longrightarrow> fr = frs @ extra \<Longrightarrow> frs \<noteq> [] \<Longrightarrow>
   \<exists>frs''. frs' = frs'' @ extra \<and> pstep source_global \<Pi> (c, s, frs) (c', s', frs'')"
proof (induction "(c, s, fr)" "(c', s', frs')"
       arbitrary: c s fr frs c' s' frs' rule: pstep.induct)
  case (Seq2 c1 s1 f1 c1' s1' f1' c2 frs)
  from Seq2.hyps(2)[OF Seq2.prems] obtain frs'' where
    ih: "f1' = frs'' @ extra" "pstep source_global \<Pi> (c1, s1, frs) (c1', s1', frs'')" by blast
  show ?case
    by (rule exI[of _ frs'']) (use ih in \<open>auto intro: pstep.Seq2\<close>)
next
  case (Call p decl actuals dst vals callee s1 frs0 frs)
  then show ?case by (auto intro: pstep.Call)
next
  case (RestoreStep s1 fr0 dst frs0 frs)
  from RestoreStep.prems obtain frs1 where "frs = Frame fr0 dst # frs1" "frs0 = frs1 @ extra"
    by (auto simp: Cons_eq_append_conv)
  then show ?case by (auto intro: pstep.RestoreStep)
next
  case (UnwindAct s1 fr0 dst frs0 frs)
  from UnwindAct.prems obtain frs1 where "frs = Frame fr0 dst # frs1" "frs0 = frs1 @ extra"
    by (auto simp: Cons_eq_append_conv)
  then show ?case by (auto intro: pstep.UnwindAct)
qed (auto intro: pstep.intros)

text \<open>The CFG dual: a single \<^const>\<open>cstep\<close> also touches only the head of the CFG stack, so an
  extra bottom segment rides along unchanged (no non-emptiness needed --- the return step already
  requires a non-empty stack).\<close>
lemma cstep_frame_extend:
  "cstep source_global g (u, s, stk) (u', s', stk') \<Longrightarrow> cstep source_global g (u, s, stk @ E) (u', s', stk' @ E)"
  by (erule cstep.cases) (auto intro: cstep.intros)

text \<open>A returning-phase config has non-empty stacks: the frame the return pops is present.\<close>
lemma csim_returning_frames_nonempty:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> is_returning c \<Longrightarrow> frs \<noteq> [] \<and> stk \<noteq> []"
  by (erule csim.cases) (auto dest: control_at_not_returning)

subsection \<open>Deep return completion through \<open>Nested\<close> wrappers\<close>

text \<open>\<^const>\<open>control_at\<close> never locates \<^const>\<open>Unwind\<close> (a runtime-only marker), so no \<open>csim\<close>
  activation is a bare \<^const>\<open>Unwind\<close>: \<open>Base\<close> is excluded by location, \<open>Nested\<close> heads with a
  \<^term>\<open>Seq inner Restore\<close>, and \<open>Returning\<close> carries a \<open>pop_ready\<close> command.\<close>
lemma control_at_not_unwind:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r \<noteq> Unwind"
  by (induction rule: control_at.induct) auto

lemma csim_not_unwind:
  "csim \<Pi> g (Unwind, s, frs) cfg' \<Longrightarrow> False"
  by (erule csim.cases) (auto dest: control_at_not_unwind pop_ready_not_Unwind)

text \<open>The CFG dual for runs: a whole \<^const>\<open>star\<close> of \<^const>\<open>cstep\<close> rides an extra bottom stack segment.\<close>
lemma cstep_star_frame_extend:
  assumes "star (cstep source_global g) c c'"
  shows "star (cstep source_global g) (fst c, fst (snd c), snd (snd c) @ E)
                        (fst c', fst (snd c'), snd (snd c') @ E)"
  using assms
proof (induction rule: star.induct)
  case (refl a) show ?case by simp
next
  case (step a b c)
  obtain ua sa stka where a: "a = (ua, sa, stka)" by (cases a)
  obtain ub sb stkb where b: "b = (ub, sb, stkb)" by (cases b)
  from step.hyps(1) a b have "cstep source_global g (ua, sa, stka) (ub, sb, stkb)" by simp
  hence "cstep source_global g (ua, sa, stka @ E) (ub, sb, stkb @ E)" by (rule cstep_frame_extend)
  with step.IH a b show ?case by (auto intro: star.step)
qed


text \<open>Stepping a returning \<open>Nested\<close> command descends the outer \<^const>\<open>Seq\<close> spine to the callee
  residual: a csim'd \<open>inner\<close> is never \<^const>\<open>SKIP\<close> (it is returning) nor \<^const>\<open>Unwind\<close>, so the
  innermost sequencing fires \<open>Seq2\<close> and the pending continuations \<open>afters\<close> and the trailing
  \<^const>\<open>Restore\<close> ride along unchanged.  Proved by \<open>rev_induct\<close> on \<open>afters\<close>: the outermost
  \<^const>\<open>Seq\<close> peels off (its left component, a \<^const>\<open>seq_after\<close>, is never \<^const>\<open>SKIP\<close> / \<^const>\<open>Unwind\<close>)
  and the induction hypothesis descends the remaining spine.\<close>
lemma pstep_seq_after_seq_restore:
  assumes step: "pstep source_global \<Pi> (seq_after (Seq inner Restore) afters, s, frs) src'"
      and nsk: "inner \<noteq> SKIP" and nunw: "inner \<noteq> Unwind"
  obtains inner' s' fz where
    "src' = (seq_after (Seq inner' Restore) afters, s', fz)"
    "pstep source_global \<Pi> (inner, s, frs) (inner', s', fz)"
proof -
  have "\<exists>inner' s' fz. src' = (seq_after (Seq inner' Restore) afters, s', fz)
          \<and> pstep source_global \<Pi> (inner, s, frs) (inner', s', fz)"
    using step
  proof (induction afters arbitrary: src' rule: rev_induct)
    case Nil
    from Nil.prems have "pstep source_global \<Pi> (Seq inner Restore, s, frs) src'" by simp
    then obtain inner' s' fz where
      "src' = (Seq inner' Restore, s', fz)" "pstep source_global \<Pi> (inner, s, frs) (inner', s', fz)"
      using nsk nunw by (auto elim!: SeqSE)
    then show ?case by auto
  next
    case (snoc a xs)
    from snoc.prems have "pstep source_global \<Pi> (Seq (seq_after (Seq inner Restore) xs) a, s, frs) src'"
      by (simp add: seq_after_snoc)
    then obtain B' s' fz where
      A: "src' = (Seq B' a, s', fz)"
        and B: "pstep source_global \<Pi> (seq_after (Seq inner Restore) xs, s, frs) (B', s', fz)"
      by (auto elim!: SeqSE)
    from snoc.IH[OF B] obtain inner' where
      "B' = seq_after (Seq inner' Restore) xs" "pstep source_global \<Pi> (inner, s, frs) (inner', s', fz)"
      by auto
    then show ?case using A by (auto simp: seq_after_snoc)
  qed
  then show ?thesis using that by blast
qed

text \<open>
  Return completion propagates through any number of unchanged outer \<open>Nested\<close> wrappers.  The
  source step descends the outer \<open>Seq2\<close> spine to the innermost returning activation, which either
  pops its frame (one \<^const>\<open>cstep\<close> return) or advances one unwind layer (zero \<^const>\<open>cstep\<close>, the CFG
  waiting at \<^term>\<open>FunctionResult\<close>); the outer wrappers are rebuilt unchanged.  Proved by induction on
  \<open>csim\<close>: \<open>Base\<close> is vacuous (\<open>control_at_not_returning\<close>), \<open>Returning\<close> is
  \<open>csim_returning_base_completion\<close>, and \<open>Nested\<close> descends via \<open>pstep_seq_after_seq_restore\<close> /
  \<open>pstep_frame_restrict\<close> / \<open>cstep_star_frame_extend\<close> and the IH.
\<close>
lemma csim_returning_completion:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> is_returning c \<Longrightarrow> pstep source_global \<Pi> (c, s, frs) src' \<Longrightarrow>
   \<exists>cfg'. star (cstep source_global g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
proof (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c s frs v t stk src' rule: csim.induct)
  case (Base p c0 kk n cc vv ss)
  from control_at_not_returning[OF Base.hyps(1)] Base.prems(1) show ?case by simp
next
  case (Returning w pc c0c kc nc ao cont callee caller dst p)
  from csim_returning_base_completion[OF Returning.hyps(1) Returning.hyps(2) Returning.hyps(3)
                                         Returning.hyps(4) Returning.prems(2)]
  show ?case .
next
  case (Nested inner s0 frs0 v0 stk0 pc c0c kc nc afters cont caller dst)
  have retinner: "is_returning inner" using Nested.prems(1) by simp
  have nsk: "inner \<noteq> SKIP" using retinner by auto
  have nunw: "inner \<noteq> Unwind"
  proof (rule notI)
    assume "inner = Unwind"
    with Nested.hyps(1) show False by (blast dest: csim_not_unwind)
  qed
  have frsne: "frs0 \<noteq> []"
    using csim_returning_frames_nonempty[OF Nested.hyps(1) retinner] by simp
  obtain inner' s' fz where
    src': "src' = (seq_after (Seq inner' Restore) afters, s', fz)"
      and stepin: "pstep source_global \<Pi> (inner, s0, frs0 @ [Frame caller dst]) (inner', s', fz)"
    by (rule pstep_seq_after_seq_restore[OF Nested.prems(2) nsk nunw])
  from pstep_frame_restrict[OF stepin refl frsne] obtain fz' where
    fz: "fz = fz' @ [Frame caller dst]"
      and stepin': "pstep source_global \<Pi> (inner, s0, frs0) (inner', s', fz')" by blast
  from Nested.hyps(2)[OF retinner stepin'] obtain v' t' stk' where
    cstepin: "star (cstep source_global g) (v0, s0, stk0) (v', t', stk')"
      and csimin: "csim \<Pi> g (inner', s', fz') (v', t', stk')" by auto
  have teq: "t' = s'" using csim_store_eq[OF csimin] by simp
  have cstepN: "star (cstep source_global g) (v0, s0, stk0 @ [(cont, dst, caller)])
                               (v', s', stk' @ [(cont, dst, caller)])"
    using cstep_star_frame_extend[OF cstepin, of "[(cont, dst, caller)]"] teq by simp
  have "csim \<Pi> g (seq_after (Seq inner' Restore) afters, s', fz' @ [Frame caller dst])
                 (v', s', stk' @ [(cont, dst, caller)])"
    by (rule csim.Nested[OF csimin[unfolded teq] Nested.hyps(3) Nested.hyps(4) Nested.hyps(5)])
  then have "csim \<Pi> g src' (v', s', stk' @ [(cont, dst, caller)])"
    by (simp add: src' fz)
  with cstepN show ?case by blast
qed

section \<open>Compiler well-formedness of the target graph\<close>

text \<open>
  \<open>procs_compiled \<Pi> g\<close> is the static compiler-correctness certificate for the target graph:
  every declared procedure's body is compiled into \<open>g\<close>, with its intra/call edges included and
  the entry/exit wiring present (\<^term>\<open>FunctionEntry p\<close> \<open>--EA_Nop-->\<close> body entry, and body exit
  \<open>--EA_Ret-->\<close> \<^term>\<open>FunctionResult p\<close>).  It is kept \<^emph>\<open>separate\<close> from \<open>csim\<close> (which describes only
  the dynamic configuration correspondence): the returning phase needs none of it, while the
  ordinary and call phases receive it as a single static premise and read off the concrete facts
  through the projection lemmas below.
\<close>

definition procs_compiled :: "proc_table \<Rightarrow> cfg \<Rightarrow> bool" where
  "procs_compiled \<Pi> g \<longleftrightarrow>
     (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow>
        (\<exists>k n n' en E K.
           compile \<Pi> p (body decl) k n = (n', en, E, K)
         \<and> E \<subseteq> intra g \<and> K \<subseteq> calls g
         \<and> (FunctionEntry p, EA_Nop, en) \<in> intra g
         \<and> (falls_through (body decl) \<longrightarrow>
              (k, EA_Ret None p, FunctionResult p) \<in> intra g)
         \<and> source_com (body decl)))"

text \<open>Projection: the compiled fragment of a declared procedure's body, with its edge inclusions
  and entry/epilogue wiring, all read off a single \<^const>\<open>procs_compiled\<close> assumption.  The
  continuation \<open>k\<close> is the procedure's epilogue node, which is where the fall-through return edge
  starts when the body can reach it.\<close>
lemma procs_compiled_proc:
  assumes "procs_compiled \<Pi> g" and "\<Pi> p = Some decl"
  obtains k n n' en E K where
    "compile \<Pi> p (body decl) k n = (n', en, E, K)"
    "E \<subseteq> intra g" "K \<subseteq> calls g"
    "(FunctionEntry p, EA_Nop, en) \<in> intra g"
    "falls_through (body decl) \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g"
    "source_com (body decl)"
  using assms unfolding procs_compiled_def by blast


text \<open>A declared procedure's body is a source command.\<close>
lemma procs_compiled_source_com:
  assumes "procs_compiled \<Pi> g" and "\<Pi> p = Some decl"
  shows "source_com (body decl)"
  using assms by (blast elim: procs_compiled_proc)



section \<open>Call preservation\<close>

text \<open>
  A source \<^const>\<open>Call\<close> in head position of the active (base) residual is simulated by a
  \<^const>\<open>star\<close> of two \<^const>\<open>cstep\<close>s --- the call edge to \<^term>\<open>FunctionEntry q\<close> and the entry
  \<^term>\<open>EA_Nop\<close> to the callee body's entry --- and adds exactly one \<open>Nested\<close> layer: the callee body
  becomes a fresh \<open>Base\<close> activation (located at its entry by \<open>control_at_initial\<close>, a real
  procedure by \<^const>\<open>proc_activation\<close>), and the caller resumes at its located post-call residual
  \<^term>\<open>seq_after SKIP afters\<close> --- bare \<^const>\<open>SKIP\<close> for a tail call (\<^term>\<open>afters = []\<close>), a nonempty
  \<^const>\<open>seq_after\<close> spine when pending continuations follow the call.  Everything the callee needs
  (edge inclusions, entry wiring, body source-ness) comes from the single \<^const>\<open>procs_compiled\<close>
  certificate.  This is the low-level helper: the caller's post-call location \<^term>\<open>seq_after SKIP afters\<close>
  is supplied as a hypothesis; \<open>csim_call_preservation\<close> derives it from the located call residual.
\<close>


lemma csim_call_base:
  assumes pc: "procs_compiled \<Pi> g"
      and loc: "control_at \<Pi> p c0 kk n (seq_after (Call dst q actuals) afters) v"
      and cacc: "compiled_at \<Pi> g p c0 kk n"
      and pa: "proc_activation \<Pi> p c0"
      and decl: "\<Pi> q = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct: "distinct (formals decl)"
  shows "\<exists>cfg'. star (cstep source_global g) (v, s, [])  cfg'
              \<and> csim \<Pi> g (seq_after (Seq (body decl) Restore) afters,
                          bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals)
                            (enter_state source_global s),
                          [Frame s dst]) cfg'"
proof -
  let ?callee =
    "bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state source_global s)"
  from cacc obtain n' en E K where comp: "compile \<Pi> p c0 kk n = (n', en, E, K)"
      and Ksub: "K \<subseteq> calls g" by (auto simp: compiled_at_def)
  from control_at_seq_after_call_edge[OF loc refl comp] obtain j w where
    vk: "v = Statement j"
    and edgeK: "(Statement j, CallEdge dst (case \<Pi> q of Some d \<Rightarrow> formals d | None \<Rightarrow> []) actuals,
                 FunctionEntry q, w) \<in> K"
    and callerSKIP: "control_at \<Pi> p c0 kk n (seq_after SKIP afters) w" by blast
  have edge: "(Statement j, CallEdge dst (formals decl) actuals, FunctionEntry q, w)
                \<in> calls g" using edgeK Ksub by (auto simp: decl)
  have cstep1: "cstep source_global g (Statement j, s, [])
           (FunctionEntry q, call_enter source_global (CallEdge dst (formals decl) actuals) s,
            [(w, dst, s)])" by (rule cstep.Call[OF edge])
  have ce: "call_enter source_global (CallEdge dst (formals decl) actuals) s = ?callee"
    by (rule call_enter_eq_source_call_store)
  obtain kq m m' en_q E_q K_q where
    cbody: "compile \<Pi> q (body decl) kq m = (m', en_q, E_q, K_q)"
      and E_qsub: "E_q \<subseteq> intra g" and K_qsub: "K_q \<subseteq> calls g"
      and entry: "(FunctionEntry q, EA_Nop, en_q) \<in> intra g"
      and exitq: "falls_through (body decl) \<longrightarrow>
                    (kq, EA_Ret None q, FunctionResult q) \<in> intra g"
      and srcbody: "source_com (body decl)"
    by (rule procs_compiled_proc[OF pc decl])
  have caccq: "compiled_at \<Pi> g q (body decl) kq m"
    by (rule compiled_atI[OF cbody E_qsub K_qsub exitq])

  have cstep2: "cstep source_global g (FunctionEntry q, ?callee, [(w, dst, s)])
                        (en_q, ?callee, [(w, dst, s)])"
    using cstep_nop[OF entry] .
  have star: "star (cstep source_global g) (v, s, []) (en_q, ?callee, [(w, dst, s)])"
    using cstep1[unfolded ce] cstep2 vk by (simp add: cstep_star_single star.step)
  have paq: "proc_activation \<Pi> q (body decl)"
    using decl unfolding proc_activation_def by blast
  have baseCallee: "csim \<Pi> g (body decl, ?callee, []) (en_q, ?callee, [])"
    by (rule csim.Base[OF control_at_initial[OF srcbody,
          of \<Pi> q kq m, folded compile_entry_node[OF cbody]] caccq paq])
  have "csim \<Pi> g (seq_after (Seq (body decl) Restore) afters, ?callee, [] @ [Frame s dst])
                 (en_q, ?callee, [] @ [(w, dst, s)])"
    by (rule csim.Nested[OF baseCallee callerSKIP cacc pa])
  then have "csim \<Pi> g (seq_after (Seq (body decl) Restore) afters, ?callee, [Frame s dst])
                      (en_q, ?callee, [(w, dst, s)])" by simp
  with star show ?thesis by blast
qed

text \<open>Call-specific frame restriction: a call-headed step only \<^emph>\<open>pushes\<close> a frame, so an extra
  bottom segment rides along even when the active part is empty (unlike the general
  \<open>pstep_frame_restrict\<close>, which needs a non-empty active stack to exclude a pop).  The
  pop cases (\<open>RestoreStep\<close> / \<open>UnwindAct\<close> / \<open>ISeq1\<close>) are impossible because a call-headed command
  never heads with \<^const>\<open>SKIP\<close> / \<^const>\<open>Restore\<close> / \<^const>\<open>Unwind\<close>.\<close>
lemma pstep_call_frame_restrict:
  "pstep source_global \<Pi> (c, s, fr) (c', s', frs') \<Longrightarrow> head_call c \<Longrightarrow> fr = frs @ extra \<Longrightarrow>
   \<exists>frs''. frs' = frs'' @ extra \<and> pstep source_global \<Pi> (c, s, frs) (c', s', frs'')"
proof (induction "(c, s, fr)" "(c', s', frs')"
       arbitrary: c s fr frs c' s' frs' rule: pstep.induct)
  case (Seq2 c1 s1 f1 c1' s1' f1' c2 frs)
  from Seq2.prems(1) have "head_call c1" by simp
  from Seq2.hyps(2)[OF this Seq2.prems(2)] obtain frs'' where
    ih: "f1' = frs'' @ extra" "pstep source_global \<Pi> (c1, s1, frs) (c1', s1', frs'')" by blast
  show ?case by (rule exI[of _ frs'']) (use ih in \<open>auto intro: pstep.Seq2\<close>)
next
  case (Call p decl actuals dst vals callee s1 frs0 frs)
  then show ?case by (auto intro: pstep.Call)
qed (auto intro: pstep.intros)

section \<open>Full call preservation\<close>

text \<open>
  A source \<^const>\<open>Call\<close> redex in the active layer of any \<open>csim\<close> configuration is simulated by a
  \<^const>\<open>star\<close> of \<^const>\<open>cstep\<close>s ending in a \<open>csim\<close> configuration --- the deep lift of
  \<open>csim_call_base\<close> through any number of outer \<open>Nested\<close> wrappers.  The active layer is either a
  \<open>Base\<close> (the call fires directly, adding one \<open>Nested\<close> callee layer via \<open>csim_call_base\<close>) or the inner
  activation of a \<open>Nested\<close> stack (the call is deeper; the outer wrappers ride along and the induction
  hypothesis descends).  The \<open>Returning\<close> case is vacuous: a \<^const>\<open>pop_ready\<close> body is never
  call-headed.  Mirrors \<open>csim_returning_completion\<close>, with \<^const>\<open>head_call\<close> in place of
  \<^const>\<open>is_returning\<close> and \<open>csim_call_base\<close> in place of \<open>csim_returning_base_completion\<close>.
\<close>
theorem csim_call_completion:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> procs_compiled \<Pi> g \<Longrightarrow> head_call c \<Longrightarrow>
   pstep source_global \<Pi> (c, s, frs) src' \<Longrightarrow>
   \<exists>cfg'. star (cstep source_global g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
proof (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c s frs v t stk src' rule: csim.induct)
  case (Base p c0 kk n cc vv ss)
  from head_call_seq_after_form[OF Base.prems(2)] obtain dst q actuals afters where
    ceq: "cc = seq_after (Call dst q actuals) afters" by blast
  have step: "pstep source_global \<Pi> (seq_after (Call dst q actuals) afters, ss, []) src'"
    using Base.prems(3) ceq by simp
  have w1: "Call dst q actuals \<noteq> SKIP" by simp
  have w2: "Call dst q actuals \<noteq> Unwind" by simp
  obtain h' s' fz where
    src': "src' = (seq_after h' afters, s', fz)"
      and pcall: "pstep source_global \<Pi> (Call dst q actuals, ss, []) (h', s', fz)"
    by (rule pstep_seq_after_headD[OF step w1 w2])
  from pcall obtain decl where
    qdecl: "\<Pi> q = Some decl" and ar: "length actuals = length (formals decl)"
      and di: "distinct (formals decl)"
      and heq: "h' = Seq (body decl) Restore"
      and seq: "s' = bind_formals (formals decl) (map (\<lambda>e. aval e ss) actuals)
                        (enter_state source_global ss)"
      and fzeq: "fz = [Frame ss dst]"
    by (auto elim!: CallSE)
  have loc': "control_at \<Pi> p c0 kk n (seq_after (Call dst q actuals) afters) vv"
    using Base.hyps(1) ceq by simp
  from csim_call_base[OF Base.prems(1) loc' Base.hyps(2) Base.hyps(3) qdecl ar di, where s = ss]
  obtain cfg' where
    cstar: "star (cstep source_global g) (vv, ss, []) cfg'"
      and csimr: "csim \<Pi> g (seq_after (Seq (body decl) Restore) afters,
               bind_formals (formals decl) (map (\<lambda>e. aval e ss) actuals)
                 (enter_state source_global ss),
               [Frame ss dst]) cfg'" by blast
  from csimr have "csim \<Pi> g src' cfg'" by (simp add: src' heq seq fzeq)
  with cstar show ?case by blast
next
  case (Returning w pc c0c kc nc afters cont callee caller dst p)
  from Returning.prems(2) have "head_call w" by simp
  with pop_ready_not_head_call[OF Returning.hyps(1)] show ?case by simp
next
  case (Nested inner s0 frs0 v0 stk0 pc c0c kc nc afters cont caller dst)
  have headinner: "head_call inner" using Nested.prems(2) by simp
  have nsk: "inner \<noteq> SKIP" using headinner by (rule head_call_not_SKIP)
  have nunw: "inner \<noteq> Unwind" using headinner by (rule head_call_not_Unwind)
  obtain inner' s' fz where
    src': "src' = (seq_after (Seq inner' Restore) afters, s', fz)"
      and stepin: "pstep source_global \<Pi> (inner, s0, frs0 @ [Frame caller dst]) (inner', s', fz)"
    by (rule pstep_seq_after_seq_restore[OF Nested.prems(3) nsk nunw])
  from pstep_call_frame_restrict[OF stepin headinner refl] obtain fz' where
    fz: "fz = fz' @ [Frame caller dst]"
      and stepin': "pstep source_global \<Pi> (inner, s0, frs0) (inner', s', fz')" by blast
  from Nested.hyps(2)[OF Nested.prems(1) headinner stepin'] obtain v' t' stk' where
    cstepin: "star (cstep source_global g) (v0, s0, stk0) (v', t', stk')"
      and csimin: "csim \<Pi> g (inner', s', fz') (v', t', stk')" by auto
  have teq: "t' = s'" using csim_store_eq[OF csimin] by simp
  have cstepN: "star (cstep source_global g) (v0, s0, stk0 @ [(cont, dst, caller)])
                               (v', s', stk' @ [(cont, dst, caller)])"
    using cstep_star_frame_extend[OF cstepin, of "[(cont, dst, caller)]"] teq by simp
  have "csim \<Pi> g (seq_after (Seq inner' Restore) afters, s', fz' @ [Frame caller dst])
                 (v', s', stk' @ [(cont, dst, caller)])"
    by (rule csim.Nested[OF csimin[unfolded teq] Nested.hyps(3) Nested.hyps(4) Nested.hyps(5)])
  then have "csim \<Pi> g src' (v', s', stk' @ [(cont, dst, caller)])"
    by (simp add: src' fz)
  with cstepN show ?case by blast
qed

section \<open>Intra-procedural preservation and callee fall-through\<close>

text \<open>An \<^const>\<open>intra_step\<close> of a \<open>Nested\<close> activation's outer command descends the \<^const>\<open>seq_after\<close>
  spine to its \<^term>\<open>Seq inner Restore\<close> core: either the callee has completed (\<open>inner = SKIP\<close>, the
  \<open>ISeq1\<close> fall-through exposing \<^const>\<open>Restore\<close>) or the callee takes one more intra step (all with the
  frame stack unchanged, since intra steps ignore frames).\<close>
lemma intra_step_seq_after_seq_restore:
  "intra_step \<Pi> (seq_after (Seq inner Restore) afters, s, frs) src' \<Longrightarrow>
   (inner = SKIP \<and> src' = (seq_after Restore afters, s, frs))
   \<or> (\<exists>inner' s'. src' = (seq_after (Seq inner' Restore) afters, s', frs)
        \<and> intra_step \<Pi> (inner, s, frs) (inner', s', frs))"
proof (induction afters arbitrary: src' rule: rev_induct)
  case Nil
  obtain c' s' frs' where sc: "src' = (c', s', frs')" by (cases src')
  from Nil.prems sc have "intra_step \<Pi> (Seq inner Restore, s, frs) (c', s', frs')" by simp
  from intra_Seq_cases[OF this] show ?case by (auto simp: sc)
next
  case (snoc a xs)
  obtain c' s' frs' where sc: "src' = (c', s', frs')" by (cases src')
  from snoc.prems sc
  have "intra_step \<Pi> (Seq (seq_after (Seq inner Restore) xs) a, s, frs) (c', s', frs')"
    by (simp add: seq_after_snoc)
  from intra_Seq_cases[OF this] obtain B' where
    A: "c' = Seq B' a" "frs' = frs"
      and B: "intra_step \<Pi> (seq_after (Seq inner Restore) xs, s, frs) (B', s', frs)"
    by auto
  from snoc.IH[OF B] show ?case
  proof (rule disjE)
    assume "inner = SKIP \<and> (B', s', frs) = (seq_after Restore xs, s, frs)"
    then show ?case using A sc by (auto simp: seq_after_snoc)
  next
    assume "\<exists>inner' s''. (B', s', frs) = (seq_after (Seq inner' Restore) xs, s'', frs)
              \<and> intra_step \<Pi> (inner, s, frs) (inner', s'', frs)"
    then show ?case using A sc by (auto simp: seq_after_snoc)
  qed
qed

text \<open>
  An \<^const>\<open>intra_step\<close> of any \<open>csim\<close> configuration is simulated by a \<^const>\<open>star\<close> of \<^const>\<open>cstep\<close>s
  ending in a \<open>csim\<close> configuration.  Three shapes:
    \<^enum> a \<open>Base\<close> activation makes an ordinary intra step (\<open>intra_step_simulation\<close> relocates it);
    \<^enum> a \<open>Nested\<close> callee makes an ordinary intra step (descend, rebuild the wrapper);
    \<^enum> a \<open>Nested\<close> callee \<^emph>\<open>completes\<close> (\<open>inner = SKIP\<close>): the \<open>ISeq1\<close> fall-through exposes \<^const>\<open>Restore\<close>,
      the CFG runs the completed callee to its exit (\<open>control_at_skip_to_exit\<close>) and takes the
      \<^term>\<open>EA_Ret None p\<close> edge into \<^term>\<open>FunctionResult p\<close> (\<open>compiled_at_exit\<close>), landing in a
      \<open>Returning\<close> activation.
  The \<open>Returning\<close> case is vacuous: an intra step never fires on a \<^const>\<open>pop_ready\<close> source.
\<close>
theorem csim_intra_completion:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> procs_compiled \<Pi> g \<Longrightarrow>
   intra_step \<Pi> (c, s, frs) src' \<Longrightarrow>
   \<exists>cfg'. star (cstep source_global g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
proof (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c s frs v t stk src' rule: csim.induct)
  case (Base p c0 kk n cc vv ss)
  obtain c' s' frs' where sc: "src' = (c', s', frs')" by (cases src')
  from Base.prems(2) sc have istep: "intra_step \<Pi> (cc, ss, []) (c', s', frs')" by simp
  from Base.hyps(3) obtain decl where pdecl: "\<Pi> p = Some decl" "c0 = body decl"
    by (rule proc_activationD)
  have srcbody: "source_com c0"
    using procs_compiled_source_com[OF Base.prems(1) \<open>\<Pi> p = Some decl\<close>] \<open>c0 = body decl\<close> by simp
  from Base.hyps(2) obtain n' en E K where comp: "compile \<Pi> p c0 kk n = (n', en, E, K)"
      and Esub: "E \<subseteq> intra g" by (auto simp: compiled_at_def)
  from intra_step_simulation[OF Base.hyps(1) istep comp Esub srcbody, where stk = "[]"]
  obtain v' where feq: "frs' = []" and loc': "control_at \<Pi> p c0 kk n c' v'"
      and cstar: "star (cstep source_global g) (vv, ss, []) (v', s', [])" by blast
  have "csim \<Pi> g (c', s', []) (v', s', [])" by (rule csim.Base[OF loc' Base.hyps(2) Base.hyps(3)])
  with cstar show ?case using sc feq by auto
next
  case (Returning w pc c0c kc nc afters cont callee caller dst p)
  from Returning.prems(2) have "\<not> is_returning (seq_after w afters)"
    by (cases src') (auto dest: intra_step_not_returning)
  with Returning.hyps(1) show ?case by (simp add: pop_ready_is_returning)
next
  case (Nested inner s0 frs0 v0 stk0 pc c0c kc nc afters cont caller dst)
  from Nested.prems(2)
  have "intra_step \<Pi> (seq_after (Seq inner Restore) afters, s0, frs0 @ [Frame caller dst]) src'" .
  from intra_step_seq_after_seq_restore[OF this] show ?case
  proof (rule disjE)
    assume fall: "inner = SKIP \<and> src' = (seq_after Restore afters, s0, frs0 @ [Frame caller dst])"
    then have innerSKIP: "inner = SKIP" and src': "src' = (seq_after Restore afters, s0, frs0 @ [Frame caller dst])"
      by auto
    have baseInner: "csim \<Pi> g (SKIP, s0, frs0) (v0, s0, stk0)" using Nested.hyps(1) innerSKIP by simp
    from baseInner obtain pin c0in kin nin where
      ctrl: "control_at \<Pi> pin c0in kin nin SKIP v0" and cacc: "compiled_at \<Pi> g pin c0in kin nin"
        and frs0nil: "frs0 = []" and stk0nil: "stk0 = []"
    proof (cases rule: csim.cases)
      case (Base p2 c02 k2 n2) with that show ?thesis by auto
    qed simp_all
    have ftin: "falls_through c0in" by (rule control_at_SKIP_imp_falls_through[OF ctrl])
    from cacc obtain n' en E K where comp: "compile \<Pi> pin c0in kin nin = (n', en, E, K)"
      and Esub: "E \<subseteq> intra g"
      and exitedge: "(kin, EA_Ret None pin, FunctionResult pin) \<in> intra g"
      using ftin by (auto simp: compiled_at_def)

    have star1: "star (cstep source_global g) (v0, s0, [(cont, dst, caller)]) (kin, s0, [(cont, dst, caller)])"
      by (rule control_at_skip_to_exit[OF ctrl refl comp Esub])
    have "cstep source_global g (kin, s0, [(cont, dst, caller)]) (FunctionResult pin, s0, [(cont, dst, caller)])"
      using cstep.Intra[OF exitedge edge_step_EA_Ret_ret_store] by simp
    with star1 have star: "star (cstep source_global g) (v0, s0, [(cont, dst, caller)])                             (FunctionResult pin, s0, [(cont, dst, caller)])"
      by (meson star_trans cstep_star_single)
    have "csim \<Pi> g (seq_after Restore afters, s0, [Frame caller dst])
                   (FunctionResult pin, s0, [(cont, dst, caller)])"
      by (rule csim.Returning[OF _ Nested.hyps(3) Nested.hyps(4) Nested.hyps(5)]) simp
    then have "csim \<Pi> g src' (FunctionResult pin, s0, [(cont, dst, caller)])"
      using src' frs0nil by simp
    with star show ?case using stk0nil by auto
  next
    assume "\<exists>inner' s'. src' = (seq_after (Seq inner' Restore) afters, s', frs0 @ [Frame caller dst])
              \<and> intra_step \<Pi> (inner, s0, frs0 @ [Frame caller dst]) (inner', s', frs0 @ [Frame caller dst])"
    then obtain inner' s' where
      src': "src' = (seq_after (Seq inner' Restore) afters, s', frs0 @ [Frame caller dst])"
        and stepin: "intra_step \<Pi> (inner, s0, frs0 @ [Frame caller dst]) (inner', s', frs0 @ [Frame caller dst])"
      by blast
    from intra_step_any_frame[OF stepin] have stepin': "intra_step \<Pi> (inner, s0, frs0) (inner', s', frs0)" .
    from Nested.hyps(2)[OF Nested.prems(1) stepin'] obtain v' t' stk' where
      cstepin: "star (cstep source_global g) (v0, s0, stk0) (v', t', stk')"
        and csimin: "csim \<Pi> g (inner', s', frs0) (v', t', stk')" by auto
    have teq: "t' = s'" using csim_store_eq[OF csimin] by simp
    have cstepN: "star (cstep source_global g) (v0, s0, stk0 @ [(cont, dst, caller)])
                                 (v', s', stk' @ [(cont, dst, caller)])"
      using cstep_star_frame_extend[OF cstepin, of "[(cont, dst, caller)]"] teq by simp
    have "csim \<Pi> g (seq_after (Seq inner' Restore) afters, s', frs0 @ [Frame caller dst])
                   (v', s', stk' @ [(cont, dst, caller)])"
      by (rule csim.Nested[OF csimin[unfolded teq] Nested.hyps(3) Nested.hyps(4) Nested.hyps(5)])
    then have "csim \<Pi> g src' (v', s', stk' @ [(cont, dst, caller)])" by (simp add: src')
    with cstepN show ?case by blast
  qed
qed

section \<open>Return initiation\<close>

text \<open>
  A source \<^const>\<open>Return\<close> in head position (\<^const>\<open>head_return\<close>) fires \<open>Return e --> Unwind\<close>, turning
  the innermost callee activation into its returning phase.  On the CFG side the callee moves in one
  \<open>Intra\<close> step along the \<^term>\<open>EA_Ret e p\<close> edge from the return statement's node to
  \<^term>\<open>FunctionResult p\<close>, and the enclosing \<open>Nested\<close> wrapper becomes \<open>Returning\<close>: its body is now
  \<^term>\<open>Seq (seq_after Unwind cafters) Restore\<close>, which is \<^const>\<open>pop_ready\<close> because the callee's
  pending continuations \<open>cafters\<close> --- source residuals of a \<^const>\<open>control_at\<close> location --- carry no
  \<^const>\<open>Restore\<close> (\<open>control_at_head_return_afters_no_Restore\<close>, \<open>unwinding_seq_after_Unwind\<close>).  The
  \<open>frs \<noteq> []\<close> premise excludes the ill-formed base \<^const>\<open>Return\<close> (a stuck top-level return); \<open>csim_step\<close>
  discharges it from \<open>source_wf\<close>.  Deeper wrappers ride along unchanged via the induction hypothesis,
  exactly as in \<open>csim_returning_completion\<close>.
\<close>
theorem csim_return_init_completion:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> procs_compiled \<Pi> g \<Longrightarrow> frs \<noteq> [] \<Longrightarrow>
   head_return c \<Longrightarrow> pstep source_global \<Pi> (c, s, frs) src' \<Longrightarrow>
   \<exists>cfg'. star (cstep source_global g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
proof (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c s frs v t stk src' rule: csim.induct)
  case (Base p c0 kk n cc vv ss)
  from Base.prems(2) show ?case by simp
next
  case (Returning w pc c0c kc nc afters cont callee caller dst p)
  from Returning.prems(3) pop_ready_not_head_return[OF Returning.hyps(1)]
  show ?case by simp
next
  case (Nested inner s0 frs0 v0 stk0 pc c0c kc nc afters cont caller dst)
  have hr_inner: "head_return inner" using Nested.prems(3) by simp
  have nsk: "inner \<noteq> SKIP" using hr_inner by (rule head_return_not_SKIP)
  have nunw: "inner \<noteq> Unwind" using hr_inner by auto
  obtain inner' s' fz where
    src': "src' = (seq_after (Seq inner' Restore) afters, s', fz)"
      and stepin: "pstep source_global \<Pi> (inner, s0, frs0 @ [Frame caller dst]) (inner', s', fz)"
    by (rule pstep_seq_after_seq_restore[OF Nested.prems(4) nsk nunw])
  show ?case
  proof (cases "frs0 = []")
    case True
    have baseInner: "csim \<Pi> g (inner, s0, []) (v0, s0, stk0)" using Nested.hyps(1) True by simp
    from csim_base_procD[OF baseInner] obtain pin c0in kin nin where
      ctrl: "control_at \<Pi> pin c0in kin nin inner v0"
        and cacc: "compiled_at \<Pi> g pin c0in kin nin"
        and pa: "proc_activation \<Pi> pin c0in" .
    have stk0nil: "stk0 = []" using csim_Nil_baseD[OF baseInner] by simp
    from pa obtain decl where pdecl: "\<Pi> pin = Some decl" "c0in = body decl"
      by (rule proc_activationD)
    have srcc0: "source_com c0in"
      using procs_compiled_source_com[OF Nested.prems(1) \<open>\<Pi> pin = Some decl\<close>]
            \<open>c0in = body decl\<close>
      by simp
    obtain e cafters where innerform: "inner = seq_after (Return e) cafters"
      using head_return_seq_after_form[OF hr_inner] by blast
    \<comment> \<open>the head step is @{text \<open>Return e --> Unwind\<close>}, leaving the continuations \<open>cafters\<close>\<close>
    have stepin1: "pstep source_global \<Pi> (seq_after (Return e) cafters, s0, [Frame caller dst]) (inner', s', fz)"
      using stepin True innerform by simp
    obtain h' where inner'form: "inner' = seq_after h' cafters"
        and hstep: "pstep source_global \<Pi> (Return e, s0, [Frame caller dst]) (h', s', fz)"
      by (rule pstep_seq_after_headD[OF stepin1]) auto
    have hUnw: "h' = Unwind" and s'eq: "s' = ret_store e s0" and fzeq: "fz = [Frame caller dst]"
      using hstep by (cases e; auto simp: ret_store_def)+
    \<comment> \<open>the callee continuations carry no \<open>Restore\<close>, so the \<open>Unwind\<close> spine is \<open>pop_ready\<close>\<close>
    have noRest: "\<forall>a \<in> set cafters. a \<noteq> Restore"
      by (rule control_at_head_return_afters_no_Restore[OF ctrl[unfolded innerform] srcc0])
    have popready: "pop_ready (Seq (seq_after Unwind cafters) Restore)"
      using unwinding_seq_after_Unwind[OF noRest] by simp
    \<comment> \<open>CFG: one \<open>Intra\<close> step along the return edge to @{term \<open>FunctionResult pin\<close>}\<close>
    from cacc obtain n' en E K where comp: "compile \<Pi> pin c0in kin nin = (n', en, E, K)"
        and Esub: "E \<subseteq> intra g" by (auto simp: compiled_at_def)
    obtain j where vk: "v0 = Statement j"
        and edge: "(Statement j, EA_Ret e pin, FunctionResult pin) \<in> E"
      using control_at_seq_after_return_edge[OF ctrl[unfolded innerform] refl comp] by blast
    have edgeg: "(Statement j, EA_Ret e pin, FunctionResult pin) \<in> intra g" using edge Esub by blast
    have cstep1: "cstep source_global g (Statement j, s0, [(cont, dst, caller)])
                          (FunctionResult pin, ret_store e s0, [(cont, dst, caller)])"
      using cstep.Intra[OF edgeg edge_step_EA_Ret_ret_store] .
    \<comment> \<open>the enclosing wrapper becomes @{text Returning}\<close>
    have rel: "csim \<Pi> g
        (seq_after (Seq (seq_after Unwind cafters) Restore) afters, ret_store e s0, [Frame caller dst])
        (FunctionResult pin, ret_store e s0, [(cont, dst, caller)])"
      by (rule csim.Returning[OF popready Nested.hyps(3) Nested.hyps(4) Nested.hyps(5)])
    have srcshape: "src' = (seq_after (Seq (seq_after Unwind cafters) Restore) afters,
                            ret_store e s0, [Frame caller dst])"
      using src' inner'form hUnw s'eq fzeq by simp
    have "star (cstep source_global g) (v0, s0, stk0 @ [(cont, dst, caller)])
                         (FunctionResult pin, ret_store e s0, [(cont, dst, caller)])"
      using cstep1 vk stk0nil by (auto intro: cstep_star_single)
    with rel srcshape show ?thesis by auto
  next
    case False
    from pstep_frame_restrict[OF stepin refl False] obtain fz' where
      fz: "fz = fz' @ [Frame caller dst]"
        and stepin': "pstep source_global \<Pi> (inner, s0, frs0) (inner', s', fz')" by blast
    from Nested.hyps(2)[OF Nested.prems(1) False hr_inner stepin'] obtain v' t' stk' where
      cstepin: "star (cstep source_global g) (v0, s0, stk0) (v', t', stk')"
        and csimin: "csim \<Pi> g (inner', s', fz') (v', t', stk')" by auto
    have teq: "t' = s'" using csim_store_eq[OF csimin] by simp
    have cstepN: "star (cstep source_global g) (v0, s0, stk0 @ [(cont, dst, caller)])
                                 (v', s', stk' @ [(cont, dst, caller)])"
      using cstep_star_frame_extend[OF cstepin, of "[(cont, dst, caller)]"] teq by simp
    have "csim \<Pi> g (seq_after (Seq inner' Restore) afters, s', fz' @ [Frame caller dst])
                   (v', s', stk' @ [(cont, dst, caller)])"
      by (rule csim.Nested[OF csimin[unfolded teq] Nested.hyps(3) Nested.hyps(4) Nested.hyps(5)])
    then have "csim \<Pi> g src' (v', s', stk' @ [(cont, dst, caller)])" by (simp add: src' fz)
    with cstepN show ?thesis by blast
  qed
qed

section \<open>Single-step and finite-execution forward simulation\<close>

text \<open>A return in head position runs with a nonempty frame stack: only a \<open>Base\<close> activation has an
  empty stack, and its located residual is a source command, so \<open>source_wf\<close> forbids it from heading
  with \<^const>\<open>Return\<close>.  This is where \<open>source_wf\<close> discharges the nonempty-frame side condition of
  \<open>csim_return_init_completion\<close> --- confined to the return-initiation branch of \<open>csim_step\<close>.\<close>
lemma csim_head_return_frames:
  assumes SIM: "csim \<Pi> g (c, s, frs) (v, t, stk)"
      and PC: "procs_compiled \<Pi> g"
      and WF: "source_wf (c, s, frs)"
      and RET: "head_return c"
  shows "frs \<noteq> []"
proof (rule ccontr)
  assume "\<not> frs \<noteq> []"
  hence "csim \<Pi> g (c, s, []) (v, t, stk)" using SIM by simp
  from csim_base_procD[OF this] obtain p c0 kk n where
    ctrl: "control_at \<Pi> p c0 kk n c v" and pa: "proc_activation \<Pi> p c0"
    by metis
  from pa obtain decl where pdecl: "\<Pi> p = Some decl" "c0 = body decl"
    by (rule proc_activationD)
  have "source_com c0"
    using procs_compiled_source_com[OF PC \<open>\<Pi> p = Some decl\<close>] \<open>c0 = body decl\<close> by simp
  hence "source_com c" using control_at_source_com[OF ctrl] by simp
  from source_wf_source_not_head_return[OF WF this] RET show False by simp
qed

text \<open>
  One-step forward simulation.  Every source \<^const>\<open>pstep\<close> from a \<open>csim\<close>-related, \<open>source_wf\<close>
  configuration is matched by a \<^const>\<open>star\<close> of target \<^const>\<open>cstep\<close>s landing in a \<open>csim\<close>-related
  successor.  The proof is the four-way redex classification (\<open>head_call\<close> / \<open>head_return\<close> /
  \<open>is_returning\<close> / otherwise-intra) dispatched to the four completion theorems; \<open>source_wf\<close> is used
  only to supply the nonempty frame for the return-initiation branch.  The public statement exposes
  none of the internal classifiers, compile tuples, offsets, or frame conditions.
\<close>
theorem csim_step:
  assumes SIM: "csim \<Pi> g (c, s, frs) (v, t, stk)"
      and PC: "procs_compiled \<Pi> g"
      and WF: "source_wf (c, s, frs)"
      and STEP: "pstep source_global \<Pi> (c, s, frs) src'"
  shows "\<exists>cfg'. star (cstep source_global g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
proof -
  consider (call) "head_call c" | (ret) "head_return c" | (returning) "is_returning c"
    | (intra) "\<not> head_call c" "\<not> head_return c" "\<not> is_returning c" by blast
  then show ?thesis
  proof cases
    case call
    from csim_call_completion[OF SIM PC call STEP] show ?thesis .
  next
    case ret
    from csim_head_return_frames[OF SIM PC WF ret]
    have "frs \<noteq> []" .
    from csim_return_init_completion[OF SIM PC this ret STEP] show ?thesis .
  next
    case returning
    from csim_returning_completion[OF SIM returning STEP] show ?thesis .
  next
    case intra
    obtain c' s' frs' where sc: "src' = (c', s', frs')" by (cases src')
    have "intra_step \<Pi> (c, s, frs) (c', s', frs')"
      by (rule pstep_intra_classify[OF STEP[unfolded sc] intra(1) intra(2) intra(3)])
    from csim_intra_completion[OF SIM PC this] show ?thesis by (simp add: sc)
  qed
qed

text \<open>
  Finite-execution forward simulation.  A whole \<^const>\<open>pstep\<close> run from a \<open>csim\<close>-related, \<open>source_wf\<close>
  configuration is matched by a \<^const>\<open>cstep\<close> run into a \<open>csim\<close>-related successor.  Induction on the
  source run: \<open>csim_step\<close> advances one step, \<open>source_wf_pstep\<close> re-establishes the invariant for the
  next step, and \<open>star_trans\<close> composes the target runs.
\<close>
lemma csim_run:
  assumes PC: "procs_compiled \<Pi> g"
      and RUN: "star (pstep source_global \<Pi>) sc sc'"
      and SIM: "csim \<Pi> g sc dg"
      and WF: "source_wf sc"
  shows "\<exists>dg'. star (cstep source_global g) dg dg' \<and> csim \<Pi> g sc' dg'"
  using RUN SIM WF
proof (induction arbitrary: dg rule: star.induct)
  case (refl a)
  obtain v0 t0 k0 where "dg = (v0, t0, k0)" by (cases dg)
  with refl show ?case by (auto intro: star.refl)
next
  case (step a b cc)
  obtain c0 s0 f0 where a: "a = (c0, s0, f0)" by (cases a)
  obtain c1 s1 f1 where b: "b = (c1, s1, f1)" by (cases b)
  obtain v0 t0 k0 where dgd: "dg = (v0, t0, k0)" by (cases dg)
  have SIMa: "csim \<Pi> g (c0, s0, f0) (v0, t0, k0)" using step.prems(1) a dgd by simp
  have WFa: "source_wf (c0, s0, f0)" using step.prems(2) a by simp
  have STEP: "pstep source_global \<Pi> (c0, s0, f0) (c1, s1, f1)" using step.hyps(1) a b by simp
  from csim_step[OF SIMa PC WFa STEP] obtain dg1 where
    run1: "star (cstep source_global g) (v0, t0, k0) dg1" and sim1: "csim \<Pi> g (c1, s1, f1) dg1" by blast
  have bodies: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
    using procs_compiled_source_com[OF PC] .
  have WFb: "source_wf b" using source_wf_pstep[OF bodies STEP WFa] b by simp
  have sim1b: "csim \<Pi> g b dg1" using sim1 b by simp
  from step.IH[OF sim1b WFb] obtain dg' where
    run2: "star (cstep source_global g) dg1 dg'" and sim2: "csim \<Pi> g cc dg'" by blast
  from run1 run2 have "star (cstep source_global g) (v0, t0, k0) dg'" by (rule star_trans)
  with sim2 show ?case using dgd by blast
qed

theorem csim_star:
  assumes SIM: "csim \<Pi> g (c, s, frs) (v, t, stk)"
      and PC: "procs_compiled \<Pi> g"
      and WF: "source_wf (c, s, frs)"
      and RUN: "star (pstep source_global \<Pi>) (c, s, frs) src'"
  shows "\<exists>cfg'. star (cstep source_global g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
  using csim_run[OF PC RUN SIM WF] .



end



