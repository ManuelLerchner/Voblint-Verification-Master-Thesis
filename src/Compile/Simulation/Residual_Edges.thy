theory Residual_Edges
  imports Residual_Location "Voblint_CFG.CFG_Exec"
begin

section \<open>The next CFG edge of a located residual\<close>

text \<open>
  If a residual is located at a node and the command about to run is a base one --- an
  assignment, a check, a call, a return --- then the edge the compiler emitted for it
  really is in the graph, and taking the source step re-locates the successor residual at
  that edge's target.  Every simulation step reads its edge off one of these facts.

  \<open>intra_step\<close> collects the source steps that stay inside one activation, and
  \<open>intra_step_simulation\<close> assembles the facts below into the statement that any such step
  is matched by a run of \<^const>\<open>cstep\<close>.
\<close>

subsection \<open>Located base residuals emit their compiled edge\<close>

text \<open>A \<^emph>\<open>base\<close> residual is one the compiler turns into a single intra edge, rather than a
  branch, a call, or a relocation.  \<open>emitted_action\<close> is the action on that edge.  An ordinary
  \<^const>\<open>Call\<close> has none, because it is compiled to a call edge instead; a \<^const>\<open>Call\<close> that
  \<^const>\<open>special_table\<close> classifies is resolved in place, and \<open>wf_source_com\<close> fixes its
  destination to \<^term>\<open>Some x\<close>, so only that shape emits an action.\<close>
fun emitted_action :: "com \<Rightarrow> edge_action option" where
  "emitted_action (Assign x a) = Some (EA_Assign x a)"
| "emitted_action (VIMP_Proc.com.Check c) = Some (EA_Check c)"
| "emitted_action (Call (Some x) q actuals) =
     (case special_table q of
        None \<Rightarrow> None
      | Some desc \<Rightarrow> map_option (\<lambda>sc. EA_Special sc x) (classify_special desc actuals))"
| "emitted_action _ = None"

text \<open>Which action it is does not matter to the recursive \<open>control_at\<close> cases: they only carry
  an edge up through the enclosing fragment and re-locate the completed residual at the same
  node.  So one induction serves every base shape, and the three named corollaries below are
  this lemma read off at each of them.\<close>
lemma control_at_emitted_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> emitted_action r = Some a \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j w. v = Statement j \<and> (Statement j, a, w) \<in> E
       \<and> control_at \<Pi> p c0 k n SKIP w"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (Assign x' a' k n0)
  then show ?case by auto
next
  case (Check b' k n0)
  then show ?case by auto
next
  case (CallHead dst' q' actuals' k n0)
  show ?case
  proof (cases dst')
    case None with CallHead.prems(1) show ?thesis by simp
  next
    case (Some x)
    with CallHead.prems(1) obtain desc sc where
      sp: "special_table q' = Some desc" and cl: "classify_special desc actuals' = Some sc"
        and act: "a = EA_Special sc x"
      by (auto split: option.splits)
    have "(Statement n0, EA_Special sc x, k) \<in> E"
      using CallHead.prems(2) sp cl Some by auto
    with act show ?thesis by auto
  qed
next
  case (SeqRight c1 c2 k n0 r v)
  from SeqRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_Seq_rightE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] obtain j w where
    jw: "v = Statement j" "(Statement j, a, w) \<in> E2"
        "control_at \<Pi> p c2 k (n0 + csize c1) SKIP w" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 SKIP w"
    using control_at.SeqRight[OF SeqRight.hyps(1) jw(3)] .
  then show ?case using jw sub by blast
next
  case (IfLeft c1 k n0 r v b c2)
  from IfLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_If_leftE)
  from IfLeft.IH[OF IfLeft.prems(1) c1c] obtain j w where
    jw: "v = Statement j" "(Statement j, a, w) \<in> E1"
        "control_at \<Pi> p c1 k (Suc n0) SKIP w" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 SKIP w" using control_at.IfLeft[OF jw(3)] .
  then show ?case using jw sub by blast
next
  case (IfRight c2 k n0 c1 r v b)
  from IfRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_If_rightE)
  from IfRight.IH[OF IfRight.prems(1) c2c] obtain j w where
    jw: "v = Statement j" "(Statement j, a, w) \<in> E2"
        "control_at \<Pi> p c2 k (Suc n0 + csize c1) SKIP w" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 SKIP w" using control_at.IfRight[OF jw(3)] .
  then show ?case using jw sub by blast
qed simp_all

lemma control_at_assign_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = Assign x a \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j w. v = Statement j \<and> (Statement j, EA_Assign x a, w) \<in> E
       \<and> control_at \<Pi> p c0 k n SKIP w"
  by (erule control_at_emitted_edge) simp_all

lemma control_at_check_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = VIMP_Proc.com.Check cnd \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j w. v = Statement j \<and> (Statement j, EA_Check cnd, w) \<in> E
       \<and> control_at \<Pi> p c0 k n SKIP w"
  by (erule control_at_emitted_edge) simp_all

lemma control_at_special_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = Call (Some x) q actuals \<Longrightarrow>
   special_table q = Some desc \<Longrightarrow> classify_special desc actuals = Some sc \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j w. v = Statement j \<and> (Statement j, EA_Special sc x, w) \<in> E
       \<and> control_at \<Pi> p c0 k n SKIP w"
  by (erule control_at_emitted_edge) simp_all

text \<open>A located conditional also arises from a loop unfolding (\<^const>\<open>While\<close> steps to
  \<open>If b (Seq c (While b c)) SKIP\<close>), so the \<open>WhileUnfolded\<close> case is real: the true branch
  re-locates the loop body followed by the loop, the false branch re-locates \<^const>\<open>SKIP\<close> at
  the loop's continuation.\<close>
lemma control_at_if_edges:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = If b c1 c2 \<Longrightarrow> source_com r \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j en1 en2. v = Statement j
       \<and> (Statement j, EA_Assume b, en1) \<in> E \<and> (Statement j, EA_AssumeNot b, en2) \<in> E
       \<and> control_at \<Pi> p c0 k n c1 en1 \<and> control_at \<Pi> p c0 k n c2 en2"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (IfHead b' c1' c2' k n0)
  from IfHead.prems(1) have r: "b' = b" "c1' = c1" "c2' = c2" by auto
  note E = compile_If_assume_edges[OF IfHead.prems(3)]
  from IfHead.prems(2) r have src: "source_com c1'" "source_com c2'" by auto
  have ca1: "control_at \<Pi> p (If b' c1' c2') k n0 c1' (Statement (Suc n0))"
    by (rule control_at.IfLeft[OF control_at_initial[OF src(1)]])
  have ca2: "control_at \<Pi> p (If b' c1' c2') k n0 c2' (Statement (Suc n0 + csize c1'))"
    by (rule control_at.IfRight[OF control_at_initial[OF src(2)]])
  from E ca1 ca2 r show ?case by auto
next
  case (SeqRight c1' c2' k n0 r v)
  from SeqRight.prems(3) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2' k (n0 + csize c1') = (n2, Statement (n0 + csize c1'), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_Seq_rightE)
  from SeqRight.IH[OF SeqRight.prems(1) SeqRight.prems(2) c2c] obtain j e1 e2 where
    jw: "v = Statement j" "(Statement j, EA_Assume b, e1) \<in> E2"
        "(Statement j, EA_AssumeNot b, e2) \<in> E2"
        "control_at \<Pi> p c2' k (n0 + csize c1') c1 e1"
        "control_at \<Pi> p c2' k (n0 + csize c1') c2 e2" by blast
  have "control_at \<Pi> p (Seq c1' c2') k n0 c1 e1" "control_at \<Pi> p (Seq c1' c2') k n0 c2 e2"
    using control_at.SeqRight[OF SeqRight.hyps(1) jw(4)]
          control_at.SeqRight[OF SeqRight.hyps(1) jw(5)] .
  then show ?case using jw sub by blast
next
  case (IfLeft c1' k n0 r v b' c2')
  from IfLeft.prems(3) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1' k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_If_leftE)
  from IfLeft.IH[OF IfLeft.prems(1) IfLeft.prems(2) c1c] obtain j e1 e2 where
    jw: "v = Statement j" "(Statement j, EA_Assume b, e1) \<in> E1"
        "(Statement j, EA_AssumeNot b, e2) \<in> E1"
        "control_at \<Pi> p c1' k (Suc n0) c1 e1" "control_at \<Pi> p c1' k (Suc n0) c2 e2" by blast
  have "control_at \<Pi> p (If b' c1' c2') k n0 c1 e1" "control_at \<Pi> p (If b' c1' c2') k n0 c2 e2"
    using control_at.IfLeft[OF jw(4)] control_at.IfLeft[OF jw(5)] .
  then show ?case using jw sub by blast
next
  case (IfRight c2' k n0 c1' r v b')
  from IfRight.prems(3) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2' k (Suc n0 + csize c1')
            = (n2, Statement (Suc n0 + csize c1'), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_If_rightE)
  from IfRight.IH[OF IfRight.prems(1) IfRight.prems(2) c2c] obtain j e1 e2 where
    jw: "v = Statement j" "(Statement j, EA_Assume b, e1) \<in> E2"
        "(Statement j, EA_AssumeNot b, e2) \<in> E2"
        "control_at \<Pi> p c2' k (Suc n0 + csize c1') c1 e1"
        "control_at \<Pi> p c2' k (Suc n0 + csize c1') c2 e2" by blast
  have "control_at \<Pi> p (If b' c1' c2') k n0 c1 e1" "control_at \<Pi> p (If b' c1' c2') k n0 c2 e2"
    using control_at.IfRight[OF jw(4)] control_at.IfRight[OF jw(5)] .
  then show ?case using jw sub by blast
next
  case (WhileUnfolded b'' c'' k n0)
  from WhileUnfolded.prems(1)
  have r: "b'' = b" "Seq c'' (While b'' c'') = c1" "SKIP = c2" by auto
  note E = compile_While_assume_edges[OF WhileUnfolded.prems(3)]
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
  \<^term>\<open>EA_Nop\<close> edge.  \<open>compile_control_at_SKIP_exit_path\<close> already establishes that route as a
  store-preserving \<^const>\<open>intra_path\<close>; an intra path never touches the activation stack, so
  \<open>intra_path_imp_cstep_star\<close> reads it back as a \<open>cstep\<close> run at whatever stack is current.\<close>
lemma control_at_skip_to_exit:
  assumes "control_at \<Pi> p c0 k n r v" and "r = SKIP"
      and "compile \<Pi> p c0 k n = (n', en, E, K)" and "E \<subseteq> intra g"
  shows "star (cstep source_global g) (v, s, stk) (k, s, stk)"
  using intra_path_imp_cstep_star[
          OF compile_control_at_SKIP_exit_path[OF assms(1)[unfolded assms(2)] assms(3,4)],
          where stk = stk]
  by simp

subsection \<open>Completed-head sequence relocation\<close>

text \<open>Under continuation passing the head's own last edge already targets the entry of
  \<^term>\<open>c2\<close> --- or, when the continuation is the enclosing \<^const>\<open>While\<close>, the loop head ---
  so relocation is exactly \<open>control_at_skip_to_exit\<close>.\<close>
lemma control_at_seq_skip_reloc:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = Seq SKIP c2 \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> source_com c0 \<Longrightarrow>
   \<exists>v'. control_at \<Pi> p c0 k n c2 v' \<and> star (cstep source_global g) (v, s, stk) (v', s, stk)"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (SeqLeft c1 n0 r_in v c2r k)
  from SeqLeft.prems(1) have ri: "r_in = SKIP" and c2eq: "c2r = c2" by auto
  from SeqLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_Seq_leftE)
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
    and sub: "E1 \<subseteq> E"
    by (rule compile_While_bodyE)
  have "control_at \<Pi> p c (Statement n0) (Suc n0) SKIP v" using WhileBody.hyps ri by simp
  from control_at_skip_to_exit[OF this refl cc subset_trans[OF sub WhileBody.prems(3)]]
  have sk: "star (cstep source_global g) (v, s, stk) (Statement n0, s, stk)" .
  have "control_at \<Pi> p (While b c) k n0 (While b c) (Statement n0)" by (rule control_at.WhileHead)
  then have "control_at \<Pi> p (While b c) k n0 c2 (Statement n0)" using c2eq by simp
  with sk show ?case by blast
next
  case (SeqRight c1 c2' k n0 r v)
  from SeqRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2' k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_Seq_rightE)
  have src2: "source_com c2'" using SeqRight.prems(4) by simp
  from SeqRight.IH[OF SeqRight.prems(1) c2c subset_trans[OF sub SeqRight.prems(3)] src2]
  obtain v' where v': "control_at \<Pi> p c2' k (n0 + csize c1) c2 v'"
    "star (cstep source_global g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (Seq c1 c2') k n0 c2 v'"
    using control_at.SeqRight[OF SeqRight.hyps(1) v'(1)] .
  with v'(2) show ?case by blast
next
  case (IfLeft c1 k n0 r v b c2')
  from IfLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_If_leftE)
  have src1: "source_com c1" using IfLeft.prems(4) by simp
  from IfLeft.IH[OF IfLeft.prems(1) c1c subset_trans[OF sub IfLeft.prems(3)] src1]
  obtain v' where v': "control_at \<Pi> p c1 k (Suc n0) c2 v'"
    "star (cstep source_global g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (If b c1 c2') k n0 c2 v'" using control_at.IfLeft[OF v'(1)] .
  with v'(2) show ?case by blast
next
  case (IfRight c2' k n0 c1 r v b)
  from IfRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2' k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_If_rightE)
  have src2: "source_com c2'" using IfRight.prems(4) by simp
  from IfRight.IH[OF IfRight.prems(1) c2c subset_trans[OF sub IfRight.prems(3)] src2]
  obtain v' where v': "control_at \<Pi> p c2' k (Suc n0 + csize c1) c2 v'"
    "star (cstep source_global g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (If b c1 c2') k n0 c2 v'" using control_at.IfRight[OF v'(1)] .
  with v'(2) show ?case by blast
qed simp_all

subsection \<open>The caller continuation after a call\<close>

text \<open>
  A call site's caller has, after the call, a finite left-spine of residual continuations
  \<^term>\<open>afters\<close>: the source commands sequenced after the call, in execution order, collected
  while descending the activation's left-associated \<^const>\<open>Seq\<close> spine.  \<^term>\<open>seq_after c afters\<close>
  wraps them around the active head \<open>c\<close>: \<^term>\<open>seq_after c [s3, s4] = Seq (Seq c s3) s4\<close>.
  A tail-position call has \<^term>\<open>afters = []\<close> and the caller resumes at bare \<open>c\<close>.  The list
  holds pending commands \<^emph>\<open>inside one activation\<close>; suspended \<^emph>\<open>caller activations\<close> are
  the recursive nesting of \<open>csim\<close> instead.
\<close>
fun seq_after :: "com \<Rightarrow> com list \<Rightarrow> com" where
  "seq_after c [] = c"
| "seq_after c (a # as) = seq_after (Seq c a) as"

lemma seq_after_append: "seq_after (seq_after c xs) ys = seq_after c (xs @ ys)"
  by (induction xs arbitrary: c) auto

lemma seq_after_snoc: "seq_after c (xs @ [a]) = Seq (seq_after c xs) a"
  by (simp add: seq_after_append[symmetric])

text \<open>A \<^const>\<open>seq_after\<close> spine equals a non-\<^const>\<open>Seq\<close> atom only when its head does and the
  continuation list is empty.  These discriminators close the leaf cases of the spine
  inductions.\<close>
lemma seq_after_eq_iff [simp]:
  "(seq_after c afters = SKIP) = (c = SKIP \<and> afters = [])"
  "(SKIP = seq_after c afters) = (c = SKIP \<and> afters = [])"
  "(seq_after c afters = Restore) = (c = Restore \<and> afters = [])"
  "(Restore = seq_after c afters) = (c = Restore \<and> afters = [])"
  "(seq_after c afters = Unwind) = (c = Unwind \<and> afters = [])"
  "(Unwind = seq_after c afters) = (c = Unwind \<and> afters = [])"
  "(seq_after c afters = Assign x a) = (c = Assign x a \<and> afters = [])"
  "(Assign x a = seq_after c afters) = (c = Assign x a \<and> afters = [])"
  "(seq_after c afters = VIMP_Proc.com.Check b) = (c = VIMP_Proc.com.Check b \<and> afters = [])"
  "(VIMP_Proc.com.Check b = seq_after c afters) = (c = VIMP_Proc.com.Check b \<and> afters = [])"
  "(seq_after c afters = If b c1 c2) = (c = If b c1 c2 \<and> afters = [])"
  "(If b c1 c2 = seq_after c afters) = (c = If b c1 c2 \<and> afters = [])"
  "(seq_after c afters = While b cw) = (c = While b cw \<and> afters = [])"
  "(While b cw = seq_after c afters) = (c = While b cw \<and> afters = [])"
  "(seq_after c afters = Return e) = (c = Return e \<and> afters = [])"
  "(Return e = seq_after c afters) = (c = Return e \<and> afters = [])"
  "(seq_after c afters = Call dst q actuals) = (c = Call dst q actuals \<and> afters = [])"
  "(Call dst q actuals = seq_after c afters) = (c = Call dst q actuals \<and> afters = [])"
  by (induction afters arbitrary: c; auto)+

lemma source_com_seq_afterD [dest]:
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

text \<open>A \<^const>\<open>Call\<close> at the bottom-left of a \<^const>\<open>seq_after\<close> spine still sits on the call
  edge the compiler emitted at the call node, and the source step re-locates
  \<^term>\<open>seq_after SKIP afters\<close> at the call's continuation node.  The \<open>SeqLeft\<close> / \<open>WhileBody\<close>
  cases peel the outermost continuation, the passthrough cases keep it.\<close>
lemma control_at_seq_after_call_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = seq_after (Call dst q actuals) afters \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> special_table q = None \<Longrightarrow>
   \<exists>j w. v = Statement j
       \<and> (Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
          FunctionEntry q, w) \<in> K
       \<and> control_at \<Pi> p c0 k n (seq_after SKIP afters) w"
proof (induction arbitrary: afters n' en E K rule: control_at.induct)
  case (CallHead dst' q' actuals' k n0 afters)
  then show ?case by (auto simp: Let_def split: prod.splits)
next
  case (SeqLeft c1 n0 r v c2 k afters)
  obtain xs where afx: "afters = xs @ [c2]" and req: "r = seq_after (Call dst q actuals) xs"
    using SeqLeft.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from SeqLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
    and sub: "K1 \<subseteq> K"
    by (rule compile_Seq_leftE)
  from SeqLeft.IH[OF req c1c SeqLeft.prems(3)] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
         FunctionEntry q, w) \<in> K1"
       "control_at \<Pi> p c1 (Statement (n0 + csize c1)) n0 (seq_after SKIP xs) w" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 (seq_after SKIP afters) w"
    using control_at.SeqLeft[OF jw(3)] by (simp add: afx seq_after_snoc)
  then show ?case using jw sub by blast
next
  case (SeqRight c1 c2 k n0 r v afters)
  from SeqRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and sub: "K2 \<subseteq> K"
    by (rule compile_Seq_rightE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c SeqRight.prems(3)] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
         FunctionEntry q, w) \<in> K2"
       "control_at \<Pi> p c2 k (n0 + csize c1) (seq_after SKIP afters) w" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 (seq_after SKIP afters) w"
    using control_at.SeqRight[OF SeqRight.hyps(1) jw(3)] .
  then show ?case using jw sub by blast
next
  case (IfLeft c1 k n0 r v b c2 afters)
  from IfLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "K1 \<subseteq> K"
    by (rule compile_If_leftE)
  from IfLeft.IH[OF IfLeft.prems(1) c1c IfLeft.prems(3)] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
         FunctionEntry q, w) \<in> K1"
       "control_at \<Pi> p c1 k (Suc n0) (seq_after SKIP afters) w" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 (seq_after SKIP afters) w"
    using control_at.IfLeft[OF jw(3)] .
  then show ?case using jw sub by blast
next
  case (IfRight c2 k n0 c1 r v b afters)
  from IfRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and sub: "K2 \<subseteq> K"
    by (rule compile_If_rightE)
  from IfRight.IH[OF IfRight.prems(1) c2c IfRight.prems(3)] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
         FunctionEntry q, w) \<in> K2"
       "control_at \<Pi> p c2 k (Suc n0 + csize c1) (seq_after SKIP afters) w" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 (seq_after SKIP afters) w"
    using control_at.IfRight[OF jw(3)] .
  then show ?case using jw sub by blast
next
  case (WhileBody c n0 r v b k afters)
  obtain xs where afx: "afters = xs @ [While b c]"
      and req: "r = seq_after (Call dst q actuals) xs"
    using WhileBody.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from WhileBody.prems(2) obtain n1 E1 K1 where
    cc: "compile \<Pi> p c (Statement n0) (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "K1 \<subseteq> K"
    by (rule compile_While_bodyE)
  from WhileBody.IH[OF req cc WhileBody.prems(3)] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
         FunctionEntry q, w) \<in> K1"
       "control_at \<Pi> p c (Statement n0) (Suc n0) (seq_after SKIP xs) w" by blast
  have "control_at \<Pi> p (While b c) k n0 (seq_after SKIP afters) w"
    using control_at.WhileBody[OF jw(3)] by (simp add: afx seq_after_snoc)
  then show ?case using jw sub by blast
qed simp_all

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
  from SeqLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_Seq_leftE)
  from SeqLeft.IH[OF req c1c] show ?case using sub by blast
next
  case (SeqRight c1 c2 k n0 r v afters)
  from SeqRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_Seq_rightE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] show ?case using sub by blast
next
  case (IfLeft c1 k n0 r v b c2 afters)
  from IfLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_If_leftE)
  from IfLeft.IH[OF IfLeft.prems(1) c1c] show ?case using sub by blast
next
  case (IfRight c2 k n0 c1 r v b afters)
  from IfRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_If_rightE)
  from IfRight.IH[OF IfRight.prems(1) c2c] show ?case using sub by blast
next
  case (WhileBody c n0 r v b k afters)
  obtain xs where afx: "afters = xs @ [While b c]" and req: "r = seq_after (Return e) xs"
    using WhileBody.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from WhileBody.prems(2) obtain n1 E1 K1 where
    cc: "compile \<Pi> p c (Statement n0) (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_While_bodyE)
  from WhileBody.IH[OF req cc] show ?case using sub by blast
qed simp_all

lemma control_at_return_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = Return e \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j. v = Statement j \<and> (Statement j, EA_Ret e p, FunctionResult p) \<in> E"
  by (rule control_at_seq_after_return_edge[where afters = "[]"]) simp_all

subsection \<open>The intra-procedural source steps\<close>

text \<open>\<open>intra_step\<close> is the fragment of \<^const>\<open>pstep\<close> that stays inside one activation without
  initiating a return: assignment, sequencing (head execution and head completion), both
  conditionals, and the loop unfolding.  It excludes \<^const>\<open>Call\<close> (pushes a frame),
  \<^const>\<open>Return\<close> (produces \<^const>\<open>Unwind\<close>), and the runtime-only \<^const>\<open>Restore\<close> / \<^const>\<open>Unwind\<close>
  steps.  Every intra step preserves the frame stack and keeps the residual source-shaped.\<close>

inductive intra_step ::
  "proc_table \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool" for \<Pi> where
  IAssign: "intra_step \<Pi> (Assign x a, s, frs) (SKIP, s(x := aval a s), frs)"
| ISpecial: "special_table q = Some desc \<Longrightarrow> classify_special desc actuals = Some sc \<Longrightarrow>
             special_result sc s v \<Longrightarrow>
             intra_step \<Pi> (Call (Some x) q actuals, s, frs) (SKIP, s(x := v), frs)"
| ICheck:  "intra_step \<Pi> (VIMP_Proc.com.Check b, s, frs) (SKIP, s, frs)"
| ISeq1:   "intra_step \<Pi> (Seq SKIP c2, s, frs) (c2, s, frs)"
| ISeq2:   "intra_step \<Pi> (c1, s, frs) (c1', s', frs) \<Longrightarrow>
            intra_step \<Pi> (Seq c1 c2, s, frs) (Seq c1' c2, s', frs)"
| IIfTrue: "truthy (aval b s) \<Longrightarrow> intra_step \<Pi> (If b c1 c2, s, frs) (c1, s, frs)"
| IIfFalse:"\<not> truthy (aval b s) \<Longrightarrow> intra_step \<Pi> (If b c1 c2, s, frs) (c2, s, frs)"
| IWhile:  "intra_step \<Pi> (While b c, s, frs) (If b (Seq c (While b c)) SKIP, s, frs)"

declare intra_step.intros [intro]

inductive_cases intra_SkipE [elim!]:   "intra_step \<Pi> (SKIP, s, frs) y"
inductive_cases intra_AssignE [elim!]: "intra_step \<Pi> (Assign x a, s, frs) y"
inductive_cases intra_CheckE [elim!]:  "intra_step \<Pi> (VIMP_Proc.com.Check b, s, frs) y"
inductive_cases intra_SeqE [elim]:    "intra_step \<Pi> (Seq c1 c2, s, frs) y"
inductive_cases intra_IfE [elim!]:     "intra_step \<Pi> (If b c1 c2, s, frs) y"
inductive_cases intra_WhileE [elim]:  "intra_step \<Pi> (While b c, s, frs) y"
inductive_cases intra_CallE [elim]:   "intra_step \<Pi> (Call dst q actuals, s, frs) y"
inductive_cases intra_ReturnE [elim!]: "intra_step \<Pi> (Return e, s, frs) y"

lemma intra_Seq_cases:
  "intra_step \<Pi> (Seq c1 c2, s, frs) (c', s', frs') \<Longrightarrow>
   (c1 = SKIP \<and> c' = c2 \<and> s' = s \<and> frs' = frs) \<or>
   (\<exists>c1'. c' = Seq c1' c2 \<and> frs' = frs \<and> intra_step \<Pi> (c1, s, frs) (c1', s', frs))"
  by auto

lemma intra_If_cases:
  "intra_step \<Pi> (If b c1 c2, s, frs) (c', s', frs') \<Longrightarrow>
   (truthy (aval b s) \<and> c' = c1 \<and> s' = s \<and> frs' = frs) \<or>
   (\<not> truthy (aval b s) \<and> c' = c2 \<and> s' = s \<and> frs' = frs)"
  by auto

lemma intra_step_any_frame:
  "intra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> intra_step \<Pi> (c, s, fr) (c', s', fr)"
  by (induction "(c, s, frs)" "(c', s', frs')" arbitrary: c s frs c' s' frs'
      rule: intra_step.induct) auto

lemma intra_step_frame_eq:
  "intra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> frs' = frs"
  by (induction "(c, s, frs)" "(c', s', frs')" arbitrary: c s frs c' s' frs'
      rule: intra_step.induct) auto

subsection \<open>Intra-step simulation\<close>

text \<open>The theory's conclusion: an \<^const>\<open>intra_step\<close> of a located residual leaves the frame
  stack alone, and the graph follows it to a node at which the successor residual is located
  again.  This is the fact the simulation relation is preserved by.\<close>
theorem intra_step_simulation:
  "control_at \<Pi> p c0 k n c v \<Longrightarrow>
   intra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> source_com c0 \<Longrightarrow>
   frs' = frs
   \<and> (\<exists>v'. control_at \<Pi> p c0 k n c' v'
        \<and> star (cstep source_global g) (v, s, stk) (v', s', stk))"
proof (induction arbitrary: c' s' frs' n' en E K rule: control_at.induct)
  case (Skip k n0) then show ?case by blast
next
  case (Assign x a k n0)
  from Assign.prems(1) have out: "c' = SKIP" "s' = s(x := aval a s)" "frs' = frs"
    by auto
  have ca: "control_at \<Pi> p (Assign x a) k n0 (Assign x a) (Statement n0)"
    by (rule control_at.Assign)
  from control_at_assign_edge[OF ca refl Assign.prems(2)] obtain j w where
    jw: "Statement n0 = Statement j" "(Statement j, EA_Assign x a, w) \<in> E"
        "control_at \<Pi> p (Assign x a) k n0 SKIP w" by blast
  have "(Statement j, EA_Assign x a, w) \<in> intra g"
    using jw(2) Assign.prems(3) by blast
  from cstep_assign[OF this]
  have "cstep source_global g (Statement j, s, stk) (w, s(x := aval a s), stk)" by simp
  then have "star (cstep source_global g) (Statement n0, s, stk) (w, s', stk)"
    using jw(1) out(2) by simp
  then show ?case using out(1,3) jw(3) by auto
next
  case (AssignDone x a k n0) then show ?case by blast
next
  case (Check b k n0)
  from Check.prems(1) have out: "c' = SKIP" "s' = s" "frs' = frs"
    by auto
  have ca: "control_at \<Pi> p (VIMP_Proc.com.Check b) k n0 (VIMP_Proc.com.Check b) (Statement n0)"
    by (rule control_at.Check)
  from control_at_check_edge[OF ca refl Check.prems(2)] obtain j w where
    jw: "Statement n0 = Statement j" "(Statement j, EA_Check b, w) \<in> E"
        "control_at \<Pi> p (VIMP_Proc.com.Check b) k n0 SKIP w" by blast
  have "(Statement j, EA_Check b, w) \<in> intra g"
    using jw(2) Check.prems(3) by blast
  from cstep_check[OF this]
  have "cstep source_global g (Statement j, s, stk) (w, s, stk)" .
  then have "star (cstep source_global g) (Statement n0, s, stk) (w, s', stk)"
    using jw(1) out(2) by simp
  then show ?case using out(1,3) jw(3) by auto
next
  case (CheckDone b k n0) then show ?case by blast
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
    from SeqLeft.prems(2) obtain n1 E1 K1 where
      c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
      and sub: "E1 \<subseteq> E"
      by (rule compile_Seq_leftE)
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
  from SeqRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_Seq_rightE)
  have src2: "source_com c2" using SeqRight.prems(4) by simp
  from SeqRight.IH[OF SeqRight.prems(1) c2c subset_trans[OF sub SeqRight.prems(3)] src2]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c2 k (n0 + csize c1) c' v'
          \<and> star (cstep source_global g) (v, s, stk) (v', s', stk)" by auto
  then obtain v' where v': "control_at \<Pi> p c2 k (n0 + csize c1) c' v'"
    "star (cstep source_global g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 c' v'"
    using control_at.SeqRight[OF SeqRight.hyps(1) v'(1)] .
  with fr v'(2) show ?case by blast
next
  case (IfHead b c1 c2 k n0)
  have ca: "control_at \<Pi> p (If b c1 c2) k n0 (If b c1 c2) (Statement n0)"
    by (rule control_at.IfHead)
  from control_at_if_edges[OF ca refl IfHead.prems(4) IfHead.prems(2)] obtain j en1 en2 where
    jj: "Statement n0 = Statement j"
       "(Statement j, EA_Assume b, en1) \<in> E" "(Statement j, EA_AssumeNot b, en2) \<in> E"
       "control_at \<Pi> p (If b c1 c2) k n0 c1 en1" "control_at \<Pi> p (If b c1 c2) k n0 c2 en2" by blast
  from intra_If_cases[OF IfHead.prems(1)] consider
      (t) "truthy (aval b s)" "c' = c1" "s' = s" "frs' = frs"
    | (f) "\<not> truthy (aval b s)" "c' = c2" "s' = s" "frs' = frs" by blast
  then show ?case
  proof cases
    case t
    have "(Statement j, EA_Assume b, en1) \<in> intra g" using jj(2) IfHead.prems(3) by blast
    from cstep_assume[OF this] t(1)
    have "star (cstep source_global g) (Statement n0, s, stk) (en1, s, stk)"
      using jj(1) by simp
    then show ?thesis using t jj(4) by auto
  next
    case f
    have "(Statement j, EA_AssumeNot b, en2) \<in> intra g" using jj(3) IfHead.prems(3) by blast
    from cstep_assume_not[OF this] f(1)
    have "star (cstep source_global g) (Statement n0, s, stk) (en2, s, stk)"
      using jj(1) by simp
    then show ?thesis using f jj(5) by auto
  qed
next
  case (IfLeft c1 k n0 r v b c2)
  from IfLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub1: "E1 \<subseteq> E"
    by (rule compile_If_leftE)
  have src1: "source_com c1" using IfLeft.prems(4) by simp
  from IfLeft.IH[OF IfLeft.prems(1) c1c subset_trans[OF sub1 IfLeft.prems(3)] src1]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c1 k (Suc n0) c' v'
          \<and> star (cstep source_global g) (v, s, stk) (v', s', stk)" by auto
  then obtain v' where v': "control_at \<Pi> p c1 k (Suc n0) c' v'"
    "star (cstep source_global g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (If b c1 c2) k n0 c' v'" using control_at.IfLeft[OF v'(1)] .
  with fr v'(2) show ?case by blast
next
  case (IfRight c2 k n0 c1 r v b)
  from IfRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and sub2: "E2 \<subseteq> E"
    by (rule compile_If_rightE)
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
  case (IfDone b c1 c2 k n0) then show ?case by blast
next
  case (WhileHead b cW k n0)
  from WhileHead.prems(1) have out: "c' = If b (Seq cW (While b cW)) SKIP" "s' = s" "frs' = frs"
    by auto
  have "control_at \<Pi> p (While b cW) k n0 (If b (Seq cW (While b cW)) SKIP) (Statement n0)"
    by (rule control_at.WhileUnfolded)
  then show ?case using out by auto
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
      (t) "truthy (aval b s)" "c' = Seq cW (While b cW)" "s' = s" "frs' = frs"
    | (f) "\<not> truthy (aval b s)" "c' = SKIP" "s' = s" "frs' = frs" by blast
  then show ?case
  proof cases
    case t
    have "(Statement j, EA_Assume b, en1) \<in> intra g" using jj(2) WhileUnfolded.prems(3) by blast
    from cstep_assume[OF this] t(1)
    have "star (cstep source_global g) (Statement n0, s, stk) (en1, s, stk)"
      using jj(1) by simp
    then show ?thesis using t jj(4) by auto
  next
    case f
    have "(Statement j, EA_AssumeNot b, en2) \<in> intra g" using jj(3) WhileUnfolded.prems(3) by blast
    from cstep_assume_not[OF this] f(1)
    have "star (cstep source_global g) (Statement n0, s, stk) (en2, s, stk)"
      using jj(1) by simp
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
      and sub: "E1 \<subseteq> E"
      by (rule compile_While_bodyE)
    have srcW: "source_com cW" using WhileBody.prems(4) by simp
    from WhileBody.IH[OF s2(3) cc subset_trans[OF sub WhileBody.prems(3)] srcW]
    obtain v' where v': "control_at \<Pi> p cW (Statement n0) (Suc n0) r' v'"
      "star (cstep source_global g) (v, s, stk) (v', s', stk)" by auto
    have "control_at \<Pi> p (While b cW) k n0 (Seq r' (While b cW)) v'"
      using control_at.WhileBody[OF v'(1)] .
    then show ?thesis using s2 v'(2) by auto
  qed
next
  case (WhileDone b cW k n0) then show ?case by blast
next
  case (CallHead dst q actuals k n0)
  from CallHead.prems(1) obtain x desc sc v where
    out: "dst = Some x" "special_table q = Some desc" "classify_special desc actuals = Some sc"
         "special_result sc s v" "c' = SKIP" "s' = s(x := v)" "frs' = frs"
    by auto
  have ca: "control_at \<Pi> p (Call (Some x) q actuals) k n0 (Call (Some x) q actuals) (Statement n0)"
    by (rule control_at.CallHead)
  from control_at_special_edge[OF ca refl out(2) out(3) CallHead.prems(2)[unfolded out(1)]]
  obtain j w where
    jw: "Statement n0 = Statement j" "(Statement j, EA_Special sc x, w) \<in> E"
        "control_at \<Pi> p (Call (Some x) q actuals) k n0 SKIP w" by blast
  have edgeg: "(Statement j, EA_Special sc x, w) \<in> intra g"
    using jw(2) CallHead.prems(3) by blast
  have mem: "s(x := v) \<in> edge_step (EA_Special sc x) s" using out(4) by auto
  have "cstep source_global g (Statement j, s, stk) (w, s(x := v), stk)"
    using cstep.Intra[OF edgeg mem] by simp
  then have "star (cstep source_global g) (Statement n0, s, stk) (w, s', stk)"
    using jw(1) out(6) by simp
  then show ?case using out(1,5,7) jw(3) by auto
next
  case (CallDone dst q actuals k n0) then show ?case by blast
next
  case (ReturnHead e k n0) then show ?case by blast
qed

end
