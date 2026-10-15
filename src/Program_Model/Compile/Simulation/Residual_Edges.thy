theory Residual_Edges
  imports Residual_Location "Voblint_CFG.CFG_Exec"
begin

section \<open>The next CFG edge of a located residual\<close>

text \<open>
  If a residual is located at a node and the command about to run is a base one --- an
  assignment, a check, a call, a return --- then the edge the compiler emitted for it
  really is in the graph, and taking the source step re-locates the successor residual at
  that edge's target.  Every simulation step reads its edge off one of these facts.

  \<open>gintra_step\<close> collects the source steps that stay inside one activation, and
  \<open>intra_step_simulation\<close> assembles the facts below into the statement that any such step
  is matched by a run of \<^const>\<open>cfg_exec_sem.gcstep\<close>.

  Six proofs here induct on \<^const>\<open>control_at\<close> and repeat the same descent: project the
  sub-fragment's compile tuple, apply the induction hypothesis, lift the result back through
  \<open>control_at.SeqRight\<close> / \<open>IfLeft\<close> / \<open>IfRight\<close>.  It looks factorable and is not.  A shared
  \<^emph>\<open>descend to a base clause\<close> lemma would have to carry the residual down unchanged, and
  \<open>SeqLeft\<close> and \<open>WhileBody\<close> rebuild it --- they relate the outer residual \<^term>\<open>Seq r c2\<close> to
  the inner \<open>r\<close>.  So the descent survives only in the three clauses that pass the residual
  through, which is half the cases in two of the six proofs and none of the rest.
\<close>

subsection \<open>Located base residuals emit their compiled edge\<close>

text \<open>A \<^emph>\<open>base\<close> residual is one the compiler turns into a single intra edge, rather than a
  branch, a call, or a relocation.  \<open>emitted_action\<close> is the action on that edge.  An ordinary
  \<^const>\<open>Call\<close> has none, because it is compiled to a call edge instead; a \<^const>\<open>Call\<close> that
  \<^const>\<open>special_table\<close> classifies is resolved in place, and \<open>wf_source_com\<close> fixes its
  destination to \<^term>\<open>Some x\<close>, so only that shape emits an action.\<close>
text \<open>The annotation of the statement a residual runs next. A step leaves the annotation of
  the command it reduces on the \<^const>\<open>SKIP\<close> it produces, so this is what the completed
  residual carries.\<close>
fun stmt_ann :: "('a, 'v, 'e) gcom \<Rightarrow> 'a" where
  "stmt_ann (SKIP i) = i"
| "stmt_ann (Assign i x a) = i"
| "stmt_ann (VIMP_Proc.gcom.Check i l c) = i"
| "stmt_ann (Seq c1 c2) = stmt_ann c1"
| "stmt_ann (If i b c1 c2) = i"
| "stmt_ann (While i b c) = i"
| "stmt_ann (Call i dst q actuals) = i"
| "stmt_ann (Return i e) = i"
| "stmt_ann (Restore i) = i"
| "stmt_ann (Unwind i) = i"

fun emitted_action :: "('a, 'v, 'e) gcom \<Rightarrow> ('v, 'e) gedge_action option" where
  "emitted_action (Assign i x a) = Some (EA_Assign x a)"
| "emitted_action (VIMP_Proc.gcom.Check i l c) = Some (EA_Check l c)"
| "emitted_action (Call i (Some x) q actuals) =
     (case special_table q of
        None \<Rightarrow> None
      | Some desc \<Rightarrow> map_option (\<lambda>sc. EA_Special sc x) (classify_special desc actuals))"
| "emitted_action _ = None"

text \<open>Which action it is does not matter to the recursive \<open>control_at\<close> cases: they only carry
  an edge up through the enclosing fragment and re-locate the completed residual at the same
  node.  So one induction serves every base shape.\<close>
lemma control_at_emitted_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> emitted_action r = Some a \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j w. v = Statement j \<and> (Statement j, a, w) \<in> E
       \<and> control_at \<Pi> p c0 k n (SKIP (stmt_ann r)) w"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (Assign i x' a' k n0)
  then show ?case by auto
next
  case (Check i l b' k n0)
  then show ?case by auto
next
  case (CallHead i dst' q' actuals' k n0)
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
  case (SeqRight c2 k n0 c1 r v)
  from SeqRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_Seq_rightE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] obtain j w where
    jw: "v = Statement j" "(Statement j, a, w) \<in> E2"
        "control_at \<Pi> p c2 k (n0 + csize c1) (SKIP (stmt_ann r)) w" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 (SKIP (stmt_ann r)) w"
    using control_at.SeqRight[OF jw(3)] .
  then show ?case using jw sub by blast
next
  case (IfLeft c1 k n0 r v i b c2)
  from IfLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_If_leftE[OF _ IfLeft.hyps(2)])
  from IfLeft.IH[OF IfLeft.prems(1) c1c] obtain j w where
    jw: "v = Statement j" "(Statement j, a, w) \<in> E1"
        "control_at \<Pi> p c1 k (Suc n0) (SKIP (stmt_ann r)) w" by blast
  have "control_at \<Pi> p (If i b c1 c2) k n0 (SKIP (stmt_ann r)) w"
    using control_at.IfLeft[OF jw(3) IfLeft.hyps(2)] .
  then show ?case using jw sub by blast
next
  case (IfRight c2 k n0 c1 r v i b)
  from IfRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_If_rightE[OF _ IfRight.hyps(2)])
  from IfRight.IH[OF IfRight.prems(1) c2c] obtain j w where
    jw: "v = Statement j" "(Statement j, a, w) \<in> E2"
        "control_at \<Pi> p c2 k (Suc n0 + csize c1) (SKIP (stmt_ann r)) w" by blast
  have "control_at \<Pi> p (If i b c1 c2) k n0 (SKIP (stmt_ann r)) w"
    using control_at.IfRight[OF jw(3) IfRight.hyps(2)] .
  then show ?case using jw sub by blast
qed simp_all

text \<open>The check a residual runs next, when its leftmost command is one.  A located residual
  about to run a check sits at that check's \<^const>\<open>EA_Check\<close> edge, however much sequencing
  wraps it.\<close>
fun next_check :: "('a, 'v, 'e) gcom \<Rightarrow> (check_label \<times> 'e) option" where
  "next_check (VIMP_Proc.gcom.Check i l c) = Some (l, c)"
| "next_check (Seq c1 c2) = next_check c1"
| "next_check _ = None"

lemma control_at_next_check_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> next_check r = Some (l, c) \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> \<exists>w. (v, EA_Check l c, w) \<in> E"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (SeqLeft c1 n0 r v c2 k)
  from SeqLeft.prems(2) obtain m F L
    where "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (m, Statement n0, F, L)"
      and "F \<subseteq> E"
    by (rule compile_Seq_leftE)
  with SeqLeft.IH SeqLeft.prems(1) show ?case by auto
next
  case (SeqRight c2 k n0 c1 r v)
  from SeqRight.prems(2) obtain m F L
    where "compile \<Pi> p c2 k (n0 + csize c1) = (m, Statement (n0 + csize c1), F, L)"
      and "F \<subseteq> E"
    by (rule compile_Seq_rightE)
  with SeqRight.IH SeqRight.prems(1) show ?case by blast
next
  case (IfLeft c1 k n0 r v i b c2)
  from IfLeft.prems(2) obtain m F L
    where "compile \<Pi> p c1 k (Suc n0) = (m, Statement (Suc n0), F, L)" and "F \<subseteq> E"
    by (rule compile_If_leftE[OF _ IfLeft.hyps(2)])
  with IfLeft.IH IfLeft.prems(1) show ?case by blast
next
  case (IfRight c2 k n0 c1 r v i b)
  from IfRight.prems(2) obtain m F L
    where "compile \<Pi> p c2 k (Suc n0 + csize c1) = (m, Statement (Suc n0 + csize c1), F, L)"
      and "F \<subseteq> E"
    by (rule compile_If_rightE[OF _ IfRight.hyps(2)])
  with IfRight.IH IfRight.prems(1) show ?case by blast
next
  case (WhileBody c n0 r v i b k)
  from WhileBody.prems(2) obtain m F L
    where "compile \<Pi> p c (Statement n0) (Suc n0) = (m, Statement (Suc n0), F, L)"
      and "F \<subseteq> E"
    by (rule compile_While_bodyE)
  with WhileBody.IH WhileBody.prems(1) show ?case by auto
qed auto

text \<open>A located conditional also arises from a loop unfolding (\<^const>\<open>While\<close> steps to
  \<open>If b (Seq c (While b c)) SKIP\<close>), so the \<open>WhileUnfolded\<close> case is real: the true branch
  re-locates the loop body followed by the loop, the false branch re-locates \<^const>\<open>SKIP\<close> at
  the loop's continuation.\<close>
lemma control_at_if_edges:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = If i b c1 c2 \<Longrightarrow> source_com r \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j en1 en2. v = Statement j
       \<and> (Statement j, EA_Assume b, en1) \<in> E \<and> (Statement j, EA_AssumeNot b, en2) \<in> E
       \<and> control_at \<Pi> p c0 k n c1 en1 \<and> control_at \<Pi> p c0 k n c2 en2"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (IfHead i b' c1' c2' k n0)
  from IfHead.prems(1) have r: "b' = b" "c1' = c1" "c2' = c2" by auto
  note E = compile_If_assume_edges[OF IfHead.prems(3)]
  from IfHead.prems(2) r have src: "source_com c1'" "source_com c2'" by auto
  have ca1: "control_at \<Pi> p (If i b' c1' c2') k n0 c1'
      (if is_SKIP c1' then k else Statement (Suc n0))"
    using src(1) by (cases "is_SKIP c1'") (auto intro: control_at_initial)
  have ca2: "control_at \<Pi> p (If i b' c1' c2') k n0 c2'
      (if is_SKIP c2' then k else Statement (Suc n0 + csize c1'))"
  proof (cases "is_SKIP c2'")
    case True then show ?thesis by auto
  next
    case False
    have "control_at \<Pi> p (If i b' c1' c2') k n0 c2'
        (Statement (Suc n0 + csize c1'))"
      by (rule control_at.IfRight[OF control_at_initial[OF src(2)] False])
    with False show ?thesis by simp
  qed
  from E ca1 ca2 r show ?case by auto
next
  case (SeqRight c2' k n0 c1' r v)
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
    using control_at.SeqRight[OF jw(4)]
          control_at.SeqRight[OF jw(5)] .
  then show ?case using jw sub by blast
next
  case (IfLeft c1' k n0 r v i b' c2')
  from IfLeft.prems(3) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1' k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_If_leftE[OF _ IfLeft.hyps(2)])
  from IfLeft.IH[OF IfLeft.prems(1) IfLeft.prems(2) c1c] obtain j e1 e2 where
    jw: "v = Statement j" "(Statement j, EA_Assume b, e1) \<in> E1"
        "(Statement j, EA_AssumeNot b, e2) \<in> E1"
        "control_at \<Pi> p c1' k (Suc n0) c1 e1" "control_at \<Pi> p c1' k (Suc n0) c2 e2" by blast
  have "control_at \<Pi> p (If i b' c1' c2') k n0 c1 e1" "control_at \<Pi> p (If i b' c1' c2') k n0 c2 e2"
    using control_at.IfLeft[OF jw(4) IfLeft.hyps(2)] control_at.IfLeft[OF jw(5) IfLeft.hyps(2)] .
  then show ?case using jw sub by blast
next
  case (IfRight c2' k n0 c1' r v i b')
  from IfRight.prems(3) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2' k (Suc n0 + csize c1')
            = (n2, Statement (Suc n0 + csize c1'), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_If_rightE[OF _ IfRight.hyps(2)])
  from IfRight.IH[OF IfRight.prems(1) IfRight.prems(2) c2c] obtain j e1 e2 where
    jw: "v = Statement j" "(Statement j, EA_Assume b, e1) \<in> E2"
        "(Statement j, EA_AssumeNot b, e2) \<in> E2"
        "control_at \<Pi> p c2' k (Suc n0 + csize c1') c1 e1"
        "control_at \<Pi> p c2' k (Suc n0 + csize c1') c2 e2" by blast
  have "control_at \<Pi> p (If i b' c1' c2') k n0 c1 e1" "control_at \<Pi> p (If i b' c1' c2') k n0 c2 e2"
    using control_at.IfRight[OF jw(4) IfRight.hyps(2)] control_at.IfRight[OF jw(5) IfRight.hyps(2)]
    .
  then show ?case using jw sub by blast
next
  case (WhileUnfolded i b'' c'' k n0)
  from WhileUnfolded.prems(1)
  have r: "b'' = b" "Seq c'' (While i b'' c'') = c1" "(SKIP i) = c2" by auto
  note E = compile_While_assume_edges[OF WhileUnfolded.prems(3)]
  from WhileUnfolded.prems(2) have src: "source_com c''" by auto
  have ca1: "control_at \<Pi> p (While i b'' c'') k n0 (Seq c'' (While i b'' c'')) (Statement (Suc n0))"
    by (rule control_at.WhileBody[OF control_at_initial[OF src]])
  have ca2: "control_at \<Pi> p (While i b'' c'') k n0 (SKIP i) k"
    by (rule control_at.WhileDone)
  from E ca1 ca2 r show ?case by auto
qed simp_all

subsection \<open>SKIP relocation to the continuation\<close>

context cfg_exec_sem
begin

text \<open>A located \<^const>\<open>SKIP\<close> --- a completed sub-command --- is at its fragment's continuation
  already, except for a source \<^const>\<open>SKIP\<close>, which still has its own node and one
  \<^term>\<open>EA_Nop\<close> edge.  \<open>compile_control_at_SKIP_exit_path\<close> already establishes that route as a
  store-preserving intra path; an intra path never touches the activation stack, so
  \<open>intra_path_imp_cstep_star\<close> reads it back as a \<open>gcstep\<close> run at whatever stack is current.\<close>
lemma control_at_skip_to_exit:
  assumes "control_at \<Pi> p c0 k n r v" and "is_SKIP r"
      and "compile \<Pi> p c0 k n = (n', en, E, K)" and "E \<subseteq> intra g"
  shows "star (gcstep g) (v, s, stk) (k, s, stk)"
proof -
  from assms(2) obtain j where r: "r = SKIP j" by auto
  show ?thesis
    using intra_path_imp_cstep_star[
            OF compile_control_at_SKIP_exit_path[OF assms(1)[unfolded r] assms(3,4)],
            where stk = stk]
    by simp
qed

subsection \<open>Completed-head sequence relocation\<close>

text \<open>Under continuation passing the head's own last edge already targets the entry of
  \<^term>\<open>c2\<close> --- or, when the continuation is the enclosing \<^const>\<open>While\<close>, the loop head ---
  so relocation is exactly \<open>control_at_skip_to_exit\<close>.\<close>
lemma control_at_seq_skip_reloc:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = Seq (SKIP i) c2 \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> source_com c0 \<Longrightarrow>
   \<exists>v'. control_at \<Pi> p c0 k n c2 v' \<and> star (gcstep g) (v, s, stk) (v', s, stk)"
proof (induction arbitrary: n' en E K rule: control_at.induct)
  case (SeqLeft c1 n0 r_in v c2r k)
  from SeqLeft.prems(1) have ri: "is_SKIP r_in" and c2eq: "c2r = c2" by auto
  from SeqLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_Seq_leftE)
  have src2: "source_com c2r" using SeqLeft.prems(4) by simp
  from control_at_skip_to_exit[OF SeqLeft.hyps(1) ri c1c subset_trans[OF sub SeqLeft.prems(3)]]
  have sk: "star (gcstep g) (v, s, stk) (Statement (n0 + csize c1), s, stk)" .
  have "control_at \<Pi> p (Seq c1 c2r) k n0 c2r (Statement (n0 + csize c1))"
    by (rule control_at.SeqRight[OF control_at_initial[OF src2]])
  then have "control_at \<Pi> p (Seq c1 c2r) k n0 c2 (Statement (n0 + csize c1))" using c2eq by simp
  with sk show ?case by blast
next
  case (WhileBody c n0 r_in v i b k)
  from WhileBody.prems(1) have ri: "is_SKIP r_in" and c2eq: "c2 = While i b c" by auto
  from WhileBody.prems(2) obtain n1 E1 K1 where
    cc: "compile \<Pi> p c (Statement n0) (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_While_bodyE)
  from control_at_skip_to_exit[OF WhileBody.hyps(1) ri cc subset_trans[OF sub WhileBody.prems(3)]]
  have sk: "star (gcstep g) (v, s, stk) (Statement n0, s, stk)" .
  have "control_at \<Pi> p (While i b c) k n0 (While i b c) (Statement n0)"
    by (rule control_at.WhileHead)
  then have "control_at \<Pi> p (While i b c) k n0 c2 (Statement n0)" using c2eq by simp
  with sk show ?case by blast
next
  case (SeqRight c2' k n0 c1 r v)
  from SeqRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2' k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_Seq_rightE)
  have src2: "source_com c2'" using SeqRight.prems(4) by simp
  from SeqRight.IH[OF SeqRight.prems(1) c2c subset_trans[OF sub SeqRight.prems(3)] src2]
  obtain v' where v': "control_at \<Pi> p c2' k (n0 + csize c1) c2 v'"
    "star (gcstep g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (Seq c1 c2') k n0 c2 v'"
    using control_at.SeqRight[OF v'(1)] .
  with v'(2) show ?case by blast
next
  case (IfLeft c1 k n0 r v i b c2')
  from IfLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_If_leftE[OF _ IfLeft.hyps(2)])
  have src1: "source_com c1" using IfLeft.prems(4) by simp
  from IfLeft.IH[OF IfLeft.prems(1) c1c subset_trans[OF sub IfLeft.prems(3)] src1]
  obtain v' where v': "control_at \<Pi> p c1 k (Suc n0) c2 v'"
    "star (gcstep g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (If i b c1 c2') k n0 c2 v'" using control_at.IfLeft[OF v'(1) IfLeft.hyps(2)]
    .
  with v'(2) show ?case by blast
next
  case (IfRight c2' k n0 c1 r v i b)
  from IfRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2' k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_If_rightE[OF _ IfRight.hyps(2)])
  have src2: "source_com c2'" using IfRight.prems(4) by simp
  from IfRight.IH[OF IfRight.prems(1) c2c subset_trans[OF sub IfRight.prems(3)] src2]
  obtain v' where v': "control_at \<Pi> p c2' k (Suc n0 + csize c1) c2 v'"
    "star (gcstep g) (v, s, stk) (v', s, stk)" by blast
  have "control_at \<Pi> p (If i b c1 c2') k n0 c2 v'"
    using control_at.IfRight[OF v'(1) IfRight.hyps(2)]
    .
  with v'(2) show ?case by blast
qed simp_all

end

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
fun seq_after :: "('a, 'v, 'e) gcom \<Rightarrow> ('a, 'v, 'e) gcom list \<Rightarrow> ('a, 'v, 'e) gcom" where
  "seq_after c [] = c"
| "seq_after c (a # as) = seq_after (Seq c a) as"

lemma seq_after_append: "seq_after (seq_after c xs) ys = seq_after c (xs @ ys)"
  by (induction xs arbitrary: c) auto

lemma seq_after_snoc: "seq_after c (xs @ [a]) = Seq (seq_after c xs) a"
  by (simp add: seq_after_append[symmetric])

lemma next_check_seq_after [simp]: "next_check (seq_after c afters) = next_check c"
  by (induction afters arbitrary: c) auto

text \<open>A \<^const>\<open>seq_after\<close> spine equals a non-\<^const>\<open>Seq\<close> atom only when its head does and the
  continuation list is empty.  These discriminators close the leaf cases of the spine
  inductions.\<close>
lemma seq_after_eq_iff [simp]:
  "(seq_after c afters = SKIP i) = (c = SKIP i \<and> afters = [])"
  "(SKIP i = seq_after c afters) = (c = SKIP i \<and> afters = [])"
  "(seq_after c afters = Restore i) = (c = Restore i \<and> afters = [])"
  "(Restore i = seq_after c afters) = (c = Restore i \<and> afters = [])"
  "(seq_after c afters = Unwind i) = (c = Unwind i \<and> afters = [])"
  "(Unwind i = seq_after c afters) = (c = Unwind i \<and> afters = [])"
  "(seq_after c afters = Assign i x a) = (c = Assign i x a \<and> afters = [])"
  "(Assign i x a = seq_after c afters) = (c = Assign i x a \<and> afters = [])"
  "(seq_after c afters = VIMP_Proc.gcom.Check i l b) = (c = VIMP_Proc.gcom.Check i l b \<and> afters = [])"
  "(VIMP_Proc.gcom.Check i l b = seq_after c afters) = (c = VIMP_Proc.gcom.Check i l b \<and> afters = [])"
  "(seq_after c afters = If i b c1 c2) = (c = If i b c1 c2 \<and> afters = [])"
  "(If i b c1 c2 = seq_after c afters) = (c = If i b c1 c2 \<and> afters = [])"
  "(seq_after c afters = While i b cw) = (c = While i b cw \<and> afters = [])"
  "(While i b cw = seq_after c afters) = (c = While i b cw \<and> afters = [])"
  "(seq_after c afters = Return i e) = (c = Return i e \<and> afters = [])"
  "(Return i e = seq_after c afters) = (c = Return i e \<and> afters = [])"
  "(seq_after c afters = Call i dst q actuals) = (c = Call i dst q actuals \<and> afters = [])"
  "(Call i dst q actuals = seq_after c afters) = (c = Call i dst q actuals \<and> afters = [])"
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
  assumes "control_at \<Pi> p c0 k n (seq_after (Return i e) afters) v"
      and "source_com c0"
  shows "\<forall>a \<in> set afters. \<not> is_Restore a"
proof (rule ballI)
  fix a
  assume ain: "a \<in> set afters"
  from control_at_source_com[OF assms] source_com_seq_afterD
  have "source_com a" using ain by blast
  then show "\<not> is_Restore a" by (rule source_com_no_Restore)
qed

text \<open>A \<^const>\<open>Call\<close> at the bottom-left of a \<^const>\<open>seq_after\<close> spine still sits on the call
  edge the compiler emitted at the call node, and the source step re-locates
  \<^term>\<open>seq_after (SKIP i) afters\<close> at the call's continuation node.  The \<open>SeqLeft\<close> / \<open>WhileBody\<close>
  cases peel the outermost continuation, the passthrough cases keep it.\<close>
lemma control_at_seq_after_call_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = seq_after (Call i dst q actuals) afters \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> special_table q = None \<Longrightarrow>
   \<exists>j w. v = Statement j
       \<and> (Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
          FunctionEntry q, w) \<in> K
       \<and> control_at \<Pi> p c0 k n (seq_after (SKIP i) afters) w"
proof (induction arbitrary: afters n' en E K rule: control_at.induct)
  case (CallHead ia dst' q' actuals' k n0 afters)
  then show ?case by (auto simp: Let_def split: prod.splits)
next
  case (SeqLeft c1 n0 r v c2 k afters)
  obtain xs where afx: "afters = xs @ [c2]" and req: "r = seq_after (Call i dst q actuals) xs"
    using SeqLeft.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from SeqLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
    and sub: "K1 \<subseteq> K"
    by (rule compile_Seq_leftE)
  from SeqLeft.IH[OF req c1c SeqLeft.prems(3)] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
         FunctionEntry q, w) \<in> K1"
       "control_at \<Pi> p c1 (Statement (n0 + csize c1)) n0 (seq_after (SKIP i) xs) w" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 (seq_after (SKIP i) afters) w"
    using control_at.SeqLeft[OF jw(3)] by (simp add: afx seq_after_snoc)
  then show ?case using jw sub by blast
next
  case (SeqRight c2 k n0 c1 r v afters)
  from SeqRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and sub: "K2 \<subseteq> K"
    by (rule compile_Seq_rightE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c SeqRight.prems(3)] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
         FunctionEntry q, w) \<in> K2"
       "control_at \<Pi> p c2 k (n0 + csize c1) (seq_after (SKIP i) afters) w" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 (seq_after (SKIP i) afters) w"
    using control_at.SeqRight[OF jw(3)] .
  then show ?case using jw sub by blast
next
  case (IfLeft c1 k n0 r v ia b c2 afters)
  from IfLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "K1 \<subseteq> K"
    by (rule compile_If_leftE[OF _ IfLeft.hyps(2)])
  from IfLeft.IH[OF IfLeft.prems(1) c1c IfLeft.prems(3)] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
         FunctionEntry q, w) \<in> K1"
       "control_at \<Pi> p c1 k (Suc n0) (seq_after (SKIP i) afters) w" by blast
  have "control_at \<Pi> p (If ia b c1 c2) k n0 (seq_after (SKIP i) afters) w"
    using control_at.IfLeft[OF jw(3) IfLeft.hyps(2)] .
  then show ?case using jw sub by blast
next
  case (IfRight c2 k n0 c1 r v ia b afters)
  from IfRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and sub: "K2 \<subseteq> K"
    by (rule compile_If_rightE[OF _ IfRight.hyps(2)])
  from IfRight.IH[OF IfRight.prems(1) c2c IfRight.prems(3)] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
         FunctionEntry q, w) \<in> K2"
       "control_at \<Pi> p c2 k (Suc n0 + csize c1) (seq_after (SKIP i) afters) w" by blast
  have "control_at \<Pi> p (If ia b c1 c2) k n0 (seq_after (SKIP i) afters) w"
    using control_at.IfRight[OF jw(3) IfRight.hyps(2)] .
  then show ?case using jw sub by blast
next
  case (WhileBody c n0 r v ia b k afters)
  obtain xs where afx: "afters = xs @ [While ia b c]"
      and req: "r = seq_after (Call i dst q actuals) xs"
    using WhileBody.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from WhileBody.prems(2) obtain n1 E1 K1 where
    cc: "compile \<Pi> p c (Statement n0) (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "K1 \<subseteq> K"
    by (rule compile_While_bodyE)
  from WhileBody.IH[OF req cc WhileBody.prems(3)] obtain j w where
    jw: "v = Statement j"
       "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
         FunctionEntry q, w) \<in> K1"
       "control_at \<Pi> p c (Statement n0) (Suc n0) (seq_after (SKIP i) xs) w" by blast
  have "control_at \<Pi> p (While ia b c) k n0 (seq_after (SKIP i) afters) w"
    using control_at.WhileBody[OF jw(3)] by (simp add: afx seq_after_snoc)
  then show ?case using jw sub by blast
qed simp_all

lemma control_at_seq_after_return_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = seq_after (Return i e) afters \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j. v = Statement j \<and> (Statement j, EA_Ret e p, FunctionResult p) \<in> E"
proof (induction arbitrary: afters n' en E K rule: control_at.induct)
  case (ReturnHead i e' k n0 afters)
  then show ?case by auto
next
  case (SeqLeft c1 n0 r v c2 k afters)
  obtain xs where afx: "afters = xs @ [c2]" and req: "r = seq_after (Return i e) xs"
    using SeqLeft.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from SeqLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_Seq_leftE)
  from SeqLeft.IH[OF req c1c] show ?case using sub by blast
next
  case (SeqRight c2 k n0 c1 r v afters)
  from SeqRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_Seq_rightE)
  from SeqRight.IH[OF SeqRight.prems(1) c2c] show ?case using sub by blast
next
  case (IfLeft c1 k n0 r v i b c2 afters)
  from IfLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_If_leftE[OF _ IfLeft.hyps(2)])
  from IfLeft.IH[OF IfLeft.prems(1) c1c] show ?case using sub by blast
next
  case (IfRight c2 k n0 c1 r v i b afters)
  from IfRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_If_rightE[OF _ IfRight.hyps(2)])
  from IfRight.IH[OF IfRight.prems(1) c2c] show ?case using sub by blast
next
  case (WhileBody c n0 r v ia b k afters)
  obtain xs where afx: "afters = xs @ [While ia b c]" and req: "r = seq_after (Return i e) xs"
    using WhileBody.prems(1) by (cases afters rule: rev_cases) (auto simp: seq_after_snoc)
  from WhileBody.prems(2) obtain n1 E1 K1 where
    cc: "compile \<Pi> p c (Statement n0) (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_While_bodyE)
  from WhileBody.IH[OF req cc] show ?case using sub by blast
qed simp_all

lemma control_at_return_edge:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r = Return i e \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow>
   \<exists>j. v = Statement j \<and> (Statement j, EA_Ret e p, FunctionResult p) \<in> E"
  by (rule control_at_seq_after_return_edge[where afters = "[]"]) simp_all

subsection \<open>The intra-procedural source steps\<close>

text \<open>\<open>gintra_step\<close> is the fragment of \<^const>\<open>vimp_sem.gpstep\<close> that stays inside one activation without
  initiating a return: assignment, sequencing (head execution and head completion), both
  conditionals, and the loop unfolding.  It excludes \<^const>\<open>Call\<close> (pushes a frame),
  \<^const>\<open>Return\<close> (produces \<^const>\<open>Unwind\<close>), and the runtime-only \<^const>\<open>Restore\<close> / \<^const>\<open>Unwind\<close>
  steps.  Every intra step preserves the frame stack and keeps the residual source-shaped.\<close>

locale residual_sem = vimp_sem ev glob rv conv + cfg_exec_sem ev rv conv glob
  for ev :: "'e \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> int" and glob :: "'v \<Rightarrow> bool" and rv :: 'v
    and conv :: "'v option \<Rightarrow> int \<Rightarrow> int"
begin

inductive gintra_step ::
  "('a, 'v, 'e) gptable \<Rightarrow> ('a, 'v, 'e) gcom \<times> ('v \<Rightarrow> int) \<times> 'v gframe list
    \<Rightarrow> ('a, 'v, 'e) gcom \<times> ('v \<Rightarrow> int) \<times> 'v gframe list \<Rightarrow> bool" for \<Pi> where
  IAssign [intro]: "gintra_step \<Pi> (Assign i x a, s, frs) ((SKIP i), s(x := conv (Some x) (ev a s)), frs)"
| ISpecial [intro]: "special_table q = Some desc \<Longrightarrow> classify_special desc actuals = Some sc \<Longrightarrow>
             special_result ev sc s v \<Longrightarrow>
             gintra_step \<Pi> (Call i (Some x) q actuals, s, frs) ((SKIP i), s(x := conv (Some x) v), frs)"
| ICheck [intro]:  "gintra_step \<Pi> (VIMP_Proc.gcom.Check i l b, s, frs) ((SKIP i), s, frs)"
| ISeq1 [intro]:   "gintra_step \<Pi> (Seq (SKIP i) c2, s, frs) (c2, s, frs)"
| ISeq2 [intro]:   "gintra_step \<Pi> (c1, s, frs) (c1', s', frs) \<Longrightarrow>
            gintra_step \<Pi> (Seq c1 c2, s, frs) (Seq c1' c2, s', frs)"
| IIfTrue [intro]: "truthy (ev b s) \<Longrightarrow> gintra_step \<Pi> (If i b c1 c2, s, frs) (c1, s, frs)"
| IIfFalse [intro]:"\<not> truthy (ev b s) \<Longrightarrow> gintra_step \<Pi> (If i b c1 c2, s, frs) (c2, s, frs)"
| IWhile [intro]:
  "gintra_step \<Pi> (While i b c, s, frs) (If i b (Seq c (While i b c)) (SKIP i), s, frs)"


inductive_cases intra_SkipE [elim!]:   "gintra_step \<Pi> ((SKIP i), s, frs) y"
inductive_cases intra_AssignE [elim!]: "gintra_step \<Pi> (Assign i x a, s, frs) y"
inductive_cases intra_CheckE [elim!]:  "gintra_step \<Pi> (VIMP_Proc.gcom.Check i l b, s, frs) y"
inductive_cases intra_SeqE [elim]:    "gintra_step \<Pi> (Seq c1 c2, s, frs) y"
inductive_cases intra_IfE [elim!]:     "gintra_step \<Pi> (If i b c1 c2, s, frs) y"
inductive_cases intra_WhileE [elim]:  "gintra_step \<Pi> (While i b c, s, frs) y"
inductive_cases intra_CallE [elim]:   "gintra_step \<Pi> (Call i dst q actuals, s, frs) y"
inductive_cases intra_ReturnE [elim!]: "gintra_step \<Pi> (Return i e, s, frs) y"

lemma intra_Seq_cases:
  "gintra_step \<Pi> (Seq c1 c2, s, frs) (c', s', frs') \<Longrightarrow>
   (is_SKIP c1 \<and> c' = c2 \<and> s' = s \<and> frs' = frs) \<or>
   (\<exists>c1'. c' = Seq c1' c2 \<and> frs' = frs \<and> gintra_step \<Pi> (c1, s, frs) (c1', s', frs))"
  by auto

lemma intra_If_cases:
  "gintra_step \<Pi> (If i b c1 c2, s, frs) (c', s', frs') \<Longrightarrow>
   (truthy (ev b s) \<and> c' = c1 \<and> s' = s \<and> frs' = frs) \<or>
   (\<not> truthy (ev b s) \<and> c' = c2 \<and> s' = s \<and> frs' = frs)"
  by auto

lemma intra_step_any_frame:
  "gintra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> gintra_step \<Pi> (c, s, fr) (c', s', fr)"
  by (induction "(c, s, frs)" "(c', s', frs')" arbitrary: c s frs c' s' frs'
      rule: gintra_step.induct) auto

lemma intra_step_frame_eq:
  "gintra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> frs' = frs"
  by (induction "(c, s, frs)" "(c', s', frs')" arbitrary: c s frs c' s' frs'
      rule: gintra_step.induct) auto

subsection \<open>Intra-step simulation\<close>

text \<open>The base cases of that simulation, once: a located residual with an emitted action moves
  along its own edge in one \<open>gcstep\<close> and re-locates as a completed sub-command.  Which action it
  is only decides the store, which the caller supplies as \<open>s' \<in> gedge_step a s\<close>.\<close>
lemma control_at_base_step:
  assumes loc: "control_at \<Pi> p c0 k n r v"
      and act: "emitted_action r = Some a"
      and cmp: "compile \<Pi> p c0 k n = (n', en, E, K)"
      and sub: "E \<subseteq> intra g"
      and stp: "s' \<in> gedge_step a s"
  obtains w where
    "control_at \<Pi> p c0 k n (SKIP (stmt_ann r)) w"
    "star (gcstep g) (v, s, stk) (w, s', stk)"
proof -
  from control_at_emitted_edge[OF loc act cmp] obtain j w where
    jw: "v = Statement j" "(Statement j, a, w) \<in> E"
        "control_at \<Pi> p c0 k n (SKIP (stmt_ann r)) w" by blast
  have "(Statement j, a, w) \<in> intra g" using jw(2) sub by blast
  from gcstep.Intra[OF this stp] have "gcstep g (Statement j, s, stk) (w, s', stk)" .
  then show ?thesis using jw(1) jw(3) that by auto
qed

text \<open>A located conditional takes whichever assume edge the store selects and lands on the
  branch located at that edge's target.  \<^const>\<open>If\<close> heads and loop unfoldings both reach it.\<close>
lemma control_at_if_step:
  assumes loc: "control_at \<Pi> p c0 k n (If i b c1 c2) v"
      and stp: "gintra_step \<Pi> (If i b c1 c2, s, frs) (c', s', frs')"
      and cmp: "compile \<Pi> p c0 k n = (n', en, E, K)"
      and sub: "E \<subseteq> intra g"
      and src: "source_com (If i b c1 c2)"
  shows "frs' = frs
         \<and> (\<exists>v'. control_at \<Pi> p c0 k n c' v' \<and> star (gcstep g) (v, s, stk) (v', s', stk))"
proof -
  from control_at_if_edges[OF loc refl src cmp] obtain j en1 en2 where
    jj: "v = Statement j"
       "(Statement j, EA_Assume b, en1) \<in> E" "(Statement j, EA_AssumeNot b, en2) \<in> E"
       "control_at \<Pi> p c0 k n c1 en1" "control_at \<Pi> p c0 k n c2 en2" by blast
  from intra_If_cases[OF stp] show ?thesis
  proof (elim disjE conjE)
    assume t: "truthy (ev b s)" "c' = c1" "s' = s" "frs' = frs"
    have "(Statement j, EA_Assume b, en1) \<in> intra g" using jj(2) sub by blast
    from star_step1[of "gcstep g", OF cstep_assume[OF this t(1)]]
    show ?thesis using t jj(1,4) by blast
  next
    assume f: "\<not> truthy (ev b s)" "c' = c2" "s' = s" "frs' = frs"
    have "(Statement j, EA_AssumeNot b, en2) \<in> intra g" using jj(3) sub by blast
    from star_step1[of "gcstep g", OF cstep_assume_not[OF this f(1)]]
    show ?thesis using f jj(1,5) by blast
  qed
qed

text \<open>A located \<^term>\<open>Seq r c2\<close> either has finished its head, and relocates to \<open>c2\<close>, or
  steps inside \<open>r\<close>.  Only the caller knows which sub-fragment \<open>r\<close> is located in, so it
  supplies that second case.\<close>
lemma control_at_seq_step:
  assumes loc: "control_at \<Pi> p c0 k n (Seq r c2) v"
      and stp: "gintra_step \<Pi> (Seq r c2, s, frs) (c', s', frs')"
      and cmp: "compile \<Pi> p c0 k n = (n', en, E, K)"
      and sub: "E \<subseteq> intra g"
      and src: "source_com c0"
      and head: "\<And>r'. gintra_step \<Pi> (r, s, frs) (r', s', frs) \<Longrightarrow>
                   \<exists>v'. control_at \<Pi> p c0 k n (Seq r' c2) v'
                        \<and> star (gcstep g) (v, s, stk) (v', s', stk)"
  shows "frs' = frs
         \<and> (\<exists>v'. control_at \<Pi> p c0 k n c' v' \<and> star (gcstep g) (v, s, stk) (v', s', stk))"
  using intra_Seq_cases[OF stp]
proof (elim disjE exE conjE)
  assume r: "is_SKIP r" and out: "c' = c2" "s' = s" "frs' = frs"
  then obtain j where rj: "r = SKIP j" by auto
  from control_at_seq_skip_reloc[OF loc[unfolded rj] refl cmp sub src] show ?thesis
    using out by blast
next
  fix r' assume "c' = Seq r' c2" "frs' = frs" "gintra_step \<Pi> (r, s, frs) (r', s', frs)"
  with head show ?thesis by blast
qed

text \<open>The theory's conclusion: an \<^const>\<open>gintra_step\<close> of a located residual leaves the frame
  stack alone, and the graph follows it to a node at which the successor residual is located
  again.  This is the fact the simulation relation is preserved by.\<close>
theorem intra_step_simulation:
  "control_at \<Pi> p c0 k n c v \<Longrightarrow>
   gintra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> source_com c0 \<Longrightarrow>
   frs' = frs
   \<and> (\<exists>v'. control_at \<Pi> p c0 k n c' v'
        \<and> star (gcstep g) (v, s, stk) (v', s', stk))"
proof (induction arbitrary: c' s' frs' n' en E K rule: control_at.induct)
  case (Skip i k n0) then show ?case by blast
next
  case (Assign i x a k n0)
  from Assign.prems(1) have out: "c' = (SKIP i)" "s' = s(x := conv (Some x) (ev a s))" "frs' = frs"
    by auto
  have act: "emitted_action (Assign i x a) = Some (EA_Assign x a)" by simp
  have mem: "s' \<in> gedge_step (EA_Assign x a) s" using out(2) by simp
  obtain w where "control_at \<Pi> p (Assign i x a) k n0 (SKIP i) w"
      and "star (gcstep g) (Statement n0, s, stk) (w, s', stk)"
    by (rule control_at_base_step[OF control_at.Assign act Assign.prems(2)
                                     Assign.prems(3) mem]) auto
  then show ?case using out(1,3) by auto
next
  case (AssignDone i x a k n0) then show ?case by blast
next
  case (Check i l b k n0)
  from Check.prems(1) have out: "c' = (SKIP i)" "s' = s" "frs' = frs"
    by auto
  have act: "emitted_action (VIMP_Proc.gcom.Check i l b) = Some (EA_Check l b)" by simp
  have mem: "s' \<in> gedge_step (EA_Check l b) s" using out(2) by simp
  obtain w where "control_at \<Pi> p (VIMP_Proc.gcom.Check i l b) k n0 (SKIP i) w"
      and "star (gcstep g) (Statement n0, s, stk) (w, s', stk)"
    by (rule control_at_base_step[OF control_at.Check act Check.prems(2)
                                     Check.prems(3) mem]) auto
  then show ?case using out(1,3) by auto
next
  case (CheckDone i l b k n0) then show ?case by blast
next
  case (SeqLeft c1 n0 r v c2 k)
  from SeqLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 (Statement (n0 + csize c1)) n0 = (n1, Statement n0, E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_Seq_leftE)
  have src1: "source_com c1" using SeqLeft.prems(4) by simp
  show ?case
    by (rule control_at_seq_step[OF control_at.SeqLeft[OF SeqLeft.hyps] SeqLeft.prems])
       (use SeqLeft.IH[OF _ c1c subset_trans[OF sub SeqLeft.prems(3)] src1] in blast)
next
  case (SeqRight c2 k n0 c1 r v)
  from SeqRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (n0 + csize c1) = (n2, Statement (n0 + csize c1), E2, K2)"
    and sub: "E2 \<subseteq> E"
    by (rule compile_Seq_rightE)
  have src2: "source_com c2" using SeqRight.prems(4) by simp
  from SeqRight.IH[OF SeqRight.prems(1) c2c subset_trans[OF sub SeqRight.prems(3)] src2]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c2 k (n0 + csize c1) c' v'
          \<and> star (gcstep g) (v, s, stk) (v', s', stk)" by auto
  then obtain v' where v': "control_at \<Pi> p c2 k (n0 + csize c1) c' v'"
    "star (gcstep g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (Seq c1 c2) k n0 c' v'"
    using control_at.SeqRight[OF v'(1)] .
  with fr v'(2) show ?case by blast
next
  case (IfHead i b c1 c2 k n0)
  show ?case by (rule control_at_if_step[OF control_at.IfHead IfHead.prems])
next
  case (IfLeft c1 k n0 r v i b c2)
  from IfLeft.prems(2) obtain n1 E1 K1 where
    c1c: "compile \<Pi> p c1 k (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub1: "E1 \<subseteq> E"
    by (rule compile_If_leftE[OF _ IfLeft.hyps(2)])
  have src1: "source_com c1" using IfLeft.prems(4) by simp
  from IfLeft.IH[OF IfLeft.prems(1) c1c subset_trans[OF sub1 IfLeft.prems(3)] src1]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c1 k (Suc n0) c' v'
          \<and> star (gcstep g) (v, s, stk) (v', s', stk)" by auto
  then obtain v' where v': "control_at \<Pi> p c1 k (Suc n0) c' v'"
    "star (gcstep g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (If i b c1 c2) k n0 c' v'" using control_at.IfLeft[OF v'(1) IfLeft.hyps(2)] .
  with fr v'(2) show ?case by blast
next
  case (IfRight c2 k n0 c1 r v i b)
  from IfRight.prems(2) obtain n2 E2 K2 where
    c2c: "compile \<Pi> p c2 k (Suc n0 + csize c1)
            = (n2, Statement (Suc n0 + csize c1), E2, K2)"
    and sub2: "E2 \<subseteq> E"
    by (rule compile_If_rightE[OF _ IfRight.hyps(2)])
  have src2: "source_com c2" using IfRight.prems(4) by simp
  from IfRight.IH[OF IfRight.prems(1) c2c subset_trans[OF sub2 IfRight.prems(3)] src2]
  have fr: "frs' = frs" and
    "\<exists>v'. control_at \<Pi> p c2 k (Suc n0 + csize c1) c' v'
          \<and> star (gcstep g) (v, s, stk) (v', s', stk)" by auto
  then obtain v' where v': "control_at \<Pi> p c2 k (Suc n0 + csize c1) c' v'"
    "star (gcstep g) (v, s, stk) (v', s', stk)" by blast
  have "control_at \<Pi> p (If i b c1 c2) k n0 c' v'" using control_at.IfRight[OF v'(1) IfRight.hyps(2)]
    .
  with fr v'(2) show ?case by blast
next
  case (IfDone i b c1 j c2 k n0) then show ?case by blast
next
  case (WhileHead i b cW k n0)
  from WhileHead.prems(1)
  have out: "c' = If i b (Seq cW (While i b cW)) (SKIP i)" "s' = s" "frs' = frs"
    by auto
  have "control_at \<Pi> p (While i b cW) k n0 (If i b (Seq cW (While i b cW)) (SKIP i)) (Statement n0)"
    by (rule control_at.WhileUnfolded)
  then show ?case using out by auto
next
  case (WhileUnfolded i b cW k n0)
  have srcif: "source_com (If i b (Seq cW (While i b cW)) (SKIP i))" using WhileUnfolded.prems(4)
    by simp
  show ?case
    by (rule control_at_if_step[OF control_at.WhileUnfolded WhileUnfolded.prems(1-3) srcif])
next
  case (WhileBody cW n0 r v i b k)
  from WhileBody.prems(2) obtain n1 E1 K1 where
    cc: "compile \<Pi> p cW (Statement n0) (Suc n0) = (n1, Statement (Suc n0), E1, K1)"
    and sub: "E1 \<subseteq> E"
    by (rule compile_While_bodyE)
  have srcW: "source_com cW" using WhileBody.prems(4) by simp
  show ?case
    by (rule control_at_seq_step[OF control_at.WhileBody[OF WhileBody.hyps] WhileBody.prems])
       (use WhileBody.IH[OF _ cc subset_trans[OF sub WhileBody.prems(3)] srcW] in blast)
next
  case (WhileDone i b cW k n0) then show ?case by blast
next
  case (CallHead i dst q actuals k n0)
  from CallHead.prems(1) obtain x desc sc v where
    out: "dst = Some x" "special_table q = Some desc" "classify_special desc actuals = Some sc"
         "special_result ev sc s v" "c' = (SKIP i)" "s' = s(x := conv (Some x) v)" "frs' = frs"
    by auto
  have act: "emitted_action (Call i (Some x) q actuals) = Some (EA_Special sc x)"
    using out(2,3) by simp
  have mem: "s' \<in> gedge_step (EA_Special sc x) s" using out(4,6) by auto
  obtain w where "control_at \<Pi> p (Call i (Some x) q actuals) k n0 (SKIP i) w"
      and "star (gcstep g) (Statement n0, s, stk) (w, s', stk)"
    by (rule control_at_base_step[OF control_at.CallHead act
              CallHead.prems(2)[unfolded out(1)] CallHead.prems(3) mem]) auto
  then show ?case using out(1,5,7) by auto
next
  case (CallDone i dst q actuals k n0) then show ?case by blast
next
  case (ReturnHead i e k n0) then show ?case by blast
qed

end

end
