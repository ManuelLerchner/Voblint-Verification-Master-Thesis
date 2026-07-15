theory Control_Simulation
  imports Located_Exec
begin

theorem control_step_simulation:
  assumes compiled:
        "compile Pi lay original n = (n', en, ex, E, C)"
      and edges: "E \<subseteq> edges g"
      and combines: "C \<subseteq> combines g"
      and procedures: "proc_layout_sound Pi lay g"
      and control:
        "control_at Pi lay original n residual v sites"
      and frames: "frames_match (sites @ suffix) frs stk"
      and step:
        "pstep Pi (residual, s, frs) (residual', s', frs')"
  shows "\<exists>v' sites' stk'.
    star (cstep g) (v, s, stk) (v', s', stk') \<and>
    control_at Pi lay original n residual' v' sites' \<and>
    frames_match (sites' @ suffix) frs' stk'"  using control compiled edges combines procedures frames step
proof (induction arbitrary: n' en ex E C suffix frs stk
    residual' s' frs' rule: control_at.induct)
  case Skip
  then show ?case by (elim SkipSE)
next
  case (Assign x a n)
  have source_result:
      "(residual', s', frs') =
       (IMP2_Proc.com.SKIP, s(x := IMP2_Expr.aval a s), frs)"
    using Assign.prems(6)
    by (rule AssignSE) simp
  have shape:
      "n = en \<and> ex = n + 1 \<and>
       E = {(n, EA_Assign x a, n + 1)}"
    using Assign.prems(1) by auto
  have edge: "(n, EA_Assign x a, n + 1) \<in> edges g"
    using Assign.prems(2) shape by blast
  have concrete:
      "cstep g (n, s, stk)
        (n + 1, s(x := IMP2_Expr.aval a s), stk)"
    by (rule cstep_assign[OF edge])
  have run:
      "star (cstep g) (n, s, stk)
        (n + 1, s(x := IMP2_Expr.aval a s), stk)"
    by (rule cstep_star_single[OF concrete])
  have located:
      "control_at Pi lay (IMP2_Proc.com.Assign x a) n
        IMP2_Proc.com.SKIP (n + 1) []"
    by (rule control_at.AssignDone)
  have matched: "frames_match ([] @ suffix) frs stk"
    using Assign.prems(5) by simp
  show ?case
    using source_result run located matched by blast
next
  case AssignDone
  then show ?case by (elim SkipSE)
next
  case (SeqLeft c1 n n1 en1 ex1 E1 C1 c2 residual v sites)
  show ?case
  proof (rule SeqSE[OF SeqLeft.prems(6)])
    assume residual_skip: "residual = IMP2_Proc.com.SKIP"
       and source_result:
         "(residual', s', frs') = (c2, s, frs)"
    obtain n2 en2 ex2 E2 C2 where second:
        "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
      by (cases "compile Pi lay c2 n1") auto
    have parent_edges:
        "E = E1 \<union>
          (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)})
          \<union> E2"
      using SeqLeft.prems(1) SeqLeft.hyps(1) second by simp
    have sub_edges: "E1 \<subseteq> edges g"
      using SeqLeft.prems(2) parent_edges by blast
    obtain stk1 where body_run:
        "star (cstep g) (v, s, stk) (ex1, s, stk1)"
        and body_frames: "frames_match suffix frs stk1"
      using control_finish_simulation[
          OF SeqLeft.hyps(1) sub_edges SeqLeft.hyps(3)
             residual_skip SeqLeft.prems(5)]
      by blast
    have entry: "en2 = n1"
      by (rule compile_entry_eq[OF second])
    have bridge:
        "star (cstep g) (ex1, s, stk1) (en2, s, stk1)"
    proof (cases "ex1 = en2")
      case True
      show ?thesis
        using True star.refl[of "cstep g" "(ex1, s, stk1)"] by simp
    next
      case False
      have edge: "(ex1, EA_Nop, en2) \<in> edges g"
        using SeqLeft.prems(2) parent_edges False by auto
      show ?thesis
        by (rule cstep_star_single, rule cstep_nop[OF edge])
    qed
    have run: "star (cstep g) (v, s, stk) (en2, s, stk1)"
      by (rule star_trans[OF body_run bridge])
    have next_control:
        "control_at Pi lay (IMP2_Proc.com.Seq c1 c2) n c2 n1 []"
      by (rule control_at.SeqRight[OF SeqLeft.hyps(1)])
         (rule control_at_initial[OF SeqLeft.hyps(2)])
    show ?case
      apply (rule exI[of _ en2])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk1])
      using source_result entry run next_control body_frames
      apply simp
      done
  next
    fix inner' t frs1
    assume source_result:
        "(residual', s', frs') =
         (IMP2_Proc.com.Seq inner' c2, t, frs1)"
       and inner_step:
         "pstep Pi (residual, s, frs) (inner', t, frs1)"
    obtain n2 en2 ex2 E2 C2 where second:
        "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
      by (cases "compile Pi lay c2 n1") auto
    have parent_sets:
        "E = E1 \<union>
          (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)})
          \<union> E2 \<and>
         C = C1 \<union> C2"
      using SeqLeft.prems(1) SeqLeft.hyps(1) second by simp
    have sub_edges: "E1 \<subseteq> edges g"
      using SeqLeft.prems(2) parent_sets by blast
    have sub_combines: "C1 \<subseteq> combines g"
      using SeqLeft.prems(3) parent_sets by blast
    obtain v' sites' stk' where run:
        "star (cstep g) (v, s, stk) (v', t, stk')"
        and inner_control:
          "control_at Pi lay c1 n inner' v' sites'"
        and matched:
          "frames_match (sites' @ suffix) frs1 stk'"
      using SeqLeft.IH[
          OF SeqLeft.hyps(1) sub_edges sub_combines
             SeqLeft.prems(4) SeqLeft.prems(5) inner_step]
      by blast
    have next_control:
        "control_at Pi lay (IMP2_Proc.com.Seq c1 c2) n
          (IMP2_Proc.com.Seq inner' c2) v' sites'"
      by (rule control_at.SeqLeft[
            OF SeqLeft.hyps(1) SeqLeft.hyps(2) inner_control])
    show ?case
      using source_result run next_control matched by blast
  qed
next
  case (SeqRight c1 n n1 en1 ex1 E1 C1 c2 residual v sites)
  obtain n2 en2 ex2 E2 C2 where second:
      "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
    by (cases "compile Pi lay c2 n1") auto
  have parent_sets:
      "E = E1 \<union>
        (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)})
        \<union> E2 \<and>
       C = C1 \<union> C2"
    using SeqRight.prems(1) SeqRight.hyps(1) second by simp
  have sub_edges: "E2 \<subseteq> edges g"
    using SeqRight.prems(2) parent_sets by blast
  have sub_combines: "C2 \<subseteq> combines g"
    using SeqRight.prems(3) parent_sets by blast
  obtain v' sites' stk' where run:
      "star (cstep g) (v, s, stk) (v', s', stk')"
      and inner_control:
        "control_at Pi lay c2 n1 residual' v' sites'"
      and matched:
        "frames_match (sites' @ suffix) frs' stk'"
    using SeqRight.IH[
        OF second sub_edges sub_combines SeqRight.prems(4)
           SeqRight.prems(5) SeqRight.prems(6)]
    by blast
  have next_control:
      "control_at Pi lay (IMP2_Proc.com.Seq c1 c2) n
        residual' v' sites'"
    by (rule control_at.SeqRight[
          OF SeqRight.hyps(1) inner_control])
  show ?case
    using run next_control matched by blast
next

  case (IfHead c1 c2 b n)
  obtain n1 en1 ex1 E1 C1 where first:
      "compile Pi lay c1 (n + 1) = (n1, en1, ex1, E1, C1)"
    by (cases "compile Pi lay c1 (n + 1)") auto
  obtain n2 en2 ex2 E2 C2 where second:
      "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
    by (cases "compile Pi lay c2 n1") auto
  have parent_edges:
      "E = insert (ex1, EA_Nop, n2)
            (insert (ex2, EA_Nop, n2)
              (insert (n, EA_Assume b, en1)
                (insert (n, EA_AssumeNot b, en2) (E1 \<union> E2))))"
    using IfHead.prems(1) first second by auto
  show ?case
  proof (rule IfSE[OF IfHead.prems(6)])
    assume guard: "IMP2_Expr.bval b s"
       and source_result: "(residual', s', frs') = (c1, s, frs)"
    have edge: "(n, EA_Assume b, en1) \<in> edges g"
      using IfHead.prems(2) parent_edges by blast
    have run: "star (cstep g) (n, s, stk) (en1, s, stk)"
      by (rule cstep_star_single, rule cstep_assume[OF edge guard])
    have entry: "en1 = n + 1"
      by (rule compile_entry_eq[OF first])
    have branch:
        "control_at Pi lay (IMP2_Proc.com.If b c1 c2) n c1 en1 []"
      apply (rule control_at.IfLeft)
      using control_at_initial[OF IfHead.hyps(1), of Pi lay "n + 1"] entry
      apply simp
      done
    show ?case
      apply (rule exI[of _ en1])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk])
      using source_result run branch IfHead.prems(5)
      apply simp
      done
  next
    assume guard: "\<not> IMP2_Expr.bval b s"
       and source_result: "(residual', s', frs') = (c2, s, frs)"
    have edge: "(n, EA_AssumeNot b, en2) \<in> edges g"
      using IfHead.prems(2) parent_edges by blast
    have run: "star (cstep g) (n, s, stk) (en2, s, stk)"
      by (rule cstep_star_single, rule cstep_assume_not[OF edge guard])
    have entry: "en2 = n1"
      by (rule compile_entry_eq[OF second])
    have branch:
        "control_at Pi lay (IMP2_Proc.com.If b c1 c2) n c2 en2 []"
      apply (rule control_at.IfRight[OF first])
      using control_at_initial[OF IfHead.hyps(2), of Pi lay n1] entry
      apply simp
      done
    show ?case
      apply (rule exI[of _ en2])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk])
      using source_result run branch IfHead.prems(5)
      apply simp
      done
  qed
next
  case (IfLeft c1 n residual v sites b c2)  obtain n1 en1 ex1 E1 C1 where first:
      "compile Pi lay c1 (n + 1) = (n1, en1, ex1, E1, C1)"
    by (cases "compile Pi lay c1 (n + 1)") auto
  obtain n2 en2 ex2 E2 C2 where second:
      "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
    by (cases "compile Pi lay c2 n1") auto
  have parent_sets:
      "E = insert (ex1, EA_Nop, n2)
            (insert (ex2, EA_Nop, n2)
              (insert (n, EA_Assume b, en1)
                (insert (n, EA_AssumeNot b, en2) (E1 \<union> E2))))
       \<and> C = C1 \<union> C2"
    using IfLeft.prems(1) first second by auto
  have sub_edges: "E1 \<subseteq> edges g"
    using IfLeft.prems(2) parent_sets by blast
  have sub_combines: "C1 \<subseteq> combines g"
    using IfLeft.prems(3) parent_sets by blast
  obtain v' sites' stk' where run:
      "star (cstep g) (v, s, stk) (v', s', stk')"
      and inner_control:
        "control_at Pi lay c1 (n + 1) residual' v' sites'"
      and matched:
        "frames_match (sites' @ suffix) frs' stk'"
    using IfLeft.IH[
        OF first sub_edges sub_combines IfLeft.prems(4)
           IfLeft.prems(5) IfLeft.prems(6)]
    by blast
  have next_control:
      "control_at Pi lay (IMP2_Proc.com.If b c1 c2) n
        residual' v' sites'"
    by (rule control_at.IfLeft[OF inner_control])
  show ?case
    using run next_control matched by blast
next
  case (IfRight c1 n n1 en1 ex1 E1 C1 c2 residual v sites b)
  obtain n2 en2 ex2 E2 C2 where second:
      "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
    by (cases "compile Pi lay c2 n1") auto
  have parent_sets:
      "E = insert (ex1, EA_Nop, n2)
            (insert (ex2, EA_Nop, n2)
              (insert (n, EA_Assume b, en1)
                (insert (n, EA_AssumeNot b, en2) (E1 \<union> E2))))
       \<and> C = C1 \<union> C2"
    using IfRight.prems(1) IfRight.hyps(1) second by auto
  have sub_edges: "E2 \<subseteq> edges g"
    using IfRight.prems(2) parent_sets by blast
  have sub_combines: "C2 \<subseteq> combines g"
    using IfRight.prems(3) parent_sets by blast
  obtain v' sites' stk' where run:
      "star (cstep g) (v, s, stk) (v', s', stk')"
      and inner_control:
        "control_at Pi lay c2 n1 residual' v' sites'"
      and matched:
        "frames_match (sites' @ suffix) frs' stk'"
    using IfRight.IH[
        OF second sub_edges sub_combines IfRight.prems(4)
           IfRight.prems(5) IfRight.prems(6)]
    by blast
  have next_control:
      "control_at Pi lay (IMP2_Proc.com.If b c1 c2) n
        residual' v' sites'"
    by (rule control_at.IfRight[
          OF IfRight.hyps(1) inner_control])
  show ?case
    using run next_control matched by blast
next
  case IfDone
  then show ?case by (elim SkipSE)
next
  case (WhileHead body b n)
  have source_result:
      "(residual', s', frs') =
       (IMP2_Proc.com.If b
         (IMP2_Proc.com.Seq body (IMP2_Proc.com.While b body))
         IMP2_Proc.com.SKIP, s, frs)"
    using WhileHead.prems(6)
    by (rule WhileSE) simp
  have run: "star (cstep g) (n, s, stk) (n, s, stk)"
    by (rule star.refl)
  have located:
      "control_at Pi lay (IMP2_Proc.com.While b body) n
        (IMP2_Proc.com.If b
          (IMP2_Proc.com.Seq body (IMP2_Proc.com.While b body))
          IMP2_Proc.com.SKIP) n []"
    by (rule control_at.WhileUnfolded[OF WhileHead.hyps(1)])
  show ?case
    apply (rule exI[of _ n])
    apply (rule exI[of _ "[]"])
    apply (rule exI[of _ stk])
    using source_result run located WhileHead.prems(5)
    apply simp
    done
next
  case (WhileUnfolded body b n)
  obtain n1 body_en body_ex Eb Cb where body_comp:
      "compile Pi lay body (n + 1) =
       (n1, body_en, body_ex, Eb, Cb)"
    by (cases "compile Pi lay body (n + 1)") auto
  have parent_edges:
      "E = insert (body_ex, EA_Nop, n)
            (insert (n, EA_Assume b, body_en)
              (insert (n, EA_AssumeNot b, n1) Eb))"
    using WhileUnfolded.prems(1) body_comp by auto
  show ?case
  proof (rule IfSE[OF WhileUnfolded.prems(6)])
    assume guard: "IMP2_Expr.bval b s"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.Seq body (IMP2_Proc.com.While b body),
           s, frs)"
    have edge: "(n, EA_Assume b, body_en) \<in> edges g"
      using WhileUnfolded.prems(2) parent_edges by blast
    have run:
        "star (cstep g) (n, s, stk) (body_en, s, stk)"
      by (rule cstep_star_single, rule cstep_assume[OF edge guard])
    have entry: "body_en = n + 1"
      by (rule compile_entry_eq[OF body_comp])
    have body_control:
        "control_at Pi lay body (n + 1) body body_en []"
      using control_at_initial[OF WhileUnfolded.hyps(1), of Pi lay "n + 1"]
        entry by simp
    have located:
        "control_at Pi lay (IMP2_Proc.com.While b body) n
          (IMP2_Proc.com.Seq body (IMP2_Proc.com.While b body))
          body_en []"
      by (rule control_at.WhileBody[
            OF WhileUnfolded.hyps(1) body_control])
    show ?case
      apply (rule exI[of _ body_en])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk])
      using source_result run located WhileUnfolded.prems(5)
      apply simp
      done
  next
    assume guard: "\<not> IMP2_Expr.bval b s"
       and source_result:
         "(residual', s', frs') = (IMP2_Proc.com.SKIP, s, frs)"
    have edge: "(n, EA_AssumeNot b, n1) \<in> edges g"
      using WhileUnfolded.prems(2) parent_edges by blast
    have run: "star (cstep g) (n, s, stk) (n1, s, stk)"
      by (rule cstep_star_single, rule cstep_assume_not[OF edge guard])
    have exit: "ex = n1"
      using WhileUnfolded.prems(1) body_comp by auto
    have finished:
        "control_at Pi lay (IMP2_Proc.com.While b body) n
          IMP2_Proc.com.SKIP ex []"
      by (rule control_at.WhileDone[OF WhileUnfolded.prems(1)])
    have located:
        "control_at Pi lay (IMP2_Proc.com.While b body) n
          IMP2_Proc.com.SKIP n1 []"
      using finished exit by simp
    show ?case
      apply (rule exI[of _ n1])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk])
      using source_result run located WhileUnfolded.prems(5)
      apply simp
      done
  qed
next
  case (WhileBody body n residual v sites b)
  obtain n1 body_en body_ex Eb Cb where body_comp:
      "compile Pi lay body (n + 1) =
       (n1, body_en, body_ex, Eb, Cb)"
    by (cases "compile Pi lay body (n + 1)") auto
  have parent_sets:
      "E = insert (body_ex, EA_Nop, n)
            (insert (n, EA_Assume b, body_en)
              (insert (n, EA_AssumeNot b, n1) Eb))
       \<and> C = Cb"
    using WhileBody.prems(1) body_comp by auto
  have sub_edges: "Eb \<subseteq> edges g"
    using WhileBody.prems(2) parent_sets by blast
  have sub_combines: "Cb \<subseteq> combines g"
    using WhileBody.prems(3) parent_sets by blast
  show ?case
  proof (rule SeqSE[OF WhileBody.prems(6)])
    assume residual_skip: "residual = IMP2_Proc.com.SKIP"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.While b body, s, frs)"
    obtain stk1 where body_run:
        "star (cstep g) (v, s, stk) (body_ex, s, stk1)"
        and body_frames: "frames_match suffix frs stk1"
      using control_finish_simulation[
          OF body_comp sub_edges WhileBody.hyps(2)
             residual_skip WhileBody.prems(5)]
      by blast
    have back_edge: "(body_ex, EA_Nop, n) \<in> edges g"
      using WhileBody.prems(2) parent_sets by blast
    have back_run:
        "star (cstep g) (body_ex, s, stk1) (n, s, stk1)"
      by (rule cstep_star_single, rule cstep_nop[OF back_edge])
    have run: "star (cstep g) (v, s, stk) (n, s, stk1)"
      by (rule star_trans[OF body_run back_run])
    have located:
        "control_at Pi lay (IMP2_Proc.com.While b body) n
          (IMP2_Proc.com.While b body) n []"
      by (rule control_at.WhileHead[OF WhileBody.hyps(1)])
    show ?case
      apply (rule exI[of _ n])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk1])
      using source_result run located body_frames
      apply simp
      done
  next
    fix inner' t frs1
    assume source_result:
        "(residual', s', frs') =
         (IMP2_Proc.com.Seq inner' (IMP2_Proc.com.While b body),
          t, frs1)"
       and inner_step:
         "pstep Pi (residual, s, frs) (inner', t, frs1)"
    obtain v' sites' stk' where run:
        "star (cstep g) (v, s, stk) (v', t, stk')"
        and inner_control:
          "control_at Pi lay body (n + 1) inner' v' sites'"
        and matched:
          "frames_match (sites' @ suffix) frs1 stk'"
      using WhileBody.IH[
          OF body_comp sub_edges sub_combines WhileBody.prems(4)
             WhileBody.prems(5) inner_step]
      by blast
    have located:
        "control_at Pi lay (IMP2_Proc.com.While b body) n
          (IMP2_Proc.com.Seq inner' (IMP2_Proc.com.While b body))
          v' sites'"
      by (rule control_at.WhileBody[
            OF WhileBody.hyps(1) inner_control])
    show ?case
      using source_result run located matched by blast
  qed
next
  case WhileDone
  then show ?case by (elim SkipSE)
next
  case (ScopeHead body n)
  have source_result:
      "(residual', s', frs') =
       (IMP2_Proc.com.Seq body (IMP2_Proc.com.Restore),
        enter_state s, Frame s None # frs)"
    using ScopeHead.prems(6)
    by (rule ScopeSE) simp
  obtain n1 body_en body_ex Eb Cb where body_comp:
      "compile Pi lay body (n + 1) =
       (n1, body_en, body_ex, Eb, Cb)"
    by (cases "compile Pi lay body (n + 1)") auto
  have shape:
      "ex = n1 \<and>
       (n, EA_Enter [] [], body_en) \<in> E \<and>
       (n, body_ex, n1, None) \<in> C"
    using ScopeHead.prems(1) body_comp by auto
  have enter_edge:
      "(n, EA_Enter [] [], body_en) \<in> edges g"
    using ScopeHead.prems(2) shape by blast
  have combine:
      "(n, body_ex, n1, None) \<in> combines g"
    using ScopeHead.prems(3) shape by blast
  have concrete:
      "cstep g (n, s, stk)
        (body_en, enter_state s, (n, n1, s) # stk)"
    by (rule cstep.Call[OF enter_edge combine]) (simp add: bind_formals_def)
  have run:
      "star (cstep g) (n, s, stk)
        (body_en, enter_state s, (n, n1, s) # stk)"
    by (rule cstep_star_single[OF concrete])
  have entry: "body_en = n + 1"
    by (rule compile_entry_eq[OF body_comp])
  have body_control:
      "control_at Pi lay body (n + 1) body body_en []"
    using control_at_initial[OF ScopeHead.hyps(1), of Pi lay "n + 1"]
      entry by simp
  have raw_location:
      "control_at Pi lay (IMP2_Proc.com.Scope body) n
        (IMP2_Proc.com.Seq body (IMP2_Proc.com.Restore))
        body_en ([] @ [(n, ex, None)])"
    by (rule control_at.ScopeBody[
          OF ScopeHead.prems(1) body_control])
  have located:
      "control_at Pi lay (IMP2_Proc.com.Scope body) n
        (IMP2_Proc.com.Seq body (IMP2_Proc.com.Restore))
        body_en [(n, n1, None)]"
    using raw_location shape by simp
  have matched:
      "frames_match ([(n, n1, None)] @ suffix) (Frame s None # frs)
        ((n, n1, s) # stk)"
    using ScopeHead.prems(5) by simp
  show ?case
    apply (rule exI[of _ body_en])
    apply (rule exI[of _ "[(n, n1, None)]"])
    apply (rule exI[of _ "(n, n1, s) # stk"])
    using source_result run located matched
    apply simp
    done
next
  case (ScopeBody body n n1 en scope_ex E0 C0 residual v sites)
  obtain body_n body_en body_ex Eb Cb where body_comp:
      "compile Pi lay body (n + 1) =
       (body_n, body_en, body_ex, Eb, Cb)"
    by (cases "compile Pi lay body (n + 1)") auto
  have parent_shape:
      "scope_ex = body_n \<and>
       E = insert (n, EA_Enter [] [], body_en) Eb \<and>
       C = insert (n, body_ex, body_n, None) Cb"
    using ScopeBody.prems(1) ScopeBody.hyps(1) body_comp by auto
  have sub_edges: "Eb \<subseteq> edges g"
    using ScopeBody.prems(2) parent_shape by blast
  have sub_combines: "Cb \<subseteq> combines g"
    using ScopeBody.prems(3) parent_shape by blast
  have frame_assoc:
      "(sites @ [(n, scope_ex, None)]) @ suffix =
       sites @ ([(n, scope_ex, None)] @ suffix)"
    by simp
  show ?case
  proof (rule SeqSE[OF ScopeBody.prems(6)])
    assume residual_skip: "residual = IMP2_Proc.com.SKIP"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.Restore, s, frs)"
    have input_frames:
        "frames_match
          (sites @ ([(n, scope_ex, None)] @ suffix)) frs stk"
      using ScopeBody.prems(5) frame_assoc by simp
    obtain stk1 where body_run:
        "star (cstep g) (v, s, stk) (body_ex, s, stk1)"
        and body_frames:
          "frames_match ([(n, scope_ex, None)] @ suffix) frs stk1"
      using control_finish_simulation[
          OF body_comp sub_edges ScopeBody.hyps(2)
             residual_skip input_frames]
      by blast
    have raw_location:
        "control_at Pi lay (IMP2_Proc.com.Scope body) n
          (IMP2_Proc.com.Restore) body_ex [(n, body_n, None)]"
      by (rule control_at.ScopeRestore[OF body_comp])
    have located:
        "control_at Pi lay (IMP2_Proc.com.Scope body) n
          (IMP2_Proc.com.Restore) body_ex [(n, scope_ex, None)]"
      using raw_location parent_shape by simp
    show ?case
      apply (rule exI[of _ body_ex])
      apply (rule exI[of _ "[(n, scope_ex, None)]"])
      apply (rule exI[of _ stk1])
      using source_result body_run located body_frames
      apply simp
      done
  next
    fix inner' t frs1
    assume source_result:
        "(residual', s', frs') =
         (IMP2_Proc.com.Seq inner' (IMP2_Proc.com.Restore),
          t, frs1)"
       and inner_step:
         "pstep Pi (residual, s, frs) (inner', t, frs1)"
    have input_frames:
        "frames_match
          (sites @ ([(n, scope_ex, None)] @ suffix)) frs stk"
      using ScopeBody.prems(5) frame_assoc by simp
    obtain v' inner_sites stk' where run:
        "star (cstep g) (v, s, stk) (v', t, stk')"
        and inner_control:
          "control_at Pi lay body (n + 1) inner' v' inner_sites"
        and matched:
          "frames_match
            (inner_sites @ ([(n, scope_ex, None)] @ suffix))
            frs1 stk'"
      using ScopeBody.IH[
          OF body_comp sub_edges sub_combines ScopeBody.prems(4)
             input_frames inner_step]
      by blast
    have raw_location:
        "control_at Pi lay (IMP2_Proc.com.Scope body) n
          (IMP2_Proc.com.Seq inner' (IMP2_Proc.com.Restore))
          v' (inner_sites @ [(n, scope_ex, None)])"
      by (rule control_at.ScopeBody[
            OF ScopeBody.hyps(1) inner_control])
    have output_frames:
        "frames_match
          ((inner_sites @ [(n, scope_ex, None)]) @ suffix)
          frs1 stk'"
      using matched by simp
    show ?case
      using source_result run raw_location output_frames by blast
  qed
next
  case (ScopeRestore body n body_n body_en body_ex Eb Cb)
  have parent_shape:
      "ex = body_n \<and>
       (n, body_ex, body_n, None) \<in> C"
    using ScopeRestore.prems(1) ScopeRestore.hyps(1) by auto
  have combine: "(n, body_ex, body_n, None) \<in> combines g"
    using ScopeRestore.prems(3) parent_shape by blast
  show ?case
  proof (rule RestoreSE[OF ScopeRestore.prems(6)])
    fix saved d outer
    assume source_frames: "frs = Frame saved d # outer"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.SKIP,
           combine_assign d (s ret_var) (IMP2_Globals.combine_states saved s),
           outer)"
    have stack_shape:
        "\<exists>stk0.
          stk = (n, body_n, saved) # stk0 \<and>
          d = None \<and>
          frames_match suffix outer stk0"
      using ScopeRestore.prems(5) source_frames
      by (cases stk) auto
    then obtain stk0 where concrete_stack:
        "stk = (n, body_n, saved) # stk0"
        and d_none: "d = None"
        and outer_frames: "frames_match suffix outer stk0"
      by blast
    have concrete:
        "cstep g (body_ex, s, stk)
          (body_n, IMP2_Globals.combine_states saved s, stk0)"
      unfolding concrete_stack
      by (rule cstep.Return[OF combine, simplified])
    have run:
        "star (cstep g) (body_ex, s, stk)
          (body_n, IMP2_Globals.combine_states saved s, stk0)"
      by (rule cstep_star_single[OF concrete])
    have finished:
        "control_at Pi lay (IMP2_Proc.com.Scope body) n
          IMP2_Proc.com.SKIP ex []"
      by (rule control_at.ScopeDone[OF ScopeRestore.prems(1)])
    have located:
        "control_at Pi lay (IMP2_Proc.com.Scope body) n
          IMP2_Proc.com.SKIP body_n []"
      using finished parent_shape by simp
    have result_cmd: "residual' = IMP2_Proc.com.SKIP"
      and result_store:
        "s' = IMP2_Globals.combine_states saved s"
      and result_frames: "frs' = outer"
      using source_result d_none by simp_all
    show ?case
      apply (rule exI[of _ body_n])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk0])
      apply (intro conjI)
       apply (subst result_store)
       apply (rule run)
      using result_cmd located apply simp
      using result_frames outer_frames apply simp
      done
  qed
next
  case ScopeDone
  then show ?case by (elim SkipSE)
next
  case (CallHead dst p actuals n)
  obtain decl where decl: "Pi p = Some decl"
     and arity: "length actuals = length (formals decl)"
     and distinct_formals: "distinct (formals decl)"
     and return_ok: "(\<exists>x. dst = Some x) \<longrightarrow> (\<exists>y. result decl = Some y)"
     and source_result:
       "(residual', s', frs') =
        (IMP2_Proc.com.Seq (with_result (body decl) (result decl))
           (IMP2_Proc.com.Restore),
         bind_formals (formals decl) (map (\<lambda>e. IMP2_Expr.aval e s) actuals) (enter_state s),
         Frame s dst # frs)"
    using CallHead.prems(6)
    by auto
  have source_pi: "source_pi Pi"
    using CallHead.prems(4)
    unfolding proc_layout_sound_def
    by (elim conjE) assumption
  have source_body: "source_com (with_result (body decl) (result decl))"
    using source_pi decl unfolding source_pi_def by auto
  have layout_complete:
      "\<forall>p decl. Pi p = Some decl \<longrightarrow>
        (\<exists>en ex Ns Ep Cp.
          lay p = Some (en, ex, Ns, Ep, Cp))"
    using CallHead.prems(4)
    unfolding proc_layout_sound_def
    by (elim conjE) assumption
  obtain proc_en proc_ex Ns Ep Cp where lookup:
      "lay p = Some (proc_en, proc_ex, Ns, Ep, Cp)"
    using layout_complete[rule_format, OF decl] by blast
  have layout_fragments:
      "\<forall>p decl en ex Ns Ep Cp.
        Pi p = Some decl \<longrightarrow>
        lay p = Some (en, ex, Ns, Ep, Cp) \<longrightarrow>
        (\<exists>finish.
          compile Pi lay (with_result (body decl) (result decl)) en =
            (finish, en, ex, Ep, Cp)) \<and>
        Ep \<subseteq> edges g \<and> Cp \<subseteq> combines g"
    using CallHead.prems(4)
    unfolding proc_layout_sound_def
    by (elim conjE) assumption
  obtain finish where body_comp:
      "compile Pi lay (with_result (body decl) (result decl)) proc_en =
       (finish, proc_en, proc_ex, Ep, Cp)"
    using layout_fragments[rule_format, OF decl lookup] by blast
  have call_shape:
      "(n, EA_Enter (formals decl) actuals, proc_en) \<in> E \<and>
       (n, proc_ex, n + 1, dst) \<in> C"
    using CallHead.prems(1) decl lookup by auto
  have enter_edge:
      "(n, EA_Enter (formals decl) actuals, proc_en) \<in> edges g"
    using CallHead.prems(2) call_shape by blast
  have combine:
      "(n, proc_ex, n + 1, dst) \<in> combines g"
    using CallHead.prems(3) call_shape by blast
  have concrete:
      "cstep g (n, s, stk)
        (proc_en,
         bind_formals (formals decl) (map (\<lambda>e. IMP2_Expr.aval e s) actuals) (enter_state s),
         (n, n + 1, s) # stk)"
    by (rule cstep.Call[OF enter_edge combine])
       (simp add: bind_formals_def)
  have run:
      "star (cstep g) (n, s, stk)
        (proc_en,
         bind_formals (formals decl) (map (\<lambda>e. IMP2_Expr.aval e s) actuals) (enter_state s),
         (n, n + 1, s) # stk)"
    by (rule cstep_star_single[OF concrete])
  have body_control:
      "control_at Pi lay (with_result (body decl) (result decl)) proc_en (with_result (body decl) (result decl)) proc_en []"
    by (rule control_at_initial[OF source_body])
  have raw_location:
      "control_at Pi lay (IMP2_Proc.com.Call dst p actuals) n
        (IMP2_Proc.com.Seq (with_result (body decl) (result decl))
           (IMP2_Proc.com.Restore))
        proc_en ([] @ [(n, n + 1, dst)])"
    by (rule control_at.CallBody[
          OF decl lookup body_comp body_control])
  have located:
      "control_at Pi lay (IMP2_Proc.com.Call dst p actuals) n
        (IMP2_Proc.com.Seq (with_result (body decl) (result decl))
           (IMP2_Proc.com.Restore))
        proc_en [(n, n + 1, dst)]"
    using raw_location by simp
  have matched:
      "frames_match ([(n, n + 1, dst)] @ suffix) (Frame s dst # frs)
        ((n, n + 1, s) # stk)"
    using CallHead.prems(5) by simp
  show ?case
    using source_result run located matched by blast
next
  case (CallBody p decl proc_en proc_ex Ns Ep Cp n1 body_en Eb Cb residual v sites dst actuals n)
  have proc_sound:
      "(\<exists>finish.
         compile Pi lay (with_result (body decl) (result decl)) proc_en =
           (finish, proc_en, proc_ex, Ep, Cp)) \<and>
       Ep \<subseteq> edges g \<and> Cp \<subseteq> combines g"
    using CallBody.prems(4) CallBody.hyps(1,2)
    unfolding proc_layout_sound_def by blast
  then obtain finish where canonical:
      "compile Pi lay (with_result (body decl) (result decl)) proc_en =
       (finish, proc_en, proc_ex, Ep, Cp)"
      and proc_edges: "Ep \<subseteq> edges g"
      and proc_combines: "Cp \<subseteq> combines g"
    by blast
  have output_eq: "Eb = Ep \<and> Cb = Cp"
    using CallBody.hyps(3) canonical by simp
  have sub_edges: "Eb \<subseteq> edges g"
    using proc_edges output_eq by simp
  have sub_combines: "Cb \<subseteq> combines g"
    using proc_combines output_eq by simp
  have frame_assoc:
      "(sites @ [(n, n + 1, dst)]) @ suffix =
       sites @ ([(n, n + 1, dst)] @ suffix)"
    by simp
  show ?case
  proof (rule SeqSE[OF CallBody.prems(6)])
    assume residual_skip: "residual = IMP2_Proc.com.SKIP"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.Restore, s, frs)"
    have input_frames:
        "frames_match
          (sites @ ([(n, n + 1, dst)] @ suffix)) frs stk"
      using CallBody.prems(5) frame_assoc by simp
    obtain stk1 where body_run:
        "star (cstep g) (v, s, stk) (proc_ex, s, stk1)"
        and body_frames:
          "frames_match ([(n, n + 1, dst)] @ suffix) frs stk1"
      using control_finish_simulation[
          OF CallBody.hyps(3) sub_edges CallBody.hyps(4)
             residual_skip input_frames]
      by blast
    have located:
        "control_at Pi lay (IMP2_Proc.com.Call dst p actuals) n
          (IMP2_Proc.com.Restore) proc_ex [(n, n + 1, dst)]"
      using CallBody.hyps(1,2)
      by (rule control_at.CallRestore)
    show ?case
      apply (rule exI[of _ proc_ex])
      apply (rule exI[of _ "[(n, n + 1, dst)]"])
      apply (rule exI[of _ stk1])
      using source_result body_run located body_frames
      apply simp
      done
  next
    fix inner' t frs1
    assume source_result:
        "(residual', s', frs') =
         (IMP2_Proc.com.Seq inner' (IMP2_Proc.com.Restore),
          t, frs1)"
       and inner_step:
         "pstep Pi (residual, s, frs) (inner', t, frs1)"
    have input_frames:
        "frames_match
          (sites @ ([(n, n + 1, dst)] @ suffix)) frs stk"
      using CallBody.prems(5) frame_assoc by simp
    obtain v' inner_sites stk' where run:
        "star (cstep g) (v, s, stk) (v', t, stk')"
        and inner_control:
          "control_at Pi lay (with_result (body decl) (result decl)) proc_en inner' v' inner_sites"
        and matched:
          "frames_match
            (inner_sites @ ([(n, n + 1, dst)] @ suffix))
            frs1 stk'"
      using CallBody.IH[
          OF CallBody.hyps(3) sub_edges sub_combines CallBody.prems(4)
             input_frames inner_step]
      by blast
    have raw_location:
        "control_at Pi lay (IMP2_Proc.com.Call dst p actuals) n
          (IMP2_Proc.com.Seq inner' (IMP2_Proc.com.Restore))
          v' (inner_sites @ [(n, n + 1, dst)])"
      by (rule control_at.CallBody[
            OF CallBody.hyps(1) CallBody.hyps(2)
               CallBody.hyps(3) inner_control])
    have output_frames:
        "frames_match
          ((inner_sites @ [(n, n + 1, dst)]) @ suffix)
          frs1 stk'"
      using matched by simp
    show ?case
      using source_result run raw_location output_frames by blast
  qed

next
  case (CallRestore p decl proc_en proc_ex Ns Ep Cp dst actuals n)
  have combine_dst:
      "(n, proc_ex, n + 1, dst) \<in> combines g"
    using CallRestore.prems(1,3) CallRestore.hyps(1,2) by auto
  have located:
      "control_at Pi lay (IMP2_Proc.com.Call dst p actuals) n
        IMP2_Proc.com.SKIP (n + 1) []"
    using CallRestore.hyps(1,2) by (rule control_at.CallDone)
  show ?case
  proof (rule RestoreSE[OF CallRestore.prems(6)])
    fix saved d outer
    assume source_frames: "frs = Frame saved d # outer"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.SKIP,
           combine_assign d (s ret_var) (IMP2_Globals.combine_states saved s),
           outer)"
    have stack_shape:
        "\<exists>stk0.
          stk = (n, n + 1, saved) # stk0 \<and>
          d = dst \<and>
          frames_match suffix outer stk0"
      using CallRestore.prems(5) source_frames
      by (cases stk) auto
    then obtain stk0 where concrete_stack:
        "stk = (n, n + 1, saved) # stk0"
        and d_eq: "d = dst"
        and outer_frames: "frames_match suffix outer stk0"
      by blast
    have concrete:
        "cstep g (proc_ex, s, stk)
          (n + 1,
           combine_assign dst (s ret_var)
             (IMP2_Globals.combine_states saved s),
           stk0)"
      unfolding concrete_stack
      by (rule cstep.Return[OF combine_dst])
    have run:
        "star (cstep g) (proc_ex, s, stk)
          (n + 1,
           combine_assign dst (s ret_var)
             (IMP2_Globals.combine_states saved s),
           stk0)"
      by (rule cstep_star_single[OF concrete])
    have result_cmd: "residual' = IMP2_Proc.com.SKIP"
      and result_store:
        "s' = combine_assign dst (s ret_var)
                (IMP2_Globals.combine_states saved s)"
      and result_frames: "frs' = outer"
      using source_result d_eq by simp_all
    show ?thesis
      apply (rule exI[of _ "n + 1"])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk0])
      apply (intro conjI)
       apply (subst result_store)
       apply (rule run)
      using result_cmd located apply simp
      using result_frames outer_frames apply simp
      done
  qed
next
  case CallDone
  then show ?case by (elim SkipSE)
qed

theorem concrete_program_step_match:
  assumes wf: "wf_compile_input Pi ps main"
      and matched: "concrete_program_match Pi ps main src cf"
      and step: "pstep Pi src src'"
  shows "\<exists>cf'.
    star (cstep (compile_prog Pi ps main)) cf cf' \<and>
    concrete_program_match Pi ps main src' cf'"
proof -
  obtain residual s frs where src: "src = (residual, s, frs)"
    by (cases src) auto
  obtain residual' s' frs' where src':
      "src' = (residual', s', frs')"
    by (cases src') auto
  obtain v t stk where cf: "cf = (v, t, stk)"
    by (cases cf) auto
  obtain nproc lay Eproc Cproc nend main_en main_ex Emain Cmain sites
    where store: "s = t"
      and procs:
        "compile_procs_list Pi ps (\<lambda>_. None) 0 =
          (nproc, lay, Eproc, Cproc)"
      and main_comp:
        "compile Pi lay main nproc =
          (nend, main_en, main_ex, Emain, Cmain)"
      and control:
        "control_at Pi lay main nproc residual v sites"
      and frames: "frames_match sites frs stk"
    using matched
    unfolding concrete_program_match_def src cf
    by auto
  have edge_sets:
      "edges (compile_prog Pi ps main) = Eproc \<union> Emain"
    by (rule compile_prog_sets(1)[OF procs main_comp])
  have combine_sets:
      "combines (compile_prog Pi ps main) = Cproc \<union> Cmain"
    by (rule compile_prog_sets(2)[OF procs main_comp])
  have main_edges:
      "Emain \<subseteq> edges (compile_prog Pi ps main)"
    unfolding edge_sets by blast
  have main_combines:
      "Cmain \<subseteq> combines (compile_prog Pi ps main)"
    unfolding combine_sets by blast
  have layout_sound:
      "proc_layout_sound Pi lay (compile_prog Pi ps main)"
  proof (unfold proc_layout_sound_def, intro conjI)
    show "source_pi Pi"
      using wf unfolding wf_compile_input_def by blast
    show "\<forall>p decl. Pi p = Some decl \<longrightarrow>
      (\<exists>en ex Ns Ep Cp.
        lay p = Some (en, ex, Ns, Ep, Cp))"
    proof (intro allI impI)
      fix p decl
      assume decl: "Pi p = Some decl"
      show "\<exists>en ex Ns Ep Cp.
        lay p = Some (en, ex, Ns, Ep, Cp)"
        using compile_procs_list_complete[OF wf procs decl] .
    qed
    show "\<forall>p decl en ex Ns Ep Cp.
      Pi p = Some decl \<longrightarrow>
      lay p = Some (en, ex, Ns, Ep, Cp) \<longrightarrow>
      (\<exists>finish.
        compile Pi lay (with_result (body decl) (result decl)) en = (finish, en, ex, Ep, Cp)) \<and>
      Ep \<subseteq> edges (compile_prog Pi ps main) \<and>
      Cp \<subseteq> combines (compile_prog Pi ps main)"
    proof (intro allI impI)
      fix p decl en ex Ns Ep Cp
      assume decl: "Pi p = Some decl"
      assume lookup: "lay p = Some (en, ex, Ns, Ep, Cp)"
      obtain finish where compiled_body:
          "compile Pi lay (with_result (body decl) (result decl)) en = (finish, en, ex, Ep, Cp)"
        using compile_procs_list_body[OF wf procs decl lookup] by blast
      have fragment: "Ep \<subseteq> Eproc \<and> Cp \<subseteq> Cproc"
        by (rule compile_procs_list_fragment[OF procs lookup])
      show "(\<exists>finish.
          compile Pi lay (with_result (body decl) (result decl)) en = (finish, en, ex, Ep, Cp)) \<and>
          Ep \<subseteq> edges (compile_prog Pi ps main) \<and>
          Cp \<subseteq> combines (compile_prog Pi ps main)"
        using compiled_body fragment edge_sets combine_sets by blast
    qed
  qed
   
  have source_step:
      "pstep Pi (residual, s, frs) (residual', s', frs')"
    using step unfolding src src' .
  have frames_suffix: "frames_match (sites @ []) frs stk"
    using frames by simp
  obtain v' sites' stk' where run:
      "star (cstep (compile_prog Pi ps main))
        (v, s, stk) (v', s', stk')"
      and control':
        "control_at Pi lay main nproc residual' v' sites'"
      and frames': "frames_match sites' frs' stk'"
    using control_step_simulation[
      OF main_comp main_edges main_combines layout_sound
        control frames_suffix source_step]
    by auto
  show ?thesis
  proof (rule exI[where x = "(v', s', stk')"], intro conjI)
    show "star (cstep (compile_prog Pi ps main)) cf (v', s', stk')"
      using run store unfolding cf by simp
    show "concrete_program_match Pi ps main src' (v', s', stk')"
      unfolding concrete_program_match_def src'
      using procs main_comp control' frames'
      by auto
  qed
qed

end
