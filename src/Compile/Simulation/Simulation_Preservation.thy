theory Simulation_Preservation
  imports Simulation_Relation Compile_Invariants
begin

section \<open>Every source step is matched by the graph\<close>

text \<open>
  The result the session exists for: if \<open>csim\<close> holds and the source takes one step, the graph
  can follow and \<open>csim\<close> holds again (\<open>csim_step\<close>); hence the same for a whole run
  (\<open>csim_star\<close>).  A source redex is one of four things --- a call, a return initiation, a
  return already in progress, or an ordinary step inside the activation --- and there is one
  completion theorem per case, which \<open>csim_step\<close> dispatches to.

  \<open>procs_embedded\<close> is the static side condition the first two share: every declared
  procedure's body has been compiled into this graph, with its entry and exit wiring present.
  It is deliberately not part of \<open>csim\<close>, which says only how two configurations correspond,
  so that the returning phase can proceed without it.  \<open>procs_embedded_compile_prog\<close>
  discharges it for any graph \<^const>\<open>compile_prog\<close> actually produced.
\<close>

definition procs_embedded :: "proc_table \<Rightarrow> cfg \<Rightarrow> bool" where
  "procs_embedded \<Pi> g \<longleftrightarrow>
     (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow>
        (\<exists>k n n' en E K.
           compile \<Pi> p (body decl) k n = (n', en, E, K)
         \<and> E \<subseteq> intra g \<and> K \<subseteq> calls g
         \<and> (FunctionEntry p, EA_Body p, en) \<in> intra g
         \<and> (falls_through (body decl) \<longrightarrow>
              (k, EA_Ret None p, FunctionResult p) \<in> intra g)
         \<and> source_com (body decl) \<and> special_table p = None))"

lemma procs_embedded_proc:
  assumes "procs_embedded \<Pi> g" and "\<Pi> p = Some decl"
  obtains k n n' en E K where
    "compile \<Pi> p (body decl) k n = (n', en, E, K)"
    "E \<subseteq> intra g" "K \<subseteq> calls g"
    "(FunctionEntry p, EA_Body p, en) \<in> intra g"
    "falls_through (body decl) \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g"
    "source_com (body decl)" "special_table p = None"
  using assms unfolding procs_embedded_def by blast

lemma procs_embedded_source_com:
  assumes "procs_embedded \<Pi> g" and "\<Pi> p = Some decl"
  shows "source_com (body decl)"
  using assms by (blast elim: procs_embedded_proc)

text \<open>A declared procedure's name is never one \<^const>\<open>special_table\<close> also classifies:
  \<open>procs_embedded\<close> bundles this disjointness alongside compiler-correctness so a declared call
  and a special call are always distinguishable without a separate well-formedness premise.\<close>
lemma procs_embedded_special_table_none:
  assumes "procs_embedded \<Pi> g" and "\<Pi> p = Some decl"
  shows "special_table p = None"
  using assms by (blast elim: procs_embedded_proc)

text \<open>Everything needed to start a fresh activation of \<open>p\<close>, in one step: the certificate its
  \<open>csim\<close> layer will carry, the initial location of its body, and the \<^term>\<open>EA_Nop\<close> edge from
  \<^term>\<open>FunctionEntry p\<close> that reaches that location.  Call preservation is otherwise the same
  destructuring written out by hand.\<close>
lemma procs_embedded_activation:
  assumes pc: "procs_embedded \<Pi> g" and decl: "\<Pi> p = Some decl"
  obtains k n en where
    "compiled_at \<Pi> g p (body decl) k n"
    "control_at \<Pi> p (body decl) k n (body decl) en"
    "(FunctionEntry p, EA_Body p, en) \<in> intra g"
    "source_com (body decl)"
proof -
  obtain k n n' en E K where
    cb: "compile \<Pi> p (body decl) k n = (n', en, E, K)"
      and Esub: "E \<subseteq> intra g" and Ksub: "K \<subseteq> calls g"
      and entry: "(FunctionEntry p, EA_Body p, en) \<in> intra g"
      and ex: "falls_through (body decl) \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g"
      and src: "source_com (body decl)"
      and sp: "special_table p = None"
    by (rule procs_embedded_proc[OF pc decl])
  have cacc: "compiled_at \<Pi> g p (body decl) k n"
    by (rule compiled_atI[OF decl refl cb Esub Ksub ex])
  have ctrl: "control_at \<Pi> p (body decl) k n (body decl) en"
    using control_at_initial[OF src, of \<Pi> p k n, folded compile_entry[OF cb]] .
  from cacc ctrl entry src show ?thesis by (rule that)
qed

section \<open>Frame-stack plumbing\<close>

text \<open>A single \<^const>\<open>pstep\<close> touches only the head region of the frame stack, so a bottom
  segment \<open>extra\<close> rides along unchanged when the active part \<open>frs\<close> is non-empty.  This
  bridges the \<open>Nested\<close> snoc (the inner step threads all frames) to the induction hypothesis
  (stated on the inner frames alone).\<close>
lemma pstep_frame_restrict:
  "pstep gs \<Pi> (c, s, fr) (c', s', frs') \<Longrightarrow> fr = frs @ extra \<Longrightarrow> frs \<noteq> [] \<Longrightarrow>
   \<exists>frs''. frs' = frs'' @ extra \<and> pstep gs \<Pi> (c, s, frs) (c', s', frs'')"
proof (induction "(c, s, fr)" "(c', s', frs')"
       arbitrary: c s fr frs c' s' frs' rule: pstep.induct)
  case (Seq2 c1 s1 f1 c1' s1' f1' c2 frs)
  from Seq2.hyps(2)[OF Seq2.prems] obtain frs'' where
    ih: "f1' = frs'' @ extra" "pstep gs \<Pi> (c1, s1, frs) (c1', s1', frs'')" by blast
  show ?case
    by (rule exI[of _ frs'']) (use ih in auto)
next
  case (Call p decl actuals dst vals callee s1 frs0 frs)
  then show ?case by auto
next
  case (RestoreStep s1 fr0 dst frs0 frs)
  from RestoreStep.prems obtain frs1 where "frs = Frame fr0 dst # frs1" "frs0 = frs1 @ extra"
    by (auto simp: Cons_eq_append_conv)
  then show ?case by auto
next
  case (UnwindAct s1 fr0 dst frs0 frs)
  from UnwindAct.prems obtain frs1 where "frs = Frame fr0 dst # frs1" "frs0 = frs1 @ extra"
    by (auto simp: Cons_eq_append_conv)
  then show ?case by auto
qed auto

text \<open>Unlike \<open>pstep_frame_restrict\<close> this needs no non-empty active stack: a call-headed
  command never heads with \<^const>\<open>SKIP\<close> / \<^const>\<open>Restore\<close> / \<^const>\<open>Unwind\<close>, so no pop can
  fire.\<close>
lemma pstep_call_frame_restrict:
  "pstep gs \<Pi> (c, s, fr) (c', s', frs') \<Longrightarrow> head_call c \<Longrightarrow> fr = frs @ extra \<Longrightarrow>
   \<exists>frs''. frs' = frs'' @ extra \<and> pstep gs \<Pi> (c, s, frs) (c', s', frs'')"
proof (induction "(c, s, fr)" "(c', s', frs')"
       arbitrary: c s fr frs c' s' frs' rule: pstep.induct)
  case (Seq2 c1 s1 f1 c1' s1' f1' c2 frs)
  from Seq2.prems(1) have "head_call c1" by simp
  from Seq2.hyps(2)[OF this Seq2.prems(2)] obtain frs'' where
    ih: "f1' = frs'' @ extra" "pstep gs \<Pi> (c1, s1, frs) (c1', s1', frs'')" by blast
  show ?case by (rule exI[of _ frs'']) (use ih in auto)
next
  case (Call p decl actuals dst vals callee s1 frs0 frs)
  then show ?case by auto
qed auto

text \<open>The CFG dual: a \<^const>\<open>cstep\<close> also touches only the head of the stack, so an extra
  bottom segment rides along --- with no non-emptiness needed, since the return step already
  requires a non-empty stack.\<close>
lemma cstep_frame_extend:
  "cstep gs g (u, s, stk) (u', s', stk') \<Longrightarrow>
   cstep gs g (u, s, stk @ E) (u', s', stk' @ E)"
  by (erule cstep.cases) auto

lemma cstep_star_frame_extend:
  assumes "star (cstep gs g) c c'"
  shows "star (cstep gs g) (fst c, fst (snd c), snd (snd c) @ E)
                        (fst c', fst (snd c'), snd (snd c') @ E)"
  using assms
proof (induction rule: star.induct)
  case (refl a) show ?case by simp
next
  case (step a b c)
  obtain ua sa stka where a: "a = (ua, sa, stka)" by (cases a)
  obtain ub sb stkb where b: "b = (ub, sb, stkb)" by (cases b)
  from step.hyps(1) a b have "cstep gs g (ua, sa, stka) (ub, sb, stkb)" by simp
  hence "cstep gs g (ua, sa, stka @ E) (ub, sb, stkb @ E)" by (rule cstep_frame_extend)
  with step.IH a b show ?case by (auto intro: star.step)
qed

text \<open>The \<open>Nested\<close> step-inversion rule: stepping a wrapped activation
  \<^term>\<open>Seq inner Restore\<close> is stepping \<open>inner\<close>, provided \<open>inner\<close> has neither completed nor
  begun to unwind (either of which would relocate rather than step).\<close>
lemma pstep_seq_after_seq_restore:
  assumes step: "pstep gs \<Pi> (seq_after (Seq inner Restore) afters, s, frs) src'"
      and nsk: "inner \<noteq> SKIP" and nunw: "inner \<noteq> Unwind"
  obtains inner' s' fz where
    "src' = (seq_after (Seq inner' Restore) afters, s', fz)"
    "pstep gs \<Pi> (inner, s, frs) (inner', s', fz)"
proof -
  obtain h' s' fz where
    src': "src' = (seq_after h' afters, s', fz)"
      and hstep: "pstep gs \<Pi> (Seq inner Restore, s, frs) (h', s', fz)"
    by (rule pstep_seq_after_headE[OF step]) auto
  from hstep nsk nunw obtain inner' where
    "h' = Seq inner' Restore" "pstep gs \<Pi> (inner, s, frs) (inner', s', fz)"
    by auto
  with src' show ?thesis using that by blast
qed

section \<open>Call preservation\<close>

text \<open>
  A source \<^const>\<open>Call\<close> at the head of the active residual is matched by two \<^const>\<open>cstep\<close>s
  --- the call edge to \<^term>\<open>FunctionEntry q\<close> and the \<^term>\<open>EA_Body\<close> edge to the callee body
  --- and adds exactly one \<open>Nested\<close> layer: the callee body becomes a fresh \<open>Base\<close> activation
  and the caller resumes at \<^term>\<open>seq_after SKIP afters\<close>.  Everything the callee needs comes
  from the single \<^const>\<open>procs_embedded\<close> certificate.
\<close>
lemma csim_call_base:
  assumes pc: "procs_embedded \<Pi> g"
      and loc: "control_at \<Pi> p c0 kk n (seq_after (Call dst q actuals) afters) v"
      and cacc: "compiled_at \<Pi> g p c0 kk n"
      and decl: "\<Pi> q = Some decl"
  shows "\<exists>cfg'. star (cstep gs g) (v, s, [])  cfg'
              \<and> csim \<Pi> g (seq_after (Seq (body decl) Restore) afters,
                          bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals)
                            (enter_state gs s),
                          [Frame s dst]) cfg'"
proof -
  let ?callee =
    "bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state gs s)"
  have spNone: "special_table q = None" by (rule procs_embedded_special_table_none[OF pc decl])
  from cacc obtain n' en E K where comp: "compile \<Pi> p c0 kk n = (n', en, E, K)"
      and Ksub: "K \<subseteq> calls g" by blast
  from control_at_seq_after_call_edge[OF loc refl comp spNone] obtain j w where
    vk: "v = Statement j"
    and edgeK: "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
                 FunctionEntry q, w) \<in> K"
    and callerSKIP: "control_at \<Pi> p c0 kk n (seq_after SKIP afters) w" by blast
  have edge: "(Statement j, CallEdge dst (formals decl) actuals, FunctionEntry q, w)
                \<in> calls g" using edgeK Ksub by (auto simp: decl)
  have cstep1: "cstep gs g (Statement j, s, [])
           (FunctionEntry q, call_enter gs (CallEdge dst (formals decl) actuals) s,
            [(w, dst, s)])" by (rule cstep.Call[OF edge])
  have ce: "call_enter gs (CallEdge dst (formals decl) actuals) s = ?callee"
    by (rule call_enter_CallEdge)
  obtain kq m en_q where
    caccq: "compiled_at \<Pi> g q (body decl) kq m"
      and ctrlq: "control_at \<Pi> q (body decl) kq m (body decl) en_q"
      and entry: "(FunctionEntry q, EA_Body q, en_q) \<in> intra g"
    by (rule procs_embedded_activation[OF pc decl])
  have cstep2: "cstep gs g (FunctionEntry q, ?callee, [(w, dst, s)])
                        (en_q, ?callee, [(w, dst, s)])"
    using cstep_body[OF entry] .
  have star: "star (cstep gs g) (v, s, []) (en_q, ?callee, [(w, dst, s)])"
    using cstep1[unfolded ce] cstep2 vk by (simp add: star.step)
  have baseCallee: "csim \<Pi> g (body decl, ?callee, []) (en_q, ?callee, [])"
    by (rule csim.Base[OF ctrlq caccq])
  have "csim \<Pi> g (seq_after (Seq (body decl) Restore) afters, ?callee, [] @ [Frame s dst])
                 (en_q, ?callee, [] @ [(w, dst, s)])"
    by (rule csim.Nested[OF baseCallee callerSKIP cacc])
  then have "csim \<Pi> g (seq_after (Seq (body decl) Restore) afters, ?callee, [Frame s dst])
                      (en_q, ?callee, [(w, dst, s)])" by simp
  with star show ?thesis by blast
qed

theorem csim_call_completion:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> procs_embedded \<Pi> g \<Longrightarrow> head_call c \<Longrightarrow>
   pstep gs \<Pi> (c, s, frs) src' \<Longrightarrow>
   \<exists>cfg'. star (cstep gs g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
proof (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c s frs v t stk src' rule: csim.induct)
  case (Base p c0 kk n cc vv ss)
  from head_call_seq_after_form[OF Base.prems(2)] obtain dst q actuals afters where
    ceq: "cc = seq_after (Call dst q actuals) afters" and spNone: "special_table q = None"
    by blast
  have step: "pstep gs \<Pi> (seq_after (Call dst q actuals) afters, ss, []) src'"
    using Base.prems(3) ceq by simp
  have w1: "Call dst q actuals \<noteq> SKIP" by simp
  have w2: "Call dst q actuals \<noteq> Unwind" by simp
  obtain h' s' fz where
    src': "src' = (seq_after h' afters, s', fz)"
      and pcall: "pstep gs \<Pi> (Call dst q actuals, ss, []) (h', s', fz)"
    by (rule pstep_seq_after_headE[OF step w1 w2])
  from pcall spNone obtain decl where
    qdecl: "\<Pi> q = Some decl"
      and heq: "h' = Seq (body decl) Restore"
      and seq: "s' = bind_formals (formals decl) (map (\<lambda>e. aval e ss) actuals)
                        (enter_state gs ss)"
      and fzeq: "fz = [Frame ss dst]"
    by auto
  have loc': "control_at \<Pi> p c0 kk n (seq_after (Call dst q actuals) afters) vv"
    using Base.hyps(1) ceq by simp
  from csim_call_base[OF Base.prems(1) loc' Base.hyps(2) qdecl, where s = ss]
  obtain cfg' where
    cstar: "star (cstep gs g) (vv, ss, []) cfg'"
      and csimr: "csim \<Pi> g (seq_after (Seq (body decl) Restore) afters,
               bind_formals (formals decl) (map (\<lambda>e. aval e ss) actuals)
                 (enter_state gs ss),
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
      and stepin: "pstep gs \<Pi> (inner, s0, frs0 @ [Frame caller dst]) (inner', s', fz)"
    by (rule pstep_seq_after_seq_restore[OF Nested.prems(3) nsk nunw])
  from pstep_call_frame_restrict[OF stepin headinner refl] obtain fz' where
    fz: "fz = fz' @ [Frame caller dst]"
      and stepin': "pstep gs \<Pi> (inner, s0, frs0) (inner', s', fz')" by blast
  from Nested.hyps(2)[OF Nested.prems(1) headinner stepin'] obtain v' t' stk' where
    cstepin: "star (cstep gs g) (v0, s0, stk0) (v', t', stk')"
      and csimin: "csim \<Pi> g (inner', s', fz') (v', t', stk')" by auto
  have teq: "t' = s'" using csim_store_eq[OF csimin] by simp
  have cstepN: "star (cstep gs g) (v0, s0, stk0 @ [(cont, dst, caller)])
                               (v', s', stk' @ [(cont, dst, caller)])"
    using cstep_star_frame_extend[OF cstepin, of "[(cont, dst, caller)]"] teq by simp
  have "csim \<Pi> g (seq_after (Seq inner' Restore) afters, s', fz' @ [Frame caller dst])
                 (v', s', stk' @ [(cont, dst, caller)])"
    by (rule csim.Nested[OF csimin[unfolded teq] Nested.hyps(3) Nested.hyps(4)])
  then have "csim \<Pi> g src' (v', s', stk' @ [(cont, dst, caller)])"
    by (simp add: src' fz)
  with cstepN show ?case by blast
qed

section \<open>Intra-procedural preservation and callee fall-through\<close>

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
  A \<open>Nested\<close> callee that \<^emph>\<open>completes\<close> (\<open>inner = SKIP\<close>) exposes \<^const>\<open>Restore\<close> through the
  \<open>ISeq1\<close> fall-through; the CFG runs the completed callee to its exit
  (\<open>control_at_skip_to_exit\<close>) and takes the \<^term>\<open>EA_Ret None p\<close> edge into
  \<^term>\<open>FunctionResult p\<close> (\<open>compiled_at_exit\<close>), landing in a \<open>Returning\<close> activation.
\<close>
theorem csim_intra_completion:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> procs_embedded \<Pi> g \<Longrightarrow>
   intra_step \<Pi> (c, s, frs) src' \<Longrightarrow>
   \<exists>cfg'. star (cstep gs g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
proof (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c s frs v t stk src' rule: csim.induct)
  case (Base p c0 kk n cc vv ss)
  obtain c' s' frs' where sc: "src' = (c', s', frs')" by (cases src')
  from Base.prems(2) sc have istep: "intra_step \<Pi> (cc, ss, []) (c', s', frs')" by simp
  from Base.hyps(2) obtain decl where pdecl: "\<Pi> p = Some decl" "c0 = body decl"
    by (rule compiled_at_decl)
  have srcbody: "source_com c0"
    using procs_embedded_source_com[OF Base.prems(1) \<open>\<Pi> p = Some decl\<close>] \<open>c0 = body decl\<close>
    by simp
  from Base.hyps(2) obtain n' en E K where comp: "compile \<Pi> p c0 kk n = (n', en, E, K)"
      and Esub: "E \<subseteq> intra g" by blast
  from intra_step_simulation[OF Base.hyps(1) istep comp Esub srcbody, where stk = "[]"]
  obtain v' where feq: "frs' = []" and loc': "control_at \<Pi> p c0 kk n c' v'"
      and cstar: "star (cstep gs g) (vv, ss, []) (v', s', [])" by blast
  have "csim \<Pi> g (c', s', []) (v', s', [])" by (rule csim.Base[OF loc' Base.hyps(2)])
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
    then have innerSKIP: "inner = SKIP"
      and src': "src' = (seq_after Restore afters, s0, frs0 @ [Frame caller dst])" by auto
    have baseInner: "csim \<Pi> g (SKIP, s0, frs0) (v0, s0, stk0)"
      using Nested.hyps(1) innerSKIP by simp
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
      using ftin by blast
    have star1: "star (cstep gs g) (v0, s0, [(cont, dst, caller)])
                   (kin, s0, [(cont, dst, caller)])"
      by (rule control_at_skip_to_exit[OF ctrl refl comp Esub])
    have "cstep gs g (kin, s0, [(cont, dst, caller)])
            (FunctionResult pin, s0, [(cont, dst, caller)])"
      using cstep.Intra[OF exitedge edge_step_EA_Ret_ret_store_mem] by simp
    with star1 have star: "star (cstep gs g) (v0, s0, [(cont, dst, caller)])
                             (FunctionResult pin, s0, [(cont, dst, caller)])"
      by (rule star_trans[OF _ star_step1])
    have "csim \<Pi> g (seq_after Restore afters, s0, [Frame caller dst])
                   (FunctionResult pin, s0, [(cont, dst, caller)])"
      by (rule csim.Returning[OF _ Nested.hyps(3) Nested.hyps(4)]) simp
    then have "csim \<Pi> g src' (FunctionResult pin, s0, [(cont, dst, caller)])"
      using src' frs0nil by simp
    with star show ?case using stk0nil by auto
  next
    assume "\<exists>inner' s'.
              src' = (seq_after (Seq inner' Restore) afters, s', frs0 @ [Frame caller dst])
              \<and> intra_step \<Pi> (inner, s0, frs0 @ [Frame caller dst])
                   (inner', s', frs0 @ [Frame caller dst])"
    then obtain inner' s' where
      src': "src' = (seq_after (Seq inner' Restore) afters, s', frs0 @ [Frame caller dst])"
        and stepin: "intra_step \<Pi> (inner, s0, frs0 @ [Frame caller dst])
                       (inner', s', frs0 @ [Frame caller dst])"
      by blast
    from intra_step_any_frame[OF stepin]
    have stepin': "intra_step \<Pi> (inner, s0, frs0) (inner', s', frs0)" .
    from Nested.hyps(2)[OF Nested.prems(1) stepin'] obtain v' t' stk' where
      cstepin: "star (cstep gs g) (v0, s0, stk0) (v', t', stk')"
        and csimin: "csim \<Pi> g (inner', s', frs0) (v', t', stk')" by auto
    have teq: "t' = s'" using csim_store_eq[OF csimin] by simp
    have cstepN: "star (cstep gs g) (v0, s0, stk0 @ [(cont, dst, caller)])
                                 (v', s', stk' @ [(cont, dst, caller)])"
      using cstep_star_frame_extend[OF cstepin, of "[(cont, dst, caller)]"] teq by simp
    have "csim \<Pi> g (seq_after (Seq inner' Restore) afters, s', frs0 @ [Frame caller dst])
                   (v', s', stk' @ [(cont, dst, caller)])"
      by (rule csim.Nested[OF csimin[unfolded teq] Nested.hyps(3) Nested.hyps(4)])
    then have "csim \<Pi> g src' (v', s', stk' @ [(cont, dst, caller)])" by (simp add: src')
    with cstepN show ?case by blast
  qed
qed

section \<open>Return initiation\<close>

text \<open>
  A source \<^const>\<open>Return\<close> in head position fires \<open>Return e --> Unwind\<close>, turning the innermost
  callee activation into its returning phase, while the CFG takes the \<^term>\<open>EA_Ret e p\<close> edge
  to \<^term>\<open>FunctionResult p\<close>.  The enclosing \<open>Nested\<close> wrapper becomes \<open>Returning\<close>: its body
  \<^term>\<open>Seq (seq_after Unwind cafters) Restore\<close> is \<^const>\<open>pop_ready\<close> because the callee's
  pending continuations \<open>cafters\<close> --- source residuals of a \<^const>\<open>control_at\<close> location ---
  carry no \<^const>\<open>Restore\<close>.  The \<open>frs \<noteq> []\<close> premise excludes the ill-formed base
  \<^const>\<open>Return\<close> (a stuck top-level return); \<open>csim_step\<close> discharges it from \<^const>\<open>return_safe\<close>.
\<close>
theorem csim_return_init_completion:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> procs_embedded \<Pi> g \<Longrightarrow> frs \<noteq> [] \<Longrightarrow>
   head_return c \<Longrightarrow> pstep gs \<Pi> (c, s, frs) src' \<Longrightarrow>
   \<exists>cfg'. star (cstep gs g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
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
      and stepin: "pstep gs \<Pi> (inner, s0, frs0 @ [Frame caller dst]) (inner', s', fz)"
    by (rule pstep_seq_after_seq_restore[OF Nested.prems(4) nsk nunw])
  show ?case
  proof (cases "frs0 = []")
    case True
    have baseInner: "csim \<Pi> g (inner, s0, []) (v0, s0, stk0)" using Nested.hyps(1) True by simp
    obtain pin c0in kin nin where
      stk0nil: "stk0 = []"
        and ctrl: "control_at \<Pi> pin c0in kin nin inner v0"
        and cacc: "compiled_at \<Pi> g pin c0in kin nin"
      using baseInner by blast
    from cacc obtain decl where pdecl: "\<Pi> pin = Some decl" "c0in = body decl"
      by (rule compiled_at_decl)
    have srcc0: "source_com c0in"
      using procs_embedded_source_com[OF Nested.prems(1) \<open>\<Pi> pin = Some decl\<close>]
            \<open>c0in = body decl\<close>
      by simp
    obtain e cafters where innerform: "inner = seq_after (Return e) cafters"
      using head_return_seq_after_form[OF hr_inner] by blast
    \<comment> \<open>the head step is @{text \<open>Return e --> Unwind\<close>}, leaving the continuations \<open>cafters\<close>\<close>
    have stepin1: "pstep gs \<Pi> (seq_after (Return e) cafters, s0, [Frame caller dst])
                     (inner', s', fz)"
      using stepin True innerform by simp
    obtain h' where inner'form: "inner' = seq_after h' cafters"
        and hstep: "pstep gs \<Pi> (Return e, s0, [Frame caller dst]) (h', s', fz)"
      by (rule pstep_seq_after_headE[OF stepin1]) auto
    have hUnw: "h' = Unwind" and s'eq: "s' = ret_store e s0" and fzeq: "fz = [Frame caller dst]"
      using hstep by (cases e; auto simp: ret_store_def)+
    \<comment> \<open>the callee continuations carry no \<open>Restore\<close>, so the \<open>Unwind\<close> spine is \<open>pop_ready\<close>\<close>
    have noRest: "\<forall>a \<in> set cafters. a \<noteq> Restore"
      by (rule control_at_head_return_afters_no_Restore[OF ctrl[unfolded innerform] srcc0])
    have popready: "pop_ready (Seq (seq_after Unwind cafters) Restore)"
      using unwinding_seq_after_Unwind[OF noRest] by simp
    \<comment> \<open>CFG: one \<open>Intra\<close> step along the return edge to @{term \<open>FunctionResult pin\<close>}\<close>
    from cacc obtain n' en E K where comp: "compile \<Pi> pin c0in kin nin = (n', en, E, K)"
        and Esub: "E \<subseteq> intra g" by blast
    obtain j where vk: "v0 = Statement j"
        and edge: "(Statement j, EA_Ret e pin, FunctionResult pin) \<in> E"
      using control_at_seq_after_return_edge[OF ctrl[unfolded innerform] refl comp] by blast
    have edgeg: "(Statement j, EA_Ret e pin, FunctionResult pin) \<in> intra g"
      using edge Esub by blast
    have cstep1: "cstep gs g (Statement j, s0, [(cont, dst, caller)])
                          (FunctionResult pin, ret_store e s0, [(cont, dst, caller)])"
      using cstep.Intra[OF edgeg edge_step_EA_Ret_ret_store_mem] .
    \<comment> \<open>the enclosing wrapper becomes @{text Returning}\<close>
    have rel: "csim \<Pi> g
        (seq_after (Seq (seq_after Unwind cafters) Restore) afters, ret_store e s0,
         [Frame caller dst])
        (FunctionResult pin, ret_store e s0, [(cont, dst, caller)])"
      by (rule csim.Returning[OF popready Nested.hyps(3) Nested.hyps(4)])
    have srcshape: "src' = (seq_after (Seq (seq_after Unwind cafters) Restore) afters,
                            ret_store e s0, [Frame caller dst])"
      using src' inner'form hUnw s'eq fzeq by simp
    have "star (cstep gs g) (v0, s0, stk0 @ [(cont, dst, caller)])
                         (FunctionResult pin, ret_store e s0, [(cont, dst, caller)])"
      using cstep1 vk stk0nil by auto
    with rel srcshape show ?thesis by auto
  next
    case False
    from pstep_frame_restrict[OF stepin refl False] obtain fz' where
      fz: "fz = fz' @ [Frame caller dst]"
        and stepin': "pstep gs \<Pi> (inner, s0, frs0) (inner', s', fz')" by blast
    from Nested.hyps(2)[OF Nested.prems(1) False hr_inner stepin'] obtain v' t' stk' where
      cstepin: "star (cstep gs g) (v0, s0, stk0) (v', t', stk')"
        and csimin: "csim \<Pi> g (inner', s', fz') (v', t', stk')" by auto
    have teq: "t' = s'" using csim_store_eq[OF csimin] by simp
    have cstepN: "star (cstep gs g) (v0, s0, stk0 @ [(cont, dst, caller)])
                                 (v', s', stk' @ [(cont, dst, caller)])"
      using cstep_star_frame_extend[OF cstepin, of "[(cont, dst, caller)]"] teq by simp
    have "csim \<Pi> g (seq_after (Seq inner' Restore) afters, s', fz' @ [Frame caller dst])
                   (v', s', stk' @ [(cont, dst, caller)])"
      by (rule csim.Nested[OF csimin[unfolded teq] Nested.hyps(3) Nested.hyps(4)])
    then have "csim \<Pi> g src' (v', s', stk' @ [(cont, dst, caller)])" by (simp add: src' fz)
    with cstepN show ?thesis by blast
  qed
qed

section \<open>Return propagation and the frame pop\<close>

lemma csim_returning_frames_nonempty:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> is_returning c \<Longrightarrow> frs \<noteq> [] \<and> stk \<noteq> []"
  by (erule csim.cases) (auto dest: control_at_not_returning)

lemma csim_not_unwind:
  "csim \<Pi> g (Unwind, s, frs) cfg' \<Longrightarrow> False"
  by (erule csim.cases) (auto dest: control_at_not_unwind pop_ready_not_Unwind)

text \<open>
  One \<^const>\<open>pstep\<close> of a base returning activation \<^term>\<open>seq_after w afters\<close>
  (\<^term>\<open>pop_ready w\<close>, framed by the single caller frame, CFG at \<^term>\<open>FunctionResult p\<close>)
  either \<^emph>\<open>pops\<close>: the source resumes at \<^term>\<open>seq_after SKIP afters\<close> with the combined store
  and the CFG performs exactly one return \<^const>\<open>cstep\<close> to \<open>cont\<close>, rebuilt as a \<open>Base\<close>
  activation; or \<^emph>\<open>propagates\<close>: an \<^const>\<open>Unwind\<close> advances one dead-code layer and the CFG
  stays at \<^term>\<open>FunctionResult p\<close> with \<^emph>\<open>zero\<close> \<^const>\<open>cstep\<close>, rebuilt as a \<open>Returning\<close>
  activation.
\<close>
lemma csim_returning_base_completion:
  assumes pr: "pop_ready w"
      and loc: "control_at \<Pi> pc c0c kc nc (seq_after SKIP afters) cont"
      and cacc: "compiled_at \<Pi> g pc c0c kc nc"
      and step: "pstep gs \<Pi> (seq_after w afters, callee, [Frame caller dst]) src'"
  shows "\<exists>cfg'. star (cstep gs g) (FunctionResult p, callee, [(cont, dst, caller)]) cfg'
              \<and> csim \<Pi> g src' cfg'"
proof -
  have wsk: "w \<noteq> SKIP" using pr by (rule pop_ready_not_SKIP)
  have wunw: "w \<noteq> Unwind" using pr by (rule pop_ready_not_Unwind)
  obtain h' s' frs' where
    src': "src' = (seq_after h' afters, s', frs')"
      and hstep: "pstep gs \<Pi> (w, callee, [Frame caller dst]) (h', s', frs')"
    by (rule pstep_seq_after_headE[OF step wsk wunw])
  let ?rs = "combine_collect gs dst caller callee"
  from pstep_pop_ready_head[OF pr hstep] show ?thesis
  proof (rule disjE)
    assume "(h', s', frs') =
              (SKIP, combine_assign dst (callee ret_var) (combine_env gs caller callee),
               [])"
    hence h': "h' = SKIP" "s' = ?rs" "frs' = []" by (auto simp: combine_collect_def)
    have "cstep gs g (FunctionResult p, callee, [(cont, dst, caller)]) (cont, ?rs, [])"
      by (rule cstep.Return)
    moreover have "csim \<Pi> g (seq_after SKIP afters, ?rs, []) (cont, ?rs, [])"
      by (rule csim.Base[OF loc cacc])
    ultimately show ?thesis using src' h' by auto
  next
    assume "\<exists>w'. (h', s', frs') = (w', callee, [Frame caller dst]) \<and> pop_ready w'"
    then obtain w' where h': "h' = w'" "s' = callee" "frs' = [Frame caller dst]"
        and pr': "pop_ready w'" by auto
    have "csim \<Pi> g (seq_after w' afters, callee, [Frame caller dst])
                   (FunctionResult p, callee, [(cont, dst, caller)])"
      by (rule csim.Returning[OF pr' loc cacc])
    with src' h' show ?thesis by auto
  qed
qed

text \<open>Deep return completion: the base case above, threaded out through any number of
  \<open>Nested\<close> wrappers.  No \<^const>\<open>procs_embedded\<close> is needed --- the returning phase runs on the
  certificates \<open>csim\<close> already carries.\<close>
theorem csim_returning_completion:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> is_returning c \<Longrightarrow>
   pstep gs \<Pi> (c, s, frs) src' \<Longrightarrow>
   \<exists>cfg'. star (cstep gs g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
proof (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c s frs v t stk src' rule: csim.induct)
  case (Base p c0 kk n cc vv ss)
  from control_at_not_returning[OF Base.hyps(1)] Base.prems(1) show ?case by simp
next
  case (Returning w pc c0c kc nc ao cont callee caller dst p)
  from csim_returning_base_completion[OF Returning.hyps(1) Returning.hyps(2) Returning.hyps(3)
                                         Returning.prems(2)]
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
      and stepin: "pstep gs \<Pi> (inner, s0, frs0 @ [Frame caller dst]) (inner', s', fz)"
    by (rule pstep_seq_after_seq_restore[OF Nested.prems(2) nsk nunw])
  from pstep_frame_restrict[OF stepin refl frsne] obtain fz' where
    fz: "fz = fz' @ [Frame caller dst]"
      and stepin': "pstep gs \<Pi> (inner, s0, frs0) (inner', s', fz')" by blast
  from Nested.hyps(2)[OF retinner stepin'] obtain v' t' stk' where
    cstepin: "star (cstep gs g) (v0, s0, stk0) (v', t', stk')"
      and csimin: "csim \<Pi> g (inner', s', fz') (v', t', stk')" by auto
  have teq: "t' = s'" using csim_store_eq[OF csimin] by simp
  have cstepN: "star (cstep gs g) (v0, s0, stk0 @ [(cont, dst, caller)])
                               (v', s', stk' @ [(cont, dst, caller)])"
    using cstep_star_frame_extend[OF cstepin, of "[(cont, dst, caller)]"] teq by simp
  have "csim \<Pi> g (seq_after (Seq inner' Restore) afters, s', fz' @ [Frame caller dst])
                 (v', s', stk' @ [(cont, dst, caller)])"
    by (rule csim.Nested[OF csimin[unfolded teq] Nested.hyps(3) Nested.hyps(4)])
  then have "csim \<Pi> g src' (v', s', stk' @ [(cont, dst, caller)])"
    by (simp add: src' fz)
  with cstepN show ?case by blast
qed

section \<open>Single-step and finite-execution forward simulation\<close>

text \<open>Only a \<open>Base\<close> activation has an empty stack, and its located residual is a source
  command, so \<^const>\<open>return_safe\<close> forbids it from heading with \<^const>\<open>Return\<close>.  This is where
  \<^const>\<open>return_safe\<close> discharges the nonempty-frame premise of
  \<open>csim_return_init_completion\<close>.\<close>
lemma csim_head_return_frames:
  assumes SIM: "csim \<Pi> g (c, s, frs) (v, t, stk)"
      and PC: "procs_embedded \<Pi> g"
      and WF: "return_safe c"
      and RET: "head_return c"
  shows "frs \<noteq> []"
proof (rule ccontr)
  assume "\<not> frs \<noteq> []"
  hence base: "csim \<Pi> g (c, s, []) (v, t, stk)" using SIM by simp
  obtain p c0 kk n where
    ctrl: "control_at \<Pi> p c0 kk n c v" and cacc: "compiled_at \<Pi> g p c0 kk n"
    using base by blast
  from cacc obtain decl where pdecl: "\<Pi> p = Some decl" "c0 = body decl"
    by (rule compiled_at_decl)
  have "source_com c0"
    using procs_embedded_source_com[OF PC \<open>\<Pi> p = Some decl\<close>] \<open>c0 = body decl\<close> by simp
  hence "source_com c" using control_at_source_com[OF ctrl] by simp
  from return_safe_not_head_return[OF WF this] RET show False by simp
qed

text \<open>
  One-step forward simulation: the four-way redex classification (\<open>head_call\<close> /
  \<open>head_return\<close> / \<open>is_returning\<close> / otherwise-intra) dispatched to the four completion
  theorems above.  \<^const>\<open>return_safe\<close> is used only to supply the nonempty frame for the
  return-initiation branch; the statement exposes none of the internal classifiers, compile
  tuples, offsets, or frame conditions.
\<close>
theorem csim_step:
  assumes SIM: "csim \<Pi> g (c, s, frs) (v, t, stk)"
      and PC: "procs_embedded \<Pi> g"
      and WF: "return_safe c"
      and STEP: "pstep gs \<Pi> (c, s, frs) src'"
  shows "\<exists>cfg'. star (cstep gs g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
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
      by (rule pstep_intra_classify[OF procs_embedded_special_table_none[OF PC]
            STEP[unfolded sc] intra(1) intra(2) intra(3)])
    from csim_intra_completion[OF SIM PC this] show ?thesis by (simp add: sc)
  qed
qed

lemma csim_run:
  assumes PC: "procs_embedded \<Pi> g"
      and RUN: "star (pstep gs \<Pi>) sc sc'"
      and SIM: "csim \<Pi> g sc dg"
      and WF: "return_safe (fst sc)"
  shows "\<exists>dg'. star (cstep gs g) dg dg' \<and> csim \<Pi> g sc' dg'"
  using RUN SIM WF
proof (induction arbitrary: dg rule: star.induct)
  case (refl a)
  obtain v0 t0 k0 where "dg = (v0, t0, k0)" by (cases dg)
  with refl show ?case by auto
next
  case (step a b cc)
  obtain c0 s0 f0 where a: "a = (c0, s0, f0)" by (cases a)
  obtain c1 s1 f1 where b: "b = (c1, s1, f1)" by (cases b)
  obtain v0 t0 k0 where dgd: "dg = (v0, t0, k0)" by (cases dg)
  have SIMa: "csim \<Pi> g (c0, s0, f0) (v0, t0, k0)" using step.prems(1) a dgd by simp
  have WFa: "return_safe c0" using step.prems(2) a by simp
  have STEP: "pstep gs \<Pi> (c0, s0, f0) (c1, s1, f1)" using step.hyps(1) a b by simp
  from csim_step[OF SIMa PC WFa STEP] obtain dg1 where
    run1: "star (cstep gs g) (v0, t0, k0) dg1"
    and sim1: "csim \<Pi> g (c1, s1, f1) dg1" by blast
  have bodies: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
    using procs_embedded_source_com[OF PC] .
  have WFb: "return_safe (fst b)" using return_safe_pstep[OF bodies STEP WFa] b by simp
  have sim1b: "csim \<Pi> g b dg1" using sim1 b by simp
  from step.IH[OF sim1b WFb] obtain dg' where
    run2: "star (cstep gs g) dg1 dg'" and sim2: "csim \<Pi> g cc dg'" by blast
  from run1 run2 have "star (cstep gs g) (v0, t0, k0) dg'" by (rule star_trans)
  with sim2 show ?case using dgd by blast
qed

theorem csim_star:
  assumes SIM: "csim \<Pi> g (c, s, frs) (v, t, stk)"
      and PC: "procs_embedded \<Pi> g"
      and WF: "return_safe c"
      and RUN: "star (pstep gs \<Pi>) (c, s, frs) src'"
  shows "\<exists>cfg'. star (cstep gs g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
  using csim_run[OF PC RUN SIM] WF by simp

section \<open>The static certificate for a whole compiled program\<close>

text \<open>The static source contract establishes the runtime return guard for the root activation.\<close>
lemma wf_compile_input_return_safe:
  assumes "wf_compile_input gs \<Pi> ps"
  shows "return_safe (main_body \<Pi>)"
  using wf_compile_inputD(8)[OF assms] wf_compile_inputD(4)[OF assms]
  by (rule return_safe_if_no_return)

text \<open>
  \<^const>\<open>procs_embedded\<close> is the static certificate \<^const>\<open>csim\<close> reads: every procedure declared
  in \<open>\<Pi>\<close> has its body fragment, entry \<open>EA_Nop\<close> wiring and \<open>EA_Ret None\<close> exit wiring in the
  target graph.  It covers the entry procedure too, since
  \<open>\<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body \<Pi>\<rparr>\<close> makes
  \<^term>\<open>FunctionEntry prog_main_name\<close> an ordinary
  activation.  Discharging it from actual \<^const>\<open>compile_prog\<close> output, rather than assuming it
  forever, is what closes the static side of the simulation.
\<close>
theorem procs_embedded_compile_prog:
  assumes wf: "wf_compile_input gs \<Pi> ps"
  shows "procs_embedded \<Pi> (compile_prog \<Pi> ps)"
  unfolding procs_embedded_def
proof (intro allI impI)
  fix p decl assume pd: "\<Pi> p = Some decl"
  let ?g = "compile_prog \<Pi> ps"
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> prog_main_name \<lparr>formals = [], body = main_body \<Pi>\<rparr> n1
                  = (n2, Emain, Kmain)"
    and intra_g: "intra ?g = Eprocs \<union> Emain" and calls_g: "calls ?g = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  have srccom: "source_com (body decl)"
    using wf_compile_inputD(7)[OF wf] pd unfolding source_pi_def by blast
  have "\<exists>m m' Ef Kf. compile_proc \<Pi> p decl m = (m', Ef, Kf)
          \<and> Ef \<subseteq> intra ?g \<and> Kf \<subseteq> calls ?g"
  proof (cases "p = prog_main_name")
    case True
    with pd wf_compile_inputD(2)[OF wf]
    have "decl = \<lparr>formals = [], body = main_body \<Pi>\<rparr>" by simp
    then show ?thesis using mainc True intra_g calls_g by blast
  next
    case False
    with pd wf_compile_inputD(10)[OF wf] have "p \<in> set ps" by auto
    from compile_procs_member[OF procs this pd] obtain m m' Ef Kf where
      cp: "compile_proc \<Pi> p decl m = (m', Ef, Kf)" and "Ef \<subseteq> Eprocs" "Kf \<subseteq> Kprocs"
      by blast
    then have "Ef \<subseteq> intra ?g" "Kf \<subseteq> calls ?g" using intra_g calls_g by auto
    with cp show ?thesis by blast
  qed
  then obtain m m' Ef Kf where cp: "compile_proc \<Pi> p decl m = (m', Ef, Kf)"
    and Esub: "Ef \<subseteq> intra ?g" and Ksub: "Kf \<subseteq> calls ?g" by blast
  from cp obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement (m + csize (body decl))) m
           = (m + csize (body decl), Statement m, Eb, Kf)"
    and Edef: "Ef = insert (FunctionEntry p, EA_Body p, Statement m)
                 (if falls_through (body decl)
                  then insert (Statement (m + csize (body decl)), EA_Ret None p, FunctionResult p)
                         Eb
                  else Eb)"
    by (rule compile_procE)
  have Ebsub: "Eb \<subseteq> intra ?g" using Edef Esub by (auto split: if_splits)
  have ent: "(FunctionEntry p, EA_Body p, Statement m) \<in> intra ?g" using Edef Esub by auto
  have ext: "falls_through (body decl) \<longrightarrow>
               (Statement (m + csize (body decl)), EA_Ret None p, FunctionResult p) \<in> intra ?g"
    using Edef Esub by auto
  show "\<exists>k n n' en E K. compile \<Pi> p (body decl) k n = (n', en, E, K)
          \<and> E \<subseteq> intra ?g \<and> K \<subseteq> calls ?g
          \<and> (FunctionEntry p, EA_Body p, en) \<in> intra ?g
          \<and> (falls_through (body decl) \<longrightarrow>
               (k, EA_Ret None p, FunctionResult p) \<in> intra ?g)
          \<and> source_com (body decl) \<and> special_table p = None"
    using cb Ebsub Ksub ent ext srccom wf_compile_inputD(6)[OF wf pd] by blast
qed

section \<open>The certificate is inhabited\<close>

text \<open>
  Everything above is stated under \<^const>\<open>procs_embedded\<close>, and \<open>csim\<close> relates configurations
  only where that certificate holds; a reader is owed one graph that satisfies it, or the
  theorems could all be vacuous.  The smallest program --- \<open>main\<close> with an empty body and no
  callees --- is that witness, and it carries through to a \<open>csim\<close> relating a real source
  configuration to a real node of a real compiled graph.
\<close>

definition witness_pi :: proc_table where
  "witness_pi p = (if p = STR ''main'' then Some \<lparr>formals = [], body = SKIP\<rparr> else None)"

abbreviation witness_cfg :: cfg where
  "witness_cfg \<equiv> compile_prog witness_pi []"

lemma main_body_witness [simp]: "main_body witness_pi = SKIP"
  by (simp add: main_body_def witness_pi_def prog_main_name_def)

lemma witness_wf: "wf_compile_input (\<lambda>_. False) witness_pi []"
  by (auto simp: wf_compile_input_def wf_source_program_def witness_pi_def
        main_body_def prog_main_name_def
        wf_proc_decl_def reserved_ret_var_def ret_var_def
        special_table_def special_pname_nondet_int_def
        special_pname_min_def special_pname_max_def)

theorem procs_embedded_witness: "procs_embedded witness_pi witness_cfg"
  by (rule procs_embedded_compile_prog[OF witness_wf])

theorem csim_witness:
  obtains v where "csim witness_pi witness_cfg (SKIP, s, []) (v, s, [])"
proof -
  have decl: "witness_pi (STR ''main'') = Some \<lparr>formals = [], body = SKIP\<rparr>"
    by (simp add: witness_pi_def)
  obtain k n en where
    cacc: "compiled_at witness_pi witness_cfg (STR ''main'')
             (body \<lparr>formals = [], body = SKIP\<rparr>) k n"
      and ctrl: "control_at witness_pi (STR ''main'')
             (body \<lparr>formals = [], body = SKIP\<rparr>) k n (body \<lparr>formals = [], body = SKIP\<rparr>) en"
    by (rule procs_embedded_activation[OF procs_embedded_witness decl])
  have "csim witness_pi witness_cfg (SKIP, s, []) (en, s, [])"
    by (rule csim.Base[OF ctrl[simplified] cacc[simplified]])
  then show ?thesis ..
qed

end
