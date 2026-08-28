theory Control_Simulation_Forward
  imports Control_Simulation
begin

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
         \<and> source_com (body decl) \<and> special_table p = None))"

lemma procs_compiled_proc:
  assumes "procs_compiled \<Pi> g" and "\<Pi> p = Some decl"
  obtains k n n' en E K where
    "compile \<Pi> p (body decl) k n = (n', en, E, K)"
    "E \<subseteq> intra g" "K \<subseteq> calls g"
    "(FunctionEntry p, EA_Nop, en) \<in> intra g"
    "falls_through (body decl) \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g"
    "source_com (body decl)" "special_table p = None"
  using assms unfolding procs_compiled_def by blast

lemma procs_compiled_source_com:
  assumes "procs_compiled \<Pi> g" and "\<Pi> p = Some decl"
  shows "source_com (body decl)"
  using assms by (blast elim: procs_compiled_proc)

text \<open>A declared procedure's name is never one \<^const>\<open>special_table\<close> also classifies:
  \<open>procs_compiled\<close> bundles this disjointness alongside compiler-correctness so a declared call
  and a special call are always distinguishable without a separate well-formedness premise.\<close>
lemma procs_compiled_special_table_none:
  assumes "procs_compiled \<Pi> g" and "\<Pi> p = Some decl"
  shows "special_table p = None"
  using assms by (blast elim: procs_compiled_proc)

section \<open>Call preservation\<close>

text \<open>
  A source \<^const>\<open>Call\<close> at the head of the active residual is matched by two \<^const>\<open>cstep\<close>s
  --- the call edge to \<^term>\<open>FunctionEntry q\<close> and the entry \<^term>\<open>EA_Nop\<close> to the callee body ---
  and adds exactly one \<open>Nested\<close> layer: the callee body becomes a fresh \<open>Base\<close> activation and
  the caller resumes at \<^term>\<open>seq_after SKIP afters\<close>.  Everything the callee needs comes from
  the single \<^const>\<open>procs_compiled\<close> certificate.
\<close>
lemma csim_call_base:
  assumes pc: "procs_compiled \<Pi> g"
      and loc: "control_at \<Pi> p c0 kk n (seq_after (Call dst q actuals) afters) v"
      and cacc: "compiled_at \<Pi> g p c0 kk n"
      and pa: "proc_activation \<Pi> p c0"
      and decl: "\<Pi> q = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct: "distinct (formals decl)"
      and spNone: "special_table q = None"
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
  from control_at_seq_after_call_edge[OF loc refl comp spNone] obtain j w where
    vk: "v = Statement j"
    and edgeK: "(Statement j, CallEdge dst (call_formals \<Pi> q) actuals,
                 FunctionEntry q, w) \<in> K"
    and callerSKIP: "control_at \<Pi> p c0 kk n (seq_after SKIP afters) w" by blast
  have edge: "(Statement j, CallEdge dst (formals decl) actuals, FunctionEntry q, w)
                \<in> calls g" using edgeK Ksub by (auto simp: decl)
  have cstep1: "cstep source_global g (Statement j, s, [])
           (FunctionEntry q, call_enter source_global (CallEdge dst (formals decl) actuals) s,
            [(w, dst, s)])" by (rule cstep.Call[OF edge])
  have ce: "call_enter source_global (CallEdge dst (formals decl) actuals) s = ?callee"
    by (rule call_enter_CallEdge)
  obtain kq m m' en_q E_q K_q where
    cbody: "compile \<Pi> q (body decl) kq m = (m', en_q, E_q, K_q)"
      and E_qsub: "E_q \<subseteq> intra g" and K_qsub: "K_q \<subseteq> calls g"
      and entry: "(FunctionEntry q, EA_Nop, en_q) \<in> intra g"
      and exitq: "falls_through (body decl) \<longrightarrow>
                    (kq, EA_Ret None q, FunctionResult q) \<in> intra g"
      and srcbody: "source_com (body decl)"
      and "special_table q = None"
    by (rule procs_compiled_proc[OF pc decl])
  have caccq: "compiled_at \<Pi> g q (body decl) kq m"
    by (rule compiled_atI[OF cbody E_qsub K_qsub exitq])
  have cstep2: "cstep source_global g (FunctionEntry q, ?callee, [(w, dst, s)])
                        (en_q, ?callee, [(w, dst, s)])"
    using cstep_nop[OF entry] .
  have star: "star (cstep source_global g) (v, s, []) (en_q, ?callee, [(w, dst, s)])"
    using cstep1[unfolded ce] cstep2 vk by (simp add: star.step)
  have paq: "proc_activation \<Pi> q (body decl)"
    using decl unfolding proc_activation_def by blast
  have baseCallee: "csim \<Pi> g (body decl, ?callee, []) (en_q, ?callee, [])"
    by (rule csim.Base[OF control_at_initial[OF srcbody,
          of \<Pi> q kq m, folded compile_entry[OF cbody]] caccq paq])
  have "csim \<Pi> g (seq_after (Seq (body decl) Restore) afters, ?callee, [] @ [Frame s dst])
                 (en_q, ?callee, [] @ [(w, dst, s)])"
    by (rule csim.Nested[OF baseCallee callerSKIP cacc pa])
  then have "csim \<Pi> g (seq_after (Seq (body decl) Restore) afters, ?callee, [Frame s dst])
                      (en_q, ?callee, [(w, dst, s)])" by simp
  with star show ?thesis by blast
qed

text \<open>Unlike \<open>pstep_frame_restrict\<close> this needs no non-empty active stack: a call-headed
  command never heads with \<^const>\<open>SKIP\<close> / \<^const>\<open>Restore\<close> / \<^const>\<open>Unwind\<close>, so no pop can
  fire.\<close>
lemma pstep_call_frame_restrict:
  "pstep source_global \<Pi> (c, s, fr) (c', s', frs') \<Longrightarrow> head_call c \<Longrightarrow> fr = frs @ extra \<Longrightarrow>
   \<exists>frs''. frs' = frs'' @ extra \<and> pstep source_global \<Pi> (c, s, frs) (c', s', frs'')"
proof (induction "(c, s, fr)" "(c', s', frs')"
       arbitrary: c s fr frs c' s' frs' rule: pstep.induct)
  case (Seq2 c1 s1 f1 c1' s1' f1' c2 frs)
  from Seq2.prems(1) have "head_call c1" by simp
  from Seq2.hyps(2)[OF this Seq2.prems(2)] obtain frs'' where
    ih: "f1' = frs'' @ extra" "pstep source_global \<Pi> (c1, s1, frs) (c1', s1', frs'')" by blast
  show ?case by (rule exI[of _ frs'']) (use ih in auto)
next
  case (Call p decl actuals dst vals callee s1 frs0 frs)
  then show ?case by auto
qed auto

section \<open>Full call preservation\<close>

theorem csim_call_completion:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> procs_compiled \<Pi> g \<Longrightarrow> head_call c \<Longrightarrow>
   pstep source_global \<Pi> (c, s, frs) src' \<Longrightarrow>
   \<exists>cfg'. star (cstep source_global g) (v, t, stk) cfg' \<and> csim \<Pi> g src' cfg'"
proof (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c s frs v t stk src' rule: csim.induct)
  case (Base p c0 kk n cc vv ss)
  from head_call_seq_after_form[OF Base.prems(2)] obtain dst q actuals afters where
    ceq: "cc = seq_after (Call dst q actuals) afters" and spNone: "special_table q = None"
    by blast
  have step: "pstep source_global \<Pi> (seq_after (Call dst q actuals) afters, ss, []) src'"
    using Base.prems(3) ceq by simp
  have w1: "Call dst q actuals \<noteq> SKIP" by simp
  have w2: "Call dst q actuals \<noteq> Unwind" by simp
  obtain h' s' fz where
    src': "src' = (seq_after h' afters, s', fz)"
      and pcall: "pstep source_global \<Pi> (Call dst q actuals, ss, []) (h', s', fz)"
    by (rule pstep_seq_after_headD[OF step w1 w2])
  from pcall spNone obtain decl where
    qdecl: "\<Pi> q = Some decl" and ar: "length actuals = length (formals decl)"
      and di: "distinct (formals decl)"
      and heq: "h' = Seq (body decl) Restore"
      and seq: "s' = bind_formals (formals decl) (map (\<lambda>e. aval e ss) actuals)
                        (enter_state source_global ss)"
      and fzeq: "fz = [Frame ss dst]"
    by auto
  have loc': "control_at \<Pi> p c0 kk n (seq_after (Call dst q actuals) afters) vv"
    using Base.hyps(1) ceq by simp
  from csim_call_base[OF Base.prems(1) loc' Base.hyps(2) Base.hyps(3) qdecl ar di spNone,
      where s = ss]
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
      using ftin by (auto simp: compiled_at_def)
    have star1: "star (cstep source_global g) (v0, s0, [(cont, dst, caller)])
                   (kin, s0, [(cont, dst, caller)])"
      by (rule control_at_skip_to_exit[OF ctrl refl comp Esub])
    have "cstep source_global g (kin, s0, [(cont, dst, caller)])
            (FunctionResult pin, s0, [(cont, dst, caller)])"
      using cstep.Intra[OF exitedge edge_step_EA_Ret_ret_store_mem] by simp
    with star1 have star: "star (cstep source_global g) (v0, s0, [(cont, dst, caller)])
                             (FunctionResult pin, s0, [(cont, dst, caller)])"
      by (rule star_trans[OF _ star_step1])
    have "csim \<Pi> g (seq_after Restore afters, s0, [Frame caller dst])
                   (FunctionResult pin, s0, [(cont, dst, caller)])"
      by (rule csim.Returning[OF _ Nested.hyps(3) Nested.hyps(4) Nested.hyps(5)]) simp
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
  A source \<^const>\<open>Return\<close> in head position fires \<open>Return e --> Unwind\<close>, turning the innermost
  callee activation into its returning phase, while the CFG takes the \<^term>\<open>EA_Ret e p\<close> edge to
  \<^term>\<open>FunctionResult p\<close>.  The enclosing \<open>Nested\<close> wrapper becomes \<open>Returning\<close>: its body
  \<^term>\<open>Seq (seq_after Unwind cafters) Restore\<close> is \<^const>\<open>pop_ready\<close> because the callee's
  pending continuations \<open>cafters\<close> --- source residuals of a \<^const>\<open>control_at\<close> location ---
  carry no \<^const>\<open>Restore\<close>.  The \<open>frs \<noteq> []\<close> premise excludes the ill-formed base
  \<^const>\<open>Return\<close> (a stuck top-level return); \<open>csim_step\<close> discharges it from \<open>source_wf\<close>.
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
    have stepin1: "pstep source_global \<Pi> (seq_after (Return e) cafters, s0, [Frame caller dst])
                     (inner', s', fz)"
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
    have edgeg: "(Statement j, EA_Ret e pin, FunctionResult pin) \<in> intra g"
      using edge Esub by blast
    have cstep1: "cstep source_global g (Statement j, s0, [(cont, dst, caller)])
                          (FunctionResult pin, ret_store e s0, [(cont, dst, caller)])"
      using cstep.Intra[OF edgeg edge_step_EA_Ret_ret_store_mem] .
    \<comment> \<open>the enclosing wrapper becomes @{text Returning}\<close>
    have rel: "csim \<Pi> g
        (seq_after (Seq (seq_after Unwind cafters) Restore) afters, ret_store e s0,
         [Frame caller dst])
        (FunctionResult pin, ret_store e s0, [(cont, dst, caller)])"
      by (rule csim.Returning[OF popready Nested.hyps(3) Nested.hyps(4) Nested.hyps(5)])
    have srcshape: "src' = (seq_after (Seq (seq_after Unwind cafters) Restore) afters,
                            ret_store e s0, [Frame caller dst])"
      using src' inner'form hUnw s'eq fzeq by simp
    have "star (cstep source_global g) (v0, s0, stk0 @ [(cont, dst, caller)])
                         (FunctionResult pin, ret_store e s0, [(cont, dst, caller)])"
      using cstep1 vk stk0nil by auto
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

text \<open>Only a \<open>Base\<close> activation has an empty stack, and its located residual is a source
  command, so \<open>source_wf\<close> forbids it from heading with \<^const>\<open>Return\<close>.  This is where
  \<open>source_wf\<close> discharges the nonempty-frame premise of \<open>csim_return_init_completion\<close>.\<close>
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
  One-step forward simulation: the four-way redex classification (\<open>head_call\<close> /
  \<open>head_return\<close> / \<open>is_returning\<close> / otherwise-intra) dispatched to the four completion
  theorems.  \<open>source_wf\<close> is used only to supply the nonempty frame for the return-initiation
  branch; the statement exposes none of the internal classifiers, compile tuples, offsets, or
  frame conditions.
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
      by (rule pstep_intra_classify[OF procs_compiled_special_table_none[OF PC]
            STEP[unfolded sc] intra(1) intra(2) intra(3)])
    from csim_intra_completion[OF SIM PC this] show ?thesis by (simp add: sc)
  qed
qed

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
  with refl show ?case by auto
next
  case (step a b cc)
  obtain c0 s0 f0 where a: "a = (c0, s0, f0)" by (cases a)
  obtain c1 s1 f1 where b: "b = (c1, s1, f1)" by (cases b)
  obtain v0 t0 k0 where dgd: "dg = (v0, t0, k0)" by (cases dg)
  have SIMa: "csim \<Pi> g (c0, s0, f0) (v0, t0, k0)" using step.prems(1) a dgd by simp
  have WFa: "source_wf (c0, s0, f0)" using step.prems(2) a by simp
  have STEP: "pstep source_global \<Pi> (c0, s0, f0) (c1, s1, f1)" using step.hyps(1) a b by simp
  from csim_step[OF SIMa PC WFa STEP] obtain dg1 where
    run1: "star (cstep source_global g) (v0, t0, k0) dg1"
    and sim1: "csim \<Pi> g (c1, s1, f1) dg1" by blast
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
