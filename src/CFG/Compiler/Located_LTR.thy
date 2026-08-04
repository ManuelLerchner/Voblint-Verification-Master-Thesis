theory Located_LTR
  imports Compile_Certificate Compile_Locality CFG_Local_Trace LTR_Collect
begin

section \<open>Source execution as activation-local traces\<close>

text \<open>
  The stack-faithful bridge from compiled source execution to the canonical activation-local
  semantics \<^const>\<open>valid_ltr\<close>.  A CFG-located configuration \<^type>\<open>cconf\<close> (advanced one edge at a
  time by \<^const>\<open>cstep\<close>) is related to a valid activation-local trace: the current activation is
  the trace, and the runtime \<^type>\<open>cframe\<close> stack is its \<^const>\<open>caller_of\<close> chain.  Each \<^const>\<open>cstep\<close>
  rule maps one-to-one onto a \<^const>\<open>valid_ltr\<close> constructor (\<open>intra\<close> / \<open>call\<close> / \<open>ret\<close>), so a source
  run --- simulated into a \<^const>\<open>cstep\<close> run by \<^const>\<open>csim\<close> --- extends the accumulated trace.
\<close>

subsection \<open>Procedure locality of a valid activation\<close>

text \<open>The imported theorem \<open>valid_ltr_entry_result_eq\<close> establishes that an activation's
  local \<^const>\<open>path\<close> stays inside one compiled procedure fragment: an entry
  \<^term>\<open>FunctionEntry p\<close> and a sink \<^term>\<open>FunctionResult q\<close> have \<open>p = q\<close>.\<close>


subsection \<open>The representation invariant\<close>

text \<open>\<open>stack_repr\<close> walks \<^const>\<open>caller_of\<close> in lockstep with the runtime frame list: each
  \<^type>\<open>cframe\<close> \<open>(cont, dst, caller)\<close> pins the caller activation \<open>c\<close> --- its frozen store
  \<open>sink_store c = caller\<close> --- and records the concrete \<^const>\<open>calls\<close> edge that spawned the child,
  whose callee \<^term>\<open>FunctionEntry p\<close> equals the child's (path-invariant) entry node.\<close>
inductive stack_repr :: "cfg \<Rightarrow> cframe list \<Rightarrow> ltr \<Rightarrow> bool" for g where
  empty: "caller_of t = None \<Longrightarrow> stack_repr g [] t"
| frame: "caller_of t = Some c \<Longrightarrow> sink_store c = caller
          \<Longrightarrow> fst (hd (path t)) = FunctionEntry p
          \<Longrightarrow> (sink_node c, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
          \<Longrightarrow> stack_repr g stk c
          \<Longrightarrow> stack_repr g ((cont, dst, caller) # stk) t"

text \<open>\<open>ltr_repr\<close> pins a valid trace to a located configuration: the trace's sink is the current
  node/store, and its caller chain is the runtime stack.\<close>
definition ltr_repr :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cconf \<Rightarrow> ltr \<Rightarrow> bool" where
  "ltr_repr gs g S cf t = (case cf of (v, s, stk) \<Rightarrow>
     t \<in> valid_ltr gs g S \<and> sink_node t = v \<and> sink_store t = s \<and> stack_repr g stk t)"

definition located_ltr :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cconf \<Rightarrow> bool" where
  "located_ltr gs g S cf = (\<exists>t. ltr_repr gs g S cf t)"

text \<open>\<open>stack_repr\<close> reads only the top \<^const>\<open>caller_of\<close> and the path-invariant entry node, so it
  transfers across activations sharing both (an \<^const>\<open>extend\<close> appends --- entry unchanged --- and a
  \<^const>\<open>Resume\<close> prepends the same activation's path --- entry unchanged).\<close>
lemma stack_repr_cong:
  "stack_repr g stk t1 \<Longrightarrow> caller_of t2 = caller_of t1
   \<Longrightarrow> fst (hd (path t2)) = fst (hd (path t1)) \<Longrightarrow> stack_repr g stk t2"
  by (cases rule: stack_repr.cases) (auto intro: stack_repr.intros)

subsection \<open>The return step\<close>

text \<open>The load-bearing case.  A \<^const>\<open>cstep\<close> return pops the top frame; \<open>stack_repr\<close> identifies the
  caller \<open>c\<close> (\<^const>\<open>caller_of\<close> recovers it) and its spawning \<^const>\<open>calls\<close> edge, whose callee
  \<^term>\<open>FunctionEntry q\<close> matches the returning \<^term>\<open>FunctionResult q\<close> by
  \<open>valid_ltr_entry_result_eq\<close> --- so the trace composes by \<open>valid_ltr.ret\<close>, and the combined
  store equals the \<^const>\<open>cstep\<close> store.\<close>
lemma ltr_repr_Return:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and rep: "ltr_repr source_global (compile_prog \<Pi> ps mnm main) S
                  (FunctionResult q, tst, (cont, dst, caller) # stk) t0"
  shows "ltr_repr source_global (compile_prog \<Pi> ps mnm main) S
           (cont, combine_collect source_global dst caller tst, stk)
           (Resume (the (caller_of t0)) t0
              (path (the (caller_of t0)) @ [(cont, combine_collect source_global dst caller tst)]))"
proof -
  let ?g = "compile_prog \<Pi> ps mnm main"
  from rep have t0v: "t0 \<in> valid_ltr source_global ?g S" and sn0: "sink_node t0 = FunctionResult q"
    and ss0: "sink_store t0 = tst"
    and stk0: "stack_repr ?g ((cont, dst, caller) # stk) t0"
    by (auto simp: ltr_repr_def)
  from stk0 obtain c p pars args where cof: "caller_of t0 = Some c"
    and ssc: "sink_store c = caller" and entryp: "fst (hd (path t0)) = FunctionEntry p"
    and edge: "(sink_node c, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ?g"
    and stkc: "stack_repr ?g stk c"
    by (cases rule: stack_repr.cases) auto
  have cvalid: "c \<in> valid_ltr source_global ?g S" using valid_ltr_caller_valid[OF t0v cof] .
  have pq: "p = q" using valid_ltr_entry_result_eq[OF wf t0v entryp sn0] .
  have cthe: "the (caller_of t0) = c" using cof by simp
  let ?r = "combine_collect source_global dst caller tst"
  let ?t' = "Resume c t0 (path c @ [(cont, ?r)])"
  have edge_q: "(sink_node c, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls ?g"
    using edge pq by simp
  have valid': "?t' \<in> valid_ltr source_global ?g S"
    using valid_ltr.ret[OF t0v cof sn0 edge_q] ssc ss0 by simp
  have sn': "sink_node ?t' = cont" by (simp add: sink_node_def)
  have ss': "sink_store ?t' = ?r" by (simp add: sink_store_def)
  have entry': "fst (hd (path ?t')) = fst (hd (path c))"
    using valid_ltr_path_nonempty[OF cvalid] by simp
  have stk': "stack_repr ?g stk ?t'"
    using stack_repr_cong[OF stkc, of ?t'] entry' by simp
  show ?thesis
    unfolding cthe using valid' sn' ss' stk' by (simp add: ltr_repr_def)
qed

subsection \<open>The invariant is preserved by located CFG steps\<close>

text \<open>Each \<^const>\<open>cstep\<close> rule maps to one \<^const>\<open>valid_ltr\<close> constructor: intra \<open>\<mapsto>\<close>
  \<^const>\<open>extend\<close>, call \<open>\<mapsto>\<close> \<^const>\<open>Call\<close>, return \<open>\<mapsto>\<close> \<^const>\<open>Resume\<close> (\<open>ltr_repr_Return\<close>).\<close>
lemma cstep_preserves_ltr_repr:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and step: "cstep source_global (compile_prog \<Pi> ps mnm main) cf cf'"
    and rep: "ltr_repr source_global (compile_prog \<Pi> ps mnm main) S cf t"
  shows "\<exists>t'. ltr_repr source_global (compile_prog \<Pi> ps mnm main) S cf' t'"
  using step rep
proof (cases rule: cstep.cases)
  case (Intra u a v s' s stk')
  let ?g = "compile_prog \<Pi> ps mnm main"
  from rep have tv: "t \<in> valid_ltr source_global ?g S" and sn: "sink_node t = u" and ss: "sink_store t = s"
    and str: "stack_repr ?g stk' t"
    using Intra by (auto simp: ltr_repr_def)
  have e1: "(sink_node t, a, v) \<in> intra ?g" using Intra sn by simp
  have e2: "s' \<in> edge_step a (sink_store t)" using Intra ss by simp
  have "extend t (v, s') \<in> valid_ltr source_global ?g S" using valid_ltr.intra[OF tv e1 e2] .
  moreover have "stack_repr ?g stk' (extend t (v, s'))"
    using stack_repr_cong[OF str] valid_ltr_path_nonempty[OF tv] by simp
  ultimately have "ltr_repr source_global ?g S (v, s', stk') (extend t (v, s'))"
    by (simp add: ltr_repr_def)
  then show ?thesis using Intra by auto
next
  case (Call u dst pars actuals q cont s stk')
  let ?g = "compile_prog \<Pi> ps mnm main"
  from rep have tv: "t \<in> valid_ltr source_global ?g S" and sn: "sink_node t = u" and ss: "sink_store t = s"
    and str: "stack_repr ?g stk' t"
    using Call by (auto simp: ltr_repr_def)
  have edge: "(sink_node t, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls ?g"
    using Call sn by simp
  let ?child = "Call t [(FunctionEntry q, call_enter source_global (CallEdge dst pars actuals) s)]"
  have child_valid: "?child \<in> valid_ltr source_global ?g S"
    using valid_ltr.call[OF tv edge] ss by simp
  have "stack_repr ?g ((cont, dst, s) # stk') ?child"
  proof (rule stack_repr.frame)
    show "caller_of ?child = Some t" by simp
    show "sink_store t = s" using ss .
    show "fst (hd (path ?child)) = FunctionEntry q" by simp
    show "(sink_node t, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls ?g"
      using edge .
    show "stack_repr ?g stk' t" using str .
  qed
  with child_valid have "ltr_repr source_global ?g S
      (FunctionEntry q, call_enter source_global (CallEdge dst pars actuals) s, (cont, dst, s) # stk') ?child"
    by (simp add: ltr_repr_def sink_node_def sink_store_def)
  then show ?thesis using Call by auto
next
  case (Return q tst cont dst caller stk')
  from rep Return(1)
  have rep': "ltr_repr source_global (compile_prog \<Pi> ps mnm main) S
                (FunctionResult q, tst, (cont, dst, caller) # stk') t" by simp
  from ltr_repr_Return[OF wf rep'] show ?thesis using Return(2) by auto
qed

lemma located_ltr_entry:
  assumes "s \<in> S"
  shows "located_ltr source_global g S (cfg_entry g, s, [])"
proof -
  have "ltr_repr source_global g S (cfg_entry g, s, []) (Root [(cfg_entry g, s)])"
    using assms
    by (auto simp: ltr_repr_def sink_node_def sink_store_def valid_ltr.init
             intro: stack_repr.empty)
  then show ?thesis by (auto simp: located_ltr_def)
qed

lemma cstep_preserves_located_ltr:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and "located_ltr source_global (compile_prog \<Pi> ps mnm main) S cf"
    and "cstep source_global (compile_prog \<Pi> ps mnm main) cf cf'"
  shows "located_ltr source_global (compile_prog \<Pi> ps mnm main) S cf'"
proof -
  from assms(2) obtain t where "ltr_repr source_global (compile_prog \<Pi> ps mnm main) S cf t"
    by (auto simp: located_ltr_def)
  then obtain t' where "ltr_repr source_global (compile_prog \<Pi> ps mnm main) S cf' t'"
    using cstep_preserves_ltr_repr[OF wf assms(3)] by blast
  then show ?thesis by (auto simp: located_ltr_def)
qed

lemma csteps_preserve_located_ltr:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and "located_ltr source_global (compile_prog \<Pi> ps mnm main) S cf"
    and "star (cstep source_global (compile_prog \<Pi> ps mnm main)) cf cf'"
  shows "located_ltr source_global (compile_prog \<Pi> ps mnm main) S cf'"
  using assms(3) assms(2)
proof (induction rule: star.induct)
  case (refl a)
  then show ?case .
next
  case (step a b c)
  have "located_ltr source_global (compile_prog \<Pi> ps mnm main) S b"
    by (rule cstep_preserves_located_ltr[OF wf step.prems step.hyps(1)])
  then show ?case by (rule step.IH)
qed

subsection \<open>The initial main activation\<close>

text \<open>The program entry \<^term>\<open>FunctionEntry mnm\<close> is an ordinary \<open>csim.Base\<close> activation: the
  distinguished main procedure is declared in \<open>\<Pi>\<close> (\<open>wf_compile_input\<close>), so its body-fragment is
  certified by \<open>procs_compiled_compile_prog\<close> and \<^const>\<open>proc_activation\<close> holds.  One \<^term>\<open>EA_Nop\<close>
  edge crosses from \<^term>\<open>FunctionEntry mnm\<close> to the body entry \<open>en\<close>, where the \<open>Base\<close> activation
  simulates the source \<open>main\<close>.\<close>
lemma compile_prog_main_base:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
  obtains en where
    "(FunctionEntry mnm, EA_Nop, en) \<in> intra (compile_prog \<Pi> ps mnm main)"
    "csim \<Pi> (compile_prog \<Pi> ps mnm main) (main, s, []) (en, s, [])"
proof -
  let ?g = "compile_prog \<Pi> ps mnm main"
  have pc: "procs_compiled \<Pi> ?g" by (rule procs_compiled_compile_prog[OF wf])
  have mnmdecl: "\<Pi> mnm = Some (proc_decl_of [] main)"
    by (rule wf_compile_input_main_exists[OF wf])
  obtain k m m' en E K where
    cbody: "compile \<Pi> mnm (body (proc_decl_of [] main)) k m = (m', en, E, K)"
      and Esub: "E \<subseteq> intra ?g" and Ksub: "K \<subseteq> calls ?g"
      and entry: "(FunctionEntry mnm, EA_Nop, en) \<in> intra ?g"
      and exitm: "falls_through (body (proc_decl_of [] main)) \<longrightarrow>
                    (k, EA_Ret None mnm, FunctionResult mnm) \<in> intra ?g"
      and srcbody: "source_com (body (proc_decl_of [] main))"
    by (rule procs_compiled_proc[OF pc mnmdecl])
  have bodyeq: "body (proc_decl_of [] main) = main" by (simp add: proc_decl_of_def)
  have cbody': "compile \<Pi> mnm main k m = (m', en, E, K)" using cbody bodyeq by simp
  have srcmain: "source_com main" using srcbody bodyeq by simp
  have exitm': "falls_through main \<longrightarrow> (k, EA_Ret None mnm, FunctionResult mnm) \<in> intra ?g"
    using exitm bodyeq by simp
  have cacc: "compiled_at \<Pi> ?g mnm main k m"
    by (rule compiled_atI[OF cbody' Esub Ksub exitm'])

  have pa: "proc_activation \<Pi> mnm main"
    using mnmdecl bodyeq unfolding proc_activation_def by auto
  have base: "csim \<Pi> ?g (main, s, []) (en, s, [])"
    by (rule csim.Base[OF control_at_initial[OF srcmain, of \<Pi> mnm k m,
                          folded compile_entry_node[OF cbody']] cacc pa])

  from entry base show ?thesis ..
qed

subsection \<open>Top-level structural facts of the invariant\<close>

text \<open>A trace has no caller exactly when its activation is at the top level (empty runtime stack).\<close>
lemma stack_repr_Nil_iff:
  "stack_repr g stk t \<Longrightarrow> (stk = []) = (caller_of t = None)"
  by (cases rule: stack_repr.cases) auto

text \<open>The context \<^const>\<open>key\<close> of a callerless activation is the seed --- descending the
  \<^const>\<open>caller_of\<close> chain (a \<^const>\<open>Resume\<close> of \<^const>\<open>Root\<close> is still callerless).\<close>
lemma key_caller_of_None:
  "caller_of t = None \<Longrightarrow> key enterc seedc t = seedc"
  by (induction t) auto

subsection \<open>The source bridge\<close>

text \<open>Composing the initial \<open>csim.Base\<close> with \<open>csim_star\<close> (the source-to-\<^const>\<open>cstep\<close>
  simulation) and the located invariant: every source run produces a matching valid
  activation-local trace at the simulated node.\<close>
theorem source_run_has_ltr:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and s0: "s0 \<in> S"
    and run: "star (pstep source_global \<Pi>) (main, s0, []) (residual, s, frs)"
  shows "\<exists>v stk t. csim \<Pi> (compile_prog \<Pi> ps mnm main) (residual, s, frs) (v, s, stk)
                   \<and> ltr_repr source_global (compile_prog \<Pi> ps mnm main) S (v, s, stk) t"
proof -
  let ?g = "compile_prog \<Pi> ps mnm main"
  have pc: "procs_compiled \<Pi> ?g" by (rule procs_compiled_compile_prog[OF wf])
  have swf: "source_wf (main, s0, [])" by (rule wf_compile_input_source_wf[OF wf])
  obtain en where entry: "(FunctionEntry mnm, EA_Nop, en) \<in> intra ?g"
    and base: "csim \<Pi> ?g (main, s0, []) (en, s0, [])"
    by (rule compile_prog_main_base[OF wf])
  have loc0: "located_ltr source_global (compile_prog \<Pi> ps mnm main) S (FunctionEntry mnm, s0, [])"
    using located_ltr_entry[where source_global=source_global and g="compile_prog \<Pi> ps mnm main", OF s0]
    by (simp add: inv16_entry_is_main)
  have step0: "cstep source_global ?g (FunctionEntry mnm, s0, []) (en, s0, [])" by (rule cstep_nop[OF entry])
  have loc_en: "located_ltr source_global ?g S (en, s0, [])"
    by (rule cstep_preserves_located_ltr[OF wf loc0 step0])
  from csim_star[OF base pc swf run] obtain cf'
    where run_c: "star (cstep source_global ?g) (en, s0, []) cf'" and sim': "csim \<Pi> ?g (residual, s, frs) cf'"
    by blast
  obtain v s' stk where cf': "cf' = (v, s', stk)" by (cases cf')
  have store: "s' = s" using csim_store_eq[OF sim'[unfolded cf']] by simp
  have loc_v: "located_ltr source_global ?g S (v, s, stk)"
    using csteps_preserve_located_ltr[OF wf loc_en run_c] cf' store by simp
  from loc_v obtain t where "ltr_repr source_global ?g S (v, s, stk) t" by (auto simp: located_ltr_def)
  then show ?thesis using sim' cf' store by blast
qed

text \<open>The plain projected source bridge: a reachable source store lies in the local-trace
  collecting \<^const>\<open>activation_collect\<close> at the simulated node, keyed by the witness trace.\<close>
theorem source_store_in_activation_collect:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and s0: "s0 \<in> S"
    and run: "star (pstep source_global \<Pi>) (main, s0, []) (residual, s, frs)"
  shows "\<exists>v stk t. csim \<Pi> (compile_prog \<Pi> ps mnm main) (residual, s, frs) (v, s, stk)
                   \<and> s \<in> activation_collect source_global enterc seedc (compile_prog \<Pi> ps mnm main) S v
                          (key enterc seedc t)"
proof -
  let ?g = "compile_prog \<Pi> ps mnm main"
  from source_run_has_ltr[OF wf s0 run] obtain v stk t
    where sim: "csim \<Pi> ?g (residual, s, frs) (v, s, stk)"
      and rep: "ltr_repr source_global ?g S (v, s, stk) t" by blast
  from rep have tv: "t \<in> valid_ltr source_global ?g S" and sn: "sink_node t = v" and ss: "sink_store t = s"
    by (auto simp: ltr_repr_def)
  have "s \<in> activation_collect source_global enterc seedc ?g S v (key enterc seedc t)"
    using activation_collect_I[OF tv sn refl] ss by simp
  then show ?thesis using sim by blast
qed

text \<open>The witness-free top-level result: a store reached with an empty source frame stack lies in
  the activation collecting at the fixed seed context --- no \<^typ>\<open>ltr\<close> witness and no context
  existential.  This is the shape a user reads for main-level program points.\<close>
theorem source_toplevel_in_activation_collect:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
    and s0: "s0 \<in> S"
    and run: "star (pstep source_global \<Pi>) (main, s0, []) (residual, s, [])"
  shows "\<exists>v. csim \<Pi> (compile_prog \<Pi> ps mnm main) (residual, s, []) (v, s, [])
             \<and> s \<in> activation_collect source_global enterc seedc (compile_prog \<Pi> ps mnm main) S v seedc"
proof -
  let ?g = "compile_prog \<Pi> ps mnm main"
  from source_run_has_ltr[OF wf s0 run] obtain v stk t
    where sim: "csim \<Pi> ?g (residual, s, []) (v, s, stk)"
      and rep: "ltr_repr source_global ?g S (v, s, stk) t" by blast
  have stk0: "stk = []" using csim_Nil_baseD[OF sim] by simp
  from rep stk0 have tv: "t \<in> valid_ltr source_global ?g S" and sn: "sink_node t = v" and ss: "sink_store t = s"
    and sr: "stack_repr ?g [] t" by (auto simp: ltr_repr_def)
  have "caller_of t = None" using stack_repr_Nil_iff[OF sr] by simp
  then have key: "key enterc seedc t = seedc" by (rule key_caller_of_None)
  have "s \<in> activation_collect source_global enterc seedc ?g S v seedc"
    using activation_collect_I[OF tv sn key] ss by simp
  then show ?thesis using sim stk0 by blast
qed

end



