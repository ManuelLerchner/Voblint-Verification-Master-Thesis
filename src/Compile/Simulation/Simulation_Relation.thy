theory Simulation_Relation
  imports Residual_Edges
begin

section \<open>The relation between a source state and a graph state\<close>

text \<open>
  \<open>csim\<close> says that a source configuration and a graph configuration are two views of the
  same execution.  Both carry an activation stack: a source frame holds the caller's store
  and the destination variable, a \<open>cframe\<close> additionally holds the node to resume at.  The
  correspondence is direct --- the stores are equal, \<^const>\<open>control_at\<close> puts the running
  residual at the current node, and the two stacks are paired frame by frame, one \<open>csim\<close>
  layer per suspended caller.

  It has three shapes: \<open>Base\<close> for an activation running with nothing beneath it, \<open>Nested\<close>
  for one with callers beneath it, and \<open>Returning\<close> for the window in which the source is
  still unwinding a finished activation while the graph has already arrived at
  \<^term>\<open>FunctionResult\<close>.
\<close>

subsection \<open>Return initiation\<close>

text \<open>The store published by a return, common to the source \<^const>\<open>Return\<close> step and the
  compiled \<^term>\<open>EA_Ret\<close> edge.\<close>
definition ret_store :: "exp option \<Rightarrow> store \<Rightarrow> store" where
  "ret_store e s = s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))"

lemma ret_store_None [simp]: "ret_store None s = s"
  by (simp add: ret_store_def)

lemma ret_store_Some [simp]: "ret_store (Some e) s = s(ret_var := aval e s)"
  by (simp add: ret_store_def)

lemma edge_step_EA_Ret_ret_store_mem [simp]: "ret_store e s \<in> edge_step (EA_Ret e p) s"
  by (simp add: ret_store_def)

subsection \<open>The empty-stack return guard\<close>

lemma pstep_Unwind_stuck: "\<not> pstep source_global \<Pi> (Unwind, s, frs) x"
  by auto

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

lemma compiled_atI [intro]:
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

subsection \<open>Derived structural facts\<close>

lemma csim_store_eq:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> s = t"
  by (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c frs v stk rule: csim.induct) auto

lemma csim_Nil_baseD:
  "csim \<Pi> g (c, s, []) (v, t, stk) \<Longrightarrow>
   stk = [] \<and> s = t \<and> (\<exists>p c0 k n. control_at \<Pi> p c0 k n c v)"
  by (blast elim: csim_NilE)

lemma csim_base_procD:
  assumes "csim \<Pi> g (c, s, []) (v, t, stk)"
  obtains p c0 k n where
    "control_at \<Pi> p c0 k n c v" "compiled_at \<Pi> g p c0 k n" "proc_activation \<Pi> p c0"
  using assms by (blast elim: csim_NilE)

subsection \<open>Returning commands and the frame-pop phase\<close>

text \<open>\<open>is_returning c\<close> holds when the leftmost-innermost of \<open>c\<close> is \<^const>\<open>Restore\<close> or
  \<^const>\<open>Unwind\<close>: the shape of every returning-phase command, ordinary or \<open>Nested\<close>-wrapped.\<close>
fun is_returning :: "com \<Rightarrow> bool" where
  "is_returning Restore = True"
| "is_returning Unwind = True"
| "is_returning (Seq c1 c2) = is_returning c1"
| "is_returning _ = False"

lemma is_returning_seq_after [simp]:
  "is_returning (seq_after c afters) = is_returning c"
  by (induction afters arbitrary: c) auto

subsection \<open>The call-redex source shape\<close>

text \<open>\<open>head_call c\<close> holds when the leftmost-innermost of \<open>c\<close> is a \<^const>\<open>Call\<close> to a procedure
  \<^const>\<open>special_table\<close> does not classify: the shape of an active residual whose next
  \<^const>\<open>pstep\<close> pushes a frame.  A call \<^const>\<open>special_table\<close> classifies resolves in place
  instead (\<^const>\<open>intra_step\<close>'s \<open>ISpecial\<close>), so it is deliberately excluded here, mirroring
  \<^const>\<open>intra_step\<close>'s own exclusion of \<^const>\<open>Call\<close>.\<close>
fun head_call :: "com \<Rightarrow> bool" where
  "head_call (Call dst q actuals) = (special_table q = None)"
| "head_call (Seq c1 c2) = head_call c1"
| "head_call _ = False"

lemma head_call_seq_after [simp]:
  "head_call (seq_after c afters) = head_call c"
  by (induction afters arbitrary: c) auto

lemma head_call_not_SKIP: "head_call c \<Longrightarrow> c \<noteq> SKIP"
  by (cases c) auto

lemma head_call_not_Unwind: "head_call c \<Longrightarrow> c \<noteq> Unwind"
  by (cases c) auto

lemma head_call_seq_after_form:
  "head_call c \<Longrightarrow> \<exists>dst q actuals afters.
     c = seq_after (Call dst q actuals) afters \<and> special_table q = None"
proof (induction c)
  case (Seq c1 c2)
  from Seq.prems have "head_call c1" by simp
  from Seq.IH(1)[OF this] obtain dst q actuals afters where
    "c1 = seq_after (Call dst q actuals) afters" "special_table q = None" by blast
  then have "Seq c1 c2 = seq_after (Call dst q actuals) (afters @ [c2])"
             "special_table q = None"
    by (simp_all add: seq_after_snoc)
  then show ?case by blast
qed auto

lemma unwinding_not_head_call: "unwinding u \<Longrightarrow> \<not> head_call u"
  by (induction u rule: unwinding.induct) auto

lemma pop_ready_not_head_call: "pop_ready w \<Longrightarrow> \<not> head_call w"
  by (cases w rule: pop_ready.cases) (auto simp: unwinding_not_head_call)

subsection \<open>The return-initiation source shape\<close>

text \<open>\<open>head_return c\<close> holds when the leftmost-innermost of \<open>c\<close> is a source \<^const>\<open>Return\<close>:
  the shape whose next \<^const>\<open>pstep\<close> initiates a return.\<close>
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

text \<open>\<open>ret_guarded rok c\<close> is the deep source-only well-formedness check: an explicit
  \<^const>\<open>Return\<close> (or an in-flight \<^const>\<open>Unwind\<close>) is admissible only where \<open>rok\<close> holds ---
  inside a called activation.  Permission is \<^emph>\<open>granted by the activation tail\<close>: the right
  child \<^const>\<open>Restore\<close> of a \<^const>\<open>Seq\<close> marks a callee body, so its left child is checked with
  \<open>rok = True\<close>, whereas ordinary continuations inherit the ambient \<open>rok\<close>.  A bare
  \<^const>\<open>Restore\<close> (the transient tail after the callee body reduces to \<^const>\<open>SKIP\<close>) is always
  admissible.  Crucially this looks \<^emph>\<open>behind\<close> \<^const>\<open>Restore\<close> boundaries: a \<^const>\<open>Return\<close>
  hidden in a base-activation continuation is rejected, which a head-only check misses ---
  exactly the configuration a frame pop would later surface at the base.\<close>
fun ret_guarded :: "bool \<Rightarrow> com \<Rightarrow> bool" where
  "ret_guarded rok SKIP = True"
| "ret_guarded rok (Assign x a) = True"
| "ret_guarded rok (VIMP_Proc.com.Check b) = True"
| "ret_guarded rok (Seq c1 c2) =
     (if c2 = Restore then ret_guarded True c1
      else ret_guarded rok c1 \<and> ret_guarded rok c2)"
| "ret_guarded rok (If b c1 c2) = (ret_guarded rok c1 \<and> ret_guarded rok c2)"
| "ret_guarded rok (While b c) = ret_guarded rok c"
| "ret_guarded rok (Call dst p actuals) = True"
| "ret_guarded rok (Return e) = rok"
| "ret_guarded rok Restore = True"
| "ret_guarded rok Unwind = rok"

lemma ret_guarded_True_source: "source_com c \<Longrightarrow> ret_guarded True c"
  by (induction c) (auto split: if_splits)

lemma ret_guarded_False_source_not_head_return:
  "source_com c \<Longrightarrow> ret_guarded False c \<Longrightarrow> \<not> head_return c"
  by (induction c) (auto split: if_splits)

text \<open>The runtime invariant: the active command is \<^const>\<open>ret_guarded\<close> at the base activation
  (returns forbidden until a call opens one).  Unlike a head-only guard this is preserved by
  \<^const>\<open>pstep\<close>, because it already forbids the base-activation returns that a frame pop
  would expose.\<close>
definition source_wf :: "com \<times> store \<times> frame list \<Rightarrow> bool" where
  "source_wf cfg \<longleftrightarrow> (case cfg of (c, s, frs) \<Rightarrow> ret_guarded False c)"

lemma source_com_no_return_source_wf:
  assumes "source_com c" and "no_return c"
  shows "source_wf (c, s, frs)"
  using assms
  unfolding source_wf_def
  by (induction c) (auto split: if_splits)

lemma source_wf_source_not_head_return:
  "source_wf (c, s, frs) \<Longrightarrow> source_com c \<Longrightarrow> \<not> head_return c"
  by (auto simp: source_wf_def ret_guarded_False_source_not_head_return)

lemma ret_guarded_pstep:
  assumes bodies: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
      and step: "pstep source_global \<Pi> (c, s, frs) (c', s', frs')"
      and "ret_guarded rok c"
  shows "ret_guarded rok c'"
  using step assms(3)
proof (induction "(c, s, frs)" "(c', s', frs')"
       arbitrary: c s frs c' s' frs' rok rule: pstep.induct)
  case Call
  then show ?case using bodies ret_guarded_True_source by auto
next
  case (Seq2 c1 s1 f1 c1' s1' f1' c2)
  then show ?case by (auto split: if_splits)
qed (auto split: if_splits)

lemma source_wf_pstep:
  assumes bodies: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
      and step: "pstep source_global \<Pi> (c, s, frs) (c', s', frs')"
      and wf: "source_wf (c, s, frs)"
  shows "source_wf (c', s', frs')"
  using ret_guarded_pstep[OF bodies step] wf by (simp add: source_wf_def)

lemma unwinding_seq_after_Unwind:
  "(\<forall>a \<in> set afters. a \<noteq> Restore) \<Longrightarrow> unwinding (seq_after Unwind afters)"
  by (induction afters rule: rev_induct) (auto simp: seq_after_snoc)

subsection \<open>Source-step classification\<close>

lemma intra_step_not_returning:
  "intra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> \<not> is_returning c"
  by (induction "(c, s, frs)" "(c', s', frs')" arbitrary: c s frs c' s' frs'
      rule: intra_step.induct) auto

text \<open>A declared procedure's name is never one \<^const>\<open>special_table\<close> also classifies: the
  same disjointness \<open>procs_compiled\<close> bundles below, supplied directly since this lemma sits
  upstream of that definition.  Without it the \<open>pstep.Call\<close> case cannot rule out \<open>c\<close> also
  matching \<open>pstep.Special\<close>, which \<^const>\<open>head_call\<close> excludes.\<close>
lemma pstep_intra_classify:
  assumes disj: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> special_table p = None"
  shows "pstep source_global \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> \<not> head_call c \<Longrightarrow> \<not> head_return c \<Longrightarrow>
   \<not> is_returning c \<Longrightarrow> intra_step \<Pi> (c, s, frs) (c', s', frs')"
proof (induction "(c, s, frs)" "(c', s', frs')"
       arbitrary: c s frs c' s' frs' rule: pstep.induct)
  case (Seq2 c1 s1 f1 c1' s1' f1' c2)
  from Seq2.prems have "\<not> head_call c1" "\<not> head_return c1" "\<not> is_returning c1" by auto
  from Seq2.hyps(2)[OF this] have ih: "intra_step \<Pi> (c1, s1, f1) (c1', s1', f1')" .
  from intra_step_frame_eq[OF ih] ih show ?case by (auto intro: intra_step.ISeq2)
next
  case (Call p decl actuals dst vals callee s1 frs0)
  then show ?case using disj by simp
qed (auto intro: intra_step.intros)

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
    using c2R unwinding_not_SKIP[OF u1w] by auto
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
  case Check   from Check.prems(1)  show ?case by simp
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

lemma pstep_pop_ready_head:
  assumes "pop_ready w" and "pstep source_global \<Pi> (w, s, Frame fr dst # frs) x"
  shows "x = (SKIP, combine_assign dst (s ret_var) (combine_env source_global fr s), frs)
       \<or> (\<exists>w'. x = (w', s, Frame fr dst # frs) \<and> pop_ready w')"
  using assms
proof (cases w rule: pop_ready.cases)
  case 1
  with assms(2) show ?thesis by auto
next
  case (2 u)
  hence uw: "unwinding u" using assms(1) by simp
  from assms(2) show ?thesis
    unfolding 2
    by (elim SeqSE) (auto dest: pstep_unwinding[OF uw] simp: unwinding_not_SKIP[OF uw])
qed (use assms(1) in auto)

text \<open>Proved by \<open>rev_induct\<close>: the outermost \<^const>\<open>Seq\<close> peels off (its left component, a
  \<^const>\<open>seq_after\<close> with active head \<open>w\<close>, is never \<^const>\<open>SKIP\<close> / \<^const>\<open>Unwind\<close>) and the
  induction hypothesis descends the remaining spine.\<close>
lemma pstep_seq_after_headD:
  assumes step: "pstep source_global \<Pi> (seq_after w afters, s, frs) src'"
      and wsk: "w \<noteq> SKIP" and wunw: "w \<noteq> Unwind"
  obtains h' s' fz where
    "src' = (seq_after h' afters, s', fz)"
    "pstep source_global \<Pi> (w, s, frs) (h', s', fz)"
proof -
  have "\<exists>h' s' fz. src' = (seq_after h' afters, s', fz)
          \<and> pstep source_global \<Pi> (w, s, frs) (h', s', fz)"
    using step
  proof (induction afters arbitrary: src' rule: rev_induct)
    case Nil
    then obtain h' s' fz where "src' = (h', s', fz)"
      "pstep source_global \<Pi> (w, s, frs) (h', s', fz)"
      by (cases src') auto
    then show ?case by auto
  next
    case (snoc a xs)
    from snoc.prems have "pstep source_global \<Pi> (Seq (seq_after w xs) a, s, frs) src'"
      by (simp add: seq_after_snoc)
    then obtain B' s' fz where
      A: "src' = (Seq B' a, s', fz)"
        and B: "pstep source_global \<Pi> (seq_after w xs, s, frs) (B', s', fz)"
      using wsk wunw by auto
    from snoc.IH[OF B] obtain h' where
      "B' = seq_after h' xs" "pstep source_global \<Pi> (w, s, frs) (h', s', fz)" by auto
    then show ?case using A by (auto simp: seq_after_snoc)
  qed
  then show ?thesis using that by blast
qed

subsection \<open>Base return completion (frame pop or unwind propagation)\<close>

text \<open>
  One \<^const>\<open>pstep\<close> of a base returning activation \<^term>\<open>seq_after w afters\<close> (\<^term>\<open>pop_ready w\<close>,
  framed by the single caller frame, CFG at \<^term>\<open>FunctionResult p\<close>) either \<^emph>\<open>pops\<close>: the
  source resumes at \<^term>\<open>seq_after SKIP afters\<close> with the combined store and the CFG performs
  exactly one return \<^const>\<open>cstep\<close> to \<open>cont\<close>, rebuilt as a \<open>Base\<close> activation; or
  \<^emph>\<open>propagates\<close>: an \<^const>\<open>Unwind\<close> advances one dead-code layer and the CFG stays at
  \<^term>\<open>FunctionResult p\<close> with \<^emph>\<open>zero\<close> \<^const>\<open>cstep\<close>, rebuilt as a \<open>Returning\<close> activation.
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
              (SKIP, combine_assign dst (callee ret_var) (combine_env source_global caller callee),
               [])"
    hence h': "h' = SKIP" "s' = ?rs" "frs' = []" by (auto simp: combine_collect_def)
    have "cstep source_global g (FunctionResult p, callee, [(cont, dst, caller)]) (cont, ?rs, [])"
      by (rule cstep.Return)
    moreover have "csim \<Pi> g (seq_after SKIP afters, ?rs, []) (cont, ?rs, [])"
      by (rule csim.Base[OF loc cacc pa])
    ultimately show ?thesis using src' h' by auto
  next
    assume "\<exists>w'. (h', s', frs') = (w', callee, [Frame caller dst]) \<and> pop_ready w'"
    then obtain w' where h': "h' = w'" "s' = callee" "frs' = [Frame caller dst]"
        and pr': "pop_ready w'" by auto
    have "csim \<Pi> g (seq_after w' afters, callee, [Frame caller dst])
                   (FunctionResult p, callee, [(cont, dst, caller)])"
      by (rule csim.Returning[OF pr' loc cacc pa])
    with src' h' show ?thesis by auto
  qed
qed

text \<open>A single \<^const>\<open>pstep\<close> touches only the head region of the frame stack, so a bottom
  segment \<open>extra\<close> rides along unchanged when the active part \<open>frs\<close> is non-empty.  This
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

text \<open>The CFG dual: a \<^const>\<open>cstep\<close> also touches only the head of the stack, so an extra
  bottom segment rides along --- with no non-emptiness needed, since the return step already
  requires a non-empty stack.\<close>
lemma cstep_frame_extend:
  "cstep source_global g (u, s, stk) (u', s', stk') \<Longrightarrow>
   cstep source_global g (u, s, stk @ E) (u', s', stk' @ E)"
  by (erule cstep.cases) (auto intro: cstep.intros)

lemma csim_returning_frames_nonempty:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> is_returning c \<Longrightarrow> frs \<noteq> [] \<and> stk \<noteq> []"
  by (erule csim.cases) (auto dest: control_at_not_returning)

subsection \<open>Deep return completion through \<open>Nested\<close> wrappers\<close>

lemma control_at_not_unwind:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r \<noteq> Unwind"
  by (induction rule: control_at.induct) auto

lemma csim_not_unwind:
  "csim \<Pi> g (Unwind, s, frs) cfg' \<Longrightarrow> False"
  by (erule csim.cases) (auto dest: control_at_not_unwind pop_ready_not_Unwind)

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
      using nsk nunw by auto
    then show ?case by auto
  next
    case (snoc a xs)
    from snoc.prems
    have "pstep source_global \<Pi> (Seq (seq_after (Seq inner Restore) xs) a, s, frs) src'"
      by (simp add: seq_after_snoc)
    then obtain B' s' fz where
      A: "src' = (Seq B' a, s', fz)"
        and B: "pstep source_global \<Pi> (seq_after (Seq inner Restore) xs, s, frs) (B', s', fz)"
      by auto
    from snoc.IH[OF B] obtain inner' where
      "B' = seq_after (Seq inner' Restore) xs"
      "pstep source_global \<Pi> (inner, s, frs) (inner', s', fz)" by auto
    then show ?case using A by (auto simp: seq_after_snoc)
  qed
  then show ?thesis using that by blast
qed

lemma csim_returning_completion:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> is_returning c \<Longrightarrow>
   pstep source_global \<Pi> (c, s, frs) src' \<Longrightarrow>
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


end

