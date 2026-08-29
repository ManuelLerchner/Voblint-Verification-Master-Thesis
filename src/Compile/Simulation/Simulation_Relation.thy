theory Simulation_Relation
  imports Residual_Edges
begin

section \<open>What it means for a source state and a graph state to agree\<close>

text \<open>
  \<open>csim\<close> relates a source configuration \<^term>\<open>(c, s, frs)\<close> to a CFG configuration
  \<^term>\<open>(v, s, stk)\<close> holding the very same store.  The two represent suspended callers
  differently: the source nests each caller's continuation inside the single command \<open>c\<close>,
  as \<^term>\<open>Seq (Seq inner Restore) after\<close> wrappings, while the CFG keeps them as
  continuation nodes on its frame stack.  \<open>csim\<close> pairs the two off, one layer per
  suspended caller.

  Both nestings run outermost-first, so the top command layer pairs with the last frame.
  After \<open>main\<close> calls \<open>f\<close> calls \<open>g\<close> the source command is
  \<open>Seq (Seq (Seq (Seq C Restore) B) Restore) A\<close> --- \<open>A\<close> is main's continuation and \<open>C\<close> the
  running residual of \<open>g\<close> --- while the CFG sits at \<open>g\<close>'s node with continuation frames
  \<open>[B's node, A's node]\<close>.

  Three constructors, one per phase an activation can be in.  \<open>Base\<close> relates a single
  activation with nothing beneath it.  \<open>Nested\<close> peels one suspended caller.  \<open>Returning\<close>
  covers the skew just after a callee finishes: the CFG has already reached
  \<^term>\<open>FunctionResult p\<close>, while the source is still propagating \<^const>\<open>Restore\<close> or
  \<^const>\<open>Unwind\<close> towards its frame-pop rule.  Proving that execution preserves \<open>csim\<close> is
  the next theory's business; this one defines the relation and the vocabulary it is
  stated in.
\<close>

subsection \<open>Return-store update\<close>

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

subsection \<open>Bare Unwind is stuck\<close>

text \<open>A lone \<^const>\<open>Unwind\<close> has no source step: only the \<^const>\<open>Seq\<close> rules propagate it, and
  the frame pop it is heading for fires on \<^term>\<open>Seq Unwind Restore\<close>.\<close>
lemma pstep_Unwind_stuck: "\<not> pstep source_global \<Pi> (Unwind, s, frs) x"
  by auto

subsection \<open>The returning (frame-pop) source shapes\<close>

text \<open>
  Once a callee finishes, the CFG is already at \<^term>\<open>FunctionResult p\<close> while the source
  propagates toward the frame-pop rule.  \<open>unwinding\<close> describes an \<^const>\<open>Unwind\<close> travelling
  up through the callee's residual, dropping the dead code it skips (never the activation's
  own \<^const>\<open>Restore\<close>); \<open>pop_ready\<close> describes the whole activation body in that phase ---
  either the normal fall-through \<^const>\<open>Restore\<close> or an \<^const>\<open>Unwind\<close> spine
  \<open>Seq u Restore\<close> from an explicit \<^const>\<open>Return\<close>.  Both pop the single caller frame with one
  \<open>cstep\<close> return; \<open>unwinding\<close> propagation is matched by \<^emph>\<open>no\<close> CFG step, because the CFG
  waits at \<^term>\<open>FunctionResult p\<close>.
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
  \<open>compiled_at \<Pi> g p c0 k n\<close> is an activation's certificate.  It says two things at once,
  because every activation needs both: \<open>c0\<close> is genuinely procedure \<open>p\<close>'s body, and that body,
  compiled at the exact offset \<open>n\<close> with continuation \<open>k\<close>, is embedded in the target graph
  \<open>g\<close> --- its intra edges lie in \<^term>\<open>intra g\<close> and its call edges in \<^term>\<open>calls g\<close>.

  The offset matters because compilation is shift-parametric: neither \<open>n\<close> nor \<open>k\<close> is fixed by
  the syntax, so graph membership \<^emph>\<open>at the chosen offset\<close> is the missing fact and this
  predicate supplies it, at the same \<open>k\<close> and \<open>n\<close> that \<^const>\<open>control_at\<close> uses.  The procedure
  identity matters because \<^const>\<open>control_at\<close>'s fragment parameter is otherwise free, and
  fall-through preservation is false for a fragment that is not a whole body.

  A procedure body's continuation is its epilogue node, which is why the fall-through return
  edge is stated from \<open>k\<close>.  That edge exists only when the body can actually fall through to
  it, so the requirement is guarded by \<^const>\<open>falls_through\<close>;
  \<open>control_at_SKIP_imp_falls_through\<close> discharges the guard wherever a completed
  (\<^const>\<open>SKIP\<close>) residual needs the edge.
\<close>
definition compiled_at ::
  "proc_table \<Rightarrow> cfg \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> cfg_node \<Rightarrow> nat \<Rightarrow> bool" where
  "compiled_at \<Pi> g p c0 k n \<longleftrightarrow>
     (\<exists>decl n' en E K. \<Pi> p = Some decl \<and> c0 = body decl
        \<and> compile \<Pi> p c0 k n = (n', en, E, K)
        \<and> E \<subseteq> intra g \<and> K \<subseteq> calls g
        \<and> (falls_through c0 \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g))"

lemma compiled_atI [intro]:
  "\<Pi> p = Some decl \<Longrightarrow> c0 = body decl \<Longrightarrow>
   compile \<Pi> p c0 k n = (n', en, E, K) \<Longrightarrow> E \<subseteq> intra g \<Longrightarrow> K \<subseteq> calls g \<Longrightarrow>
   (falls_through c0 \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g) \<Longrightarrow>
   compiled_at \<Pi> g p c0 k n"
  unfolding compiled_at_def by blast

lemma compiled_atE [elim]:
  assumes "compiled_at \<Pi> g p c0 k n"
  obtains decl n' en E K where
    "\<Pi> p = Some decl" "c0 = body decl"
    "compile \<Pi> p c0 k n = (n', en, E, K)" "E \<subseteq> intra g" "K \<subseteq> calls g"
    "falls_through c0 \<longrightarrow> (k, EA_Ret None p, FunctionResult p) \<in> intra g"
  using assms unfolding compiled_at_def by blast

text \<open>The procedure-identity half on its own, for the many proofs that only need the
  declaration behind an activation.\<close>
lemma compiled_at_decl:
  assumes "compiled_at \<Pi> g p c0 k n"
  obtains decl where "\<Pi> p = Some decl" "c0 = body decl"
  using assms unfolding compiled_at_def by blast

lemma compiled_at_exit:
  "compiled_at \<Pi> g p c0 k n \<Longrightarrow> falls_through c0 \<Longrightarrow>
   (k, EA_Ret None p, FunctionResult p) \<in> intra g"
  unfolding compiled_at_def by auto

subsection \<open>The simulation relation\<close>

inductive csim :: "proc_table \<Rightarrow> cfg \<Rightarrow> com \<times> store \<times> frame list
                    \<Rightarrow> cfg_node \<times> store \<times> cframe list \<Rightarrow> bool" for \<Pi> g where
  Base:
    "control_at \<Pi> p c0 k n c v \<Longrightarrow> compiled_at \<Pi> g p c0 k n \<Longrightarrow>
     csim \<Pi> g (c, s, []) (v, s, [])"
| Nested:
    "csim \<Pi> g (inner, s, frs) (v, s, stk) \<Longrightarrow>
     control_at \<Pi> pc c0c kc nc (seq_after SKIP afters) cont \<Longrightarrow>
     compiled_at \<Pi> g pc c0c kc nc \<Longrightarrow>
     csim \<Pi> g (seq_after (Seq inner Restore) afters, s, frs @ [Frame caller dst])
              (v, s, stk @ [(cont, dst, caller)])"
| Returning:
    "pop_ready w \<Longrightarrow>
     control_at \<Pi> pc c0c kc nc (seq_after SKIP afters) cont \<Longrightarrow>
     compiled_at \<Pi> g pc c0c kc nc \<Longrightarrow>
     csim \<Pi> g (seq_after w afters, callee, [Frame caller dst])
              (FunctionResult p, callee, [(cont, dst, caller)])"
text \<open>Inversion at an empty source frame stack.  Only \<open>Base\<close> can produce one --- \<open>Nested\<close> and
  \<open>Returning\<close> both append a caller frame --- so the CFG stack is empty too, the stores agree,
  and the whole activation certificate comes back.  \<open>csim\<close>'s introduction rules stay
  undeclared: choosing between \<open>Base\<close>, \<open>Nested\<close> and \<open>Returning\<close> is the step each preservation
  proof exists to make, and it belongs in the proof text rather than in a search.\<close>
inductive_cases csim_empty_stackE [elim]: "csim \<Pi> g (c, s, []) (v, t, stk)"

text \<open>\<open>Nested\<close> and \<open>Returning\<close> both locate the \<^emph>\<open>resumed caller\<close> --- the ordinary residual
  \<^term>\<open>seq_after SKIP afters\<close> that the return will land in --- at the continuation node
  \<open>cont\<close>.  \<open>Returning\<close> carries exactly the one frame the return pops; outer callers are
  consumed by the \<open>Nested\<close> layers wrapping it, and after the pop the caller resumes as a
  \<open>Base\<close> activation with that wrapping untouched.\<close>

lemma csim_store_eq:
  "csim \<Pi> g (c, s, frs) (v, t, stk) \<Longrightarrow> s = t"
  by (induction "(c, s, frs)" "(v, t, stk)" arbitrary: c frs v stk rule: csim.induct) auto

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

text \<open>\<open>ret_guarded allow_return c\<close> is the deep source-only well-formedness check: an explicit
  \<^const>\<open>Return\<close> (or an in-flight \<^const>\<open>Unwind\<close>) is admissible only where \<open>allow_return\<close>
  holds --- inside a called activation.  Permission is \<^emph>\<open>granted by the activation tail\<close>: the
  right child \<^const>\<open>Restore\<close> of a \<^const>\<open>Seq\<close> marks a callee body, so its left child is
  checked with \<open>allow_return = True\<close>, whereas ordinary continuations inherit the ambient
  permission.  A bare \<^const>\<open>Restore\<close> (the transient tail after the callee body reduces to
  \<^const>\<open>SKIP\<close>) is always admissible.  Crucially this looks \<^emph>\<open>behind\<close> \<^const>\<open>Restore\<close>
  boundaries: a \<^const>\<open>Return\<close> hidden in a base-activation continuation is rejected, which a
  head-only check misses --- exactly the configuration a frame pop would later surface at the
  base.\<close>
fun ret_guarded :: "bool \<Rightarrow> com \<Rightarrow> bool" where
  "ret_guarded allow_return SKIP = True"
| "ret_guarded allow_return (Assign x a) = True"
| "ret_guarded allow_return (VIMP_Proc.com.Check b) = True"
| "ret_guarded allow_return (Seq c1 c2) =
     (if c2 = Restore then ret_guarded True c1
      else ret_guarded allow_return c1 \<and> ret_guarded allow_return c2)"
| "ret_guarded allow_return (If b c1 c2) =
     (ret_guarded allow_return c1 \<and> ret_guarded allow_return c2)"
| "ret_guarded allow_return (While b c) = ret_guarded allow_return c"
| "ret_guarded allow_return (Call dst p actuals) = True"
| "ret_guarded allow_return (Return e) = allow_return"
| "ret_guarded allow_return Restore = True"
| "ret_guarded allow_return Unwind = allow_return"

lemma ret_guarded_True_source: "source_com c \<Longrightarrow> ret_guarded True c"
  by (induction c) (auto split: if_splits)

lemma ret_guarded_False_source_not_head_return:
  "source_com c \<Longrightarrow> ret_guarded False c \<Longrightarrow> \<not> head_return c"
  by (induction c) (auto split: if_splits)

lemma ret_guarded_pstep:
  assumes bodies: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
      and step: "pstep source_global \<Pi> (c, s, frs) (c', s', frs')"
      and "ret_guarded allow_return c"
  shows "ret_guarded allow_return c'"
  using step assms(3)
proof (induction "(c, s, frs)" "(c', s', frs')"
       arbitrary: c s frs c' s' frs' allow_return rule: pstep.induct)
  case Call
  then show ?case using bodies ret_guarded_True_source by auto
next
  case (Seq2 c1 s1 f1 c1' s1' f1' c2)
  then show ?case by (auto split: if_splits)
qed (auto split: if_splits)

text \<open>The runtime invariant \<open>csim_step\<close> asks for: the active command may not return until a
  call has opened an activation for it.  Only the command matters --- neither the store nor
  the frame stack --- and unlike a head-only guard this survives a \<^const>\<open>pstep\<close>, because it
  already forbids the base-activation returns that a frame pop would expose.\<close>
definition return_safe :: "com \<Rightarrow> bool" where
  "return_safe c \<longleftrightarrow> ret_guarded False c"

lemma return_safe_if_no_return:
  assumes "source_com c" and "no_return c"
  shows "return_safe c"
  using assms
  unfolding return_safe_def
  by (induction c) (auto split: if_splits)

lemma return_safe_not_head_return:
  "return_safe c \<Longrightarrow> source_com c \<Longrightarrow> \<not> head_return c"
  by (auto simp: return_safe_def ret_guarded_False_source_not_head_return)

lemma return_safe_pstep:
  assumes bodies: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> source_com (body decl)"
      and step: "pstep source_global \<Pi> (c, s, frs) (c', s', frs')"
      and wf: "return_safe c"
  shows "return_safe c'"
  using ret_guarded_pstep[OF bodies step] wf by (simp add: return_safe_def)

lemma unwinding_seq_after_Unwind:
  "(\<forall>a \<in> set afters. a \<noteq> Restore) \<Longrightarrow> unwinding (seq_after Unwind afters)"
  by (induction afters rule: rev_induct) (auto simp: seq_after_snoc)

subsection \<open>Source-step classification\<close>

lemma intra_step_not_returning:
  "intra_step \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> \<not> is_returning c"
  by (induction "(c, s, frs)" "(c', s', frs')" arbitrary: c s frs c' s' frs'
      rule: intra_step.induct) auto

text \<open>A declared procedure's name is never one \<^const>\<open>special_table\<close> also classifies: the
  same disjointness \<open>procs_embedded\<close> bundles in the next theory, supplied directly since this
  lemma sits upstream of that definition.  Without it the \<open>pstep.Call\<close> case cannot rule out
  \<open>c\<close> also matching \<open>pstep.Special\<close>, which \<^const>\<open>head_call\<close> excludes.\<close>
lemma pstep_intra_classify:
  assumes disj: "\<And>p decl. \<Pi> p = Some decl \<Longrightarrow> special_table p = None"
  shows "pstep source_global \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> \<not> head_call c \<Longrightarrow> \<not> head_return c \<Longrightarrow>
   \<not> is_returning c \<Longrightarrow> intra_step \<Pi> (c, s, frs) (c', s', frs')"
proof (induction "(c, s, frs)" "(c', s', frs')"
       arbitrary: c s frs c' s' frs' rule: pstep.induct)
  case (Seq2 c1 s1 f1 c1' s1' f1' c2)
  from Seq2.prems have "\<not> head_call c1" "\<not> head_return c1" "\<not> is_returning c1" by auto
  from Seq2.hyps(2)[OF this] have ih: "intra_step \<Pi> (c1, s1, f1) (c1', s1', f1')" .
  from intra_step_frame_eq[OF ih] ih show ?case by auto
next
  case (Call p decl actuals dst vals callee s1 frs0)
  then show ?case using disj by simp
qed auto

lemma control_at_not_returning:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> \<not> is_returning r"
  by (induction rule: control_at.induct) auto

lemma control_at_not_unwind:
  "control_at \<Pi> p c0 k n r v \<Longrightarrow> r \<noteq> Unwind"
  using control_at_not_returning by fastforce

text \<open>\<open>is_returning\<close> classifies the active head.  The \<open>unwinding\<close> and \<open>pop_ready\<close> predicates
  refine that class with the nested residual shape needed by frame-pop proofs; they
  deliberately overlap instead of forming a phase partition.\<close>
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

subsection \<open>Stepping through a \<open>seq_after\<close> spine\<close>

text \<open>A step of a \<^const>\<open>seq_after\<close> spine is a step of its head, with the pending
  continuations carried along untouched.  \<^const>\<open>SKIP\<close> and \<^const>\<open>Unwind\<close> heads are excluded
  because those relocate into the spine instead of stepping in place.\<close>
lemma pstep_seq_after_headE [elim]:
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

end
