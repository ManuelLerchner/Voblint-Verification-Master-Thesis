theory LTR_Collect
  imports CFG_Local_Trace
begin

section \<open>Local-trace collecting semantics\<close>

text \<open>
  The stack-faithful concrete carrier of a procedure-aware CFG is the local-trace set
  \<^const>\<open>valid_ltr\<close>.  This theory presents it as a least fixed point of an explicit
  monotone set transformer \<open>ltr_F\<close>, defines the plain and keyed forgetful projections of
  a trace set to a CFG node (\<open>ltr_collect\<close> / \<open>ltr_collect_keyed\<close>, the concrete and
  context-indexed collectors), and proves the collecting equations, the
  context-sensitive/insensitive bridge.

  \<open>ltr_F\<close> has exactly the four clauses of \<^const>\<open>valid_ltr\<close> (root, intra step, call,
  return), each reading exactly the relation for its phenomenon: \<open>intra\<close> for local
  extension, \<open>calls\<close> for entering a callee and for recovering a continuation.  The return
  clause mirrors \<open>valid_ltr.ret\<close> literally --- it recovers the caller from the completed
  callee's own ancestry through \<^const>\<open>caller_of\<close>, never by an independent choice, and
  matches the callee's \<open>FunctionResult p\<close> against a concrete \<open>calls\<close> edge.

  There is no global exit node: whole-program completion is collection at
  \<open>FunctionResult main\<close>, and a procedure result is an ordinary collected node, not a
  separate summary mechanism.  No solver, DG, or abstract-domain theory is imported.
\<close>

subsection \<open>The constructor transformer\<close>

definition ltr_F :: "cfg \<Rightarrow> store set \<Rightarrow> ltr set \<Rightarrow> ltr set" where
  "ltr_F g S T =
      {Root [(cfg_entry g, s)] | s. s \<in> S}
    \<union> {extend t (v, s') | t a v s'.
          t \<in> T \<and> (sink_node t, a, v) \<in> intra g \<and> edge_step a (sink_store t) = Some s'}
    \<union> {Call caller [(FunctionEntry p, call_enter (CallEdge dst pars args) (sink_store caller))]
          | caller dst pars args p cont.
          caller \<in> T \<and> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g}
    \<union> {Resume caller callee
          (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))])
          | callee caller p dst pars args cont.
          callee \<in> T \<and> caller_of callee = Some caller
          \<and> sink_node callee = FunctionResult p
          \<and> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g}"

subsection \<open>Monotonicity\<close>

lemma ltr_F_mono: "mono (ltr_F g S)"
proof (rule monoI)
  fix T T' :: "ltr set"
  assume "T \<subseteq> T'"
  then show "ltr_F g S T \<subseteq> ltr_F g S T'"
    unfolding ltr_F_def by blast
qed

lemma ltr_F_lfp_fold:
  "x \<in> ltr_F g S (lfp (ltr_F g S)) \<Longrightarrow> x \<in> lfp (ltr_F g S)"
  by (subst lfp_unfold[OF ltr_F_mono]) assumption

subsection \<open>Fixed-point characterization\<close>

text \<open>\<open>ltr_F\<close> maps \<^const>\<open>valid_ltr\<close> into itself: each summand is discharged by the
  corresponding \<^const>\<open>valid_ltr\<close> introduction rule.\<close>
lemma ltr_F_valid_ltr_closed:
  "ltr_F g S (valid_ltr g S) \<subseteq> valid_ltr g S"
  unfolding ltr_F_def
  by (blast intro: valid_ltr.intros)

lemma lfp_ltr_F_subset_valid_ltr:
  "lfp (ltr_F g S) \<subseteq> valid_ltr g S"
  by (rule lfp_lowerbound) (rule ltr_F_valid_ltr_closed)

text \<open>The converse follows by \<^const>\<open>valid_ltr\<close> rule induction: every constructor step lands
  in \<open>ltr_F g S (lfp (ltr_F g S))\<close> via the induction hypotheses, then folds back into the
  least fixed point.\<close>
lemma valid_ltr_subset_lfp:
  "valid_ltr g S \<subseteq> lfp (ltr_F g S)"
proof
  fix t assume "t \<in> valid_ltr g S"
  then show "t \<in> lfp (ltr_F g S)"
  proof (induction rule: valid_ltr.induct)
    case (init s)
    have "Root [(cfg_entry g, s)] \<in> ltr_F g S (lfp (ltr_F g S))"
      unfolding ltr_F_def[of g S "lfp (ltr_F g S)"] using init by blast
    then show ?case by (rule ltr_F_lfp_fold)
  next
    case (intra t a v s')
    have "extend t (v, s') \<in> ltr_F g S (lfp (ltr_F g S))"
      unfolding ltr_F_def[of g S "lfp (ltr_F g S)"] using intra.hyps intra.IH by blast
    then show ?case by (rule ltr_F_lfp_fold)
  next
    case (call caller dst pars args p cont)
    have "Call caller [(FunctionEntry p, call_enter (CallEdge dst pars args) (sink_store caller))]
            \<in> ltr_F g S (lfp (ltr_F g S))"
      unfolding ltr_F_def[of g S "lfp (ltr_F g S)"] using call.hyps call.IH by blast
    then show ?case by (rule ltr_F_lfp_fold)
  next
    case (ret callee caller p dst pars args cont)
    have "Resume caller callee
            (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))])
            \<in> ltr_F g S (lfp (ltr_F g S))"
      unfolding ltr_F_def[of g S "lfp (ltr_F g S)"] using ret.hyps ret.IH by blast
    then show ?case by (rule ltr_F_lfp_fold)
  qed
qed

theorem valid_ltr_eq_lfp:
  "valid_ltr g S = lfp (ltr_F g S)"
  by (rule antisym[OF valid_ltr_subset_lfp lfp_ltr_F_subset_valid_ltr])

subsection \<open>Forgetful projections\<close>

text \<open>\<open>ltr_collect\<close> is the concrete collecting view: the sink stores of valid traces
  reaching node \<open>v\<close>.  \<open>ltr_collect_keyed\<close> is the context-indexed collector, filtering
  those by a trace reader \<open>keyf\<close>.  The key type is not required finite; a keyed bucket is
  not claimed to be an exact activation identity.\<close>

definition ltr_collect :: "cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> store set" where
  "ltr_collect g S v =
     {sink_store t | t. t \<in> valid_ltr g S \<and> sink_node t = v}"

definition ltr_collect_keyed ::
  "(ltr \<Rightarrow> 'c) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> 'c \<Rightarrow> store set" where
  "ltr_collect_keyed keyf g S v c =
     {sink_store t | t. t \<in> valid_ltr g S \<and> sink_node t = v \<and> keyf t = c}"

text \<open>\<open>collect_result\<close> is a convenience view --- collection at a procedure result --- not a
  distinct mechanism.  Whole-program completion is \<open>collect_result g S main\<close>.\<close>
definition collect_result :: "cfg \<Rightarrow> store set \<Rightarrow> pname \<Rightarrow> store set" where
  "collect_result g S p = ltr_collect g S (FunctionResult p)"

lemma ltr_collect_I:
  "t \<in> valid_ltr g S \<Longrightarrow> sink_store t \<in> ltr_collect g S (sink_node t)"
  unfolding ltr_collect_def by blast

text \<open>Every collected state has a valid trace witness.\<close>
lemma ltr_collect_E:
  assumes "s \<in> ltr_collect g S v"
  obtains t where "t \<in> valid_ltr g S" "sink_node t = v" "sink_store t = s"
  using assms unfolding ltr_collect_def by blast

lemma ltr_collect_keyed_le_collect:
  "ltr_collect_keyed keyf g S v c \<subseteq> ltr_collect g S v"
  unfolding ltr_collect_keyed_def ltr_collect_def by blast

text \<open>
  \<^const>\<open>ltr_collect\<close> is closed under intra flow: extending a witness trace by one
  \<^const>\<open>intra\<close> edge is \<open>valid_ltr.intra\<close>.  Closure under \<^emph>\<open>call\<close> and \<^emph>\<open>return\<close> steps is
  deliberately absent here --- \<open>valid_ltr.ret\<close> requires the popped activation to be the
  witness trace's own caller, which a bare CFG step does not supply.
\<close>

lemma ltr_collect_intra_step:
  assumes s: "s \<in> ltr_collect g S u"
    and e: "(u, a, v) \<in> intra g"
    and st: "edge_step a s = Some s'"
  shows "s' \<in> ltr_collect g S v"
proof -
  from s obtain t where t: "t \<in> valid_ltr g S" and n: "sink_node t = u" and w: "sink_store t = s"
    by (rule ltr_collect_E)
  have "extend t (v, s') \<in> valid_ltr g S"
    by (rule valid_ltr.intra[OF t]) (use e st n w in simp_all)
  from ltr_collect_I[OF this] show ?thesis by simp
qed

text \<open>The whole-path form: an \<^const>\<open>intra_path\<close> transports a collected store to its endpoint.\<close>

lemma ltr_collect_intra_path_pair:
  "intra_path g x y \<Longrightarrow> snd x \<in> ltr_collect g S (fst x) \<Longrightarrow> snd y \<in> ltr_collect g S (fst y)"
proof (induction rule: star.induct)
  case (refl x)
  then show ?case by simp
next
  case (step x y z)
  obtain u s where x: "x = (u, s)" by (cases x)
  obtain w s1 where y: "y = (w, s1)" by (cases y)
  from step.hyps(1) x y obtain a where
    e: "(u, a, w) \<in> intra g" and st: "edge_step a s = Some s1"
    by (auto elim: cfg_intra_stepE)
  have "s1 \<in> ltr_collect g S w"
    using step.prems x by (auto intro: ltr_collect_intra_step[OF _ e st])
  then show ?case using step.IH y by simp
qed

lemma ltr_collect_intra_path:
  assumes "intra_path g (u, s) (v, s')" and "s \<in> ltr_collect g S u"
  shows "s' \<in> ltr_collect g S v"
  using ltr_collect_intra_path_pair[OF assms(1)] assms(2) by simp

text \<open>
  The activation-preserving form.  Following an \<^const>\<open>intra_path\<close> only \<open>extend\<close>s the trace, so
  the resulting witness is the \<^emph>\<open>same\<close> activation: same caller and same entry node.  Callers
  that must know \<^emph>\<open>which\<close> activation reached a node need this, not \<open>ltr_collect_intra_path\<close> ---
  the collection at a node merges every activation that reaches it.
\<close>

lemma valid_ltr_intra_path_extend_pair:
  "intra_path g x y \<Longrightarrow> t \<in> valid_ltr g S \<Longrightarrow> sink_node t = fst x \<Longrightarrow> sink_store t = snd x
   \<Longrightarrow> \<exists>t'. t' \<in> valid_ltr g S \<and> sink_node t' = fst y \<and> sink_store t' = snd y
            \<and> caller_of t' = caller_of t \<and> fst (hd (path t')) = fst (hd (path t))"
proof (induction arbitrary: t rule: star.induct)
  case (refl x)
  then show ?case by blast
next
  case (step x y z)
  obtain u s where x: "x = (u, s)" by (cases x)
  obtain w s1 where y: "y = (w, s1)" by (cases y)
  from step.hyps(1) x y obtain a where
    e: "(u, a, w) \<in> intra g" and st: "edge_step a s = Some s1"
    by (auto elim: cfg_intra_stepE)
  have ext: "extend t (w, s1) \<in> valid_ltr g S"
    by (rule valid_ltr.intra[OF step.prems(1)])
       (use e st step.prems(2,3) x in simp_all)
  have hd_ext: "fst (hd (path (extend t (w, s1)))) = fst (hd (path t))"
    using valid_ltr_path_nonempty[OF step.prems(1)] by simp
  from step.IH[OF ext] y obtain t' where
    "t' \<in> valid_ltr g S" "sink_node t' = fst z" "sink_store t' = snd z"
    "caller_of t' = caller_of (extend t (w, s1))"
    "fst (hd (path t')) = fst (hd (path (extend t (w, s1))))" by auto
  then show ?case using hd_ext by auto
qed

lemma valid_ltr_intra_path_extend:
  assumes p: "intra_path g (sink_node t, sink_store t) (v, s')"
    and t: "t \<in> valid_ltr g S"
  obtains t' where "t' \<in> valid_ltr g S" "sink_node t' = v" "sink_store t' = s'"
    "caller_of t' = caller_of t" "fst (hd (path t')) = fst (hd (path t))"
  using valid_ltr_intra_path_extend_pair[OF p t] by auto

lemma collect_result_eq:
  "collect_result g S p = ltr_collect g S (FunctionResult p)"
  by (simp add: collect_result_def)

subsection \<open>Collecting equations\<close>

text \<open>(1) Initial stores are collected at \<^const>\<open>cfg_entry\<close>.\<close>
lemma ltr_collect_init:
  "s \<in> S \<Longrightarrow> s \<in> ltr_collect g S (cfg_entry g)"
  using ltr_collect_I[OF valid_ltr.init] by simp

text \<open>(2) Intra propagation: a collected source state and a successful \<^const>\<open>edge_step\<close>
  produce a collected target state.\<close>
lemma ltr_collect_intra:
  assumes "s \<in> ltr_collect g S u" and "(u, a, v) \<in> intra g"
    and "edge_step a s = Some s'"
  shows "s' \<in> ltr_collect g S v"
proof -
  from assms(1) obtain t where t: "t \<in> valid_ltr g S" "sink_node t = u" "sink_store t = s"
    by (rule ltr_collect_E)
  have "extend t (v, s') \<in> valid_ltr g S"
    by (rule valid_ltr.intra[OF t(1)]) (use assms(2,3) t(2,3) in simp_all)
  from ltr_collect_I[OF this] show ?thesis by simp
qed

text \<open>(3) Call entry: a collected call-site state produces the entered state at the
  callee's \<^const>\<open>FunctionEntry\<close>.\<close>
lemma ltr_collect_call:
  assumes "s \<in> ltr_collect g S u"
    and "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  shows "call_enter (CallEdge dst pars args) s \<in> ltr_collect g S (FunctionEntry p)"
proof -
  from assms(1) obtain t where t: "t \<in> valid_ltr g S" "sink_node t = u" "sink_store t = s"
    by (rule ltr_collect_E)
  have "Call t [(FunctionEntry p, call_enter (CallEdge dst pars args) (sink_store t))] \<in> valid_ltr g S"
    by (rule valid_ltr.call[OF t(1)]) (use assms(2) t(2) in simp)
  from ltr_collect_I[OF this] show ?thesis using t(3) by simp
qed

text \<open>(4) Procedure result: \<^const>\<open>EA_Ret\<close> propagation collects the resulting state at
  \<^const>\<open>FunctionResult\<close> through the ordinary intra rule --- a specialisation of (2).\<close>
lemma ltr_collect_result_via_ret:
  assumes "s \<in> ltr_collect g S u" and "(u, EA_Ret e p, FunctionResult p) \<in> intra g"
    and "edge_step (EA_Ret e p) s = Some s'"
  shows "s' \<in> ltr_collect g S (FunctionResult p)"
  by (rule ltr_collect_intra[OF assms])

text \<open>(5) Resume: a collected completed callee activation produces the combined state at the
  exact continuation of its originating call edge.\<close>
lemma ltr_collect_resume:
  assumes "callee \<in> valid_ltr g S" and "caller_of callee = Some caller"
    and "sink_node callee = FunctionResult p"
    and "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  shows "combine_collect dst (sink_store caller) (sink_store callee) \<in> ltr_collect g S cont"
proof -
  have "Resume caller callee
          (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))])
        \<in> valid_ltr g S"
    by (rule valid_ltr.ret[OF assms])
  from ltr_collect_I[OF this] show ?thesis by (simp add: sink_node_def sink_store_def)
qed

text \<open>(6) Context preservation under intra: an intra extension does not change the
  activation key.\<close>
lemma ltr_collect_ctx_intra_pres:
  "path t \<noteq> [] \<Longrightarrow> key enterc seedc (extend t (v, s')) = key enterc seedc t"
  by (rule key_extend_nonempty)

text \<open>(7) Context transition under call: the child activation receives exactly the context
  produced by the configured enter function.\<close>
lemma ltr_collect_ctx_call:
  "key enterc seedc (Call caller [(FunctionEntry p, call_enter (CallEdge dst pars args) (sink_store caller))])
     = enterc (key enterc seedc caller) (call_enter (CallEdge dst pars args) (sink_store caller))"
  by simp

text \<open>(8) Context restoration under resume: a resumed trace has the caller's activation
  context, not the callee's.\<close>
lemma ltr_collect_ctx_resume:
  "key enterc seedc (Resume caller callee p) = key enterc seedc caller"
  by simp

text \<open>(9) Flat reduction: for \<open>calls g = {}\<close>, no call-derived activation exists, so
  collection is exactly the sink stores of root/intra traces.\<close>
lemma valid_ltr_flat_no_call:
  "flat_cfg g \<Longrightarrow> Call caller p \<notin> valid_ltr g S"
  using valid_ltr_flat_root by blast

lemma valid_ltr_flat_no_resume:
  "flat_cfg g \<Longrightarrow> Resume caller callee p \<notin> valid_ltr g S"
  using valid_ltr_flat_root by blast

lemma ltr_collect_flat:
  assumes "flat_cfg g"
  shows "ltr_collect g S v = {sink_store t | t. t \<in> valid_ltr g S \<and> (\<exists>q. t = Root q) \<and> sink_node t = v}"
  using assms valid_ltr_flat_root unfolding ltr_collect_def by blast

text \<open>(10) Node domain: collection outside \<^const>\<open>cfg_nodes\<close> is empty.\<close>
lemma ltr_collect_outside_nodes:
  "v \<notin> cfg_nodes g \<Longrightarrow> ltr_collect g S v = {}"
  using valid_ltr_sink_in_nodes unfolding ltr_collect_def by blast

text \<open>(11) Monotonicity in the initial stores.\<close>
lemma ltr_collect_mono_S:
  "S \<subseteq> S' \<Longrightarrow> ltr_collect g S v \<subseteq> ltr_collect g S' v"
  using valid_ltr_mono_S unfolding ltr_collect_def by blast

text \<open>(12) Union in the initial stores.\<close>
lemma ltr_collect_Un_S:
  "ltr_collect g (S \<union> S') v = ltr_collect g S v \<union> ltr_collect g S' v"
  using valid_ltr_Un_S unfolding ltr_collect_def by blast

subsection \<open>Context-sensitive / context-insensitive bridge\<close>

text \<open>The keyed buckets tile the plain view: every trace has a key, so ranging over all keys
  recovers the unfiltered collecting.  No finiteness assumption.\<close>
theorem ltr_collect_keyed_Union:
  "(\<Union>c. ltr_collect_keyed keyf g S v c) = ltr_collect g S v"
  unfolding ltr_collect_keyed_def ltr_collect_def by blast

theorem activation_collect_eq_ltr_collect_keyed:
  "activation_collect enterc seedc g S v c
     = ltr_collect_keyed (key enterc seedc) g S v c"
  unfolding activation_collect_def ltr_collect_keyed_def by simp

text \<open>Bridge (1): context-sensitive collection is included in context-insensitive
  collection.\<close>
theorem activation_collect_le_ltr_collect:
  "activation_collect enterc seedc g S v c \<subseteq> ltr_collect g S v"
  unfolding activation_collect_eq_ltr_collect_keyed by (rule ltr_collect_keyed_le_collect)

text \<open>Bridge (2): context-insensitive collection is the union over contexts.\<close>
theorem ltr_collect_eq_Union_activation:
  "ltr_collect g S v = (\<Union>c. activation_collect enterc seedc g S v c)"
  unfolding activation_collect_eq_ltr_collect_keyed by (rule ltr_collect_keyed_Union[symmetric])

subsection \<open>Matched returns\<close>

text \<open>Every reachable \<^const>\<open>Resume\<close> preserves the caller recovered from its completed
  callee.\<close>
theorem valid_ltr_Resume_caller_matched:
  "Resume caller callee p \<in> valid_ltr g S \<Longrightarrow> caller_of callee = Some caller"
  using valid_ltr_Resume_fields by blast


end

