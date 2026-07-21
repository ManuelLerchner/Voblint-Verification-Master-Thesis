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
  context-sensitive/insensitive bridge, and concrete regression witnesses.

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
    \<union> {Call caller [(FunctionEntry p, enter_state (sink_store caller))]
          | caller dst args p cont.
          caller \<in> T \<and> (sink_node caller, CallEdge dst args, FunctionEntry p, cont) \<in> calls g}
    \<union> {Resume caller callee
          (path caller @ [(cont, combine_collect dst (sink_store caller) (sink_store callee))])
          | callee caller p dst args cont.
          callee \<in> T \<and> caller_of callee = Some caller
          \<and> sink_node callee = FunctionResult p
          \<and> (sink_node caller, CallEdge dst args, FunctionEntry p, cont) \<in> calls g}"

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
    case (call caller dst args p cont)
    have "Call caller [(FunctionEntry p, enter_state (sink_store caller))]
            \<in> ltr_F g S (lfp (ltr_F g S))"
      unfolding ltr_F_def[of g S "lfp (ltr_F g S)"] using call.hyps call.IH by blast
    then show ?case by (rule ltr_F_lfp_fold)
  next
    case (ret callee caller p dst args cont)
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
    and "(u, CallEdge dst args, FunctionEntry p, cont) \<in> calls g"
  shows "enter_state s \<in> ltr_collect g S (FunctionEntry p)"
proof -
  from assms(1) obtain t where t: "t \<in> valid_ltr g S" "sink_node t = u" "sink_store t = s"
    by (rule ltr_collect_E)
  have "Call t [(FunctionEntry p, enter_state (sink_store t))] \<in> valid_ltr g S"
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
    and "(sink_node caller, CallEdge dst args, FunctionEntry p, cont) \<in> calls g"
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
  "key enterc seedc (Call caller [(FunctionEntry p, enter_state (sink_store caller))])
     = enterc (key enterc seedc caller) (enter_state (sink_store caller))"
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

subsection \<open>Regression witnesses\<close>

text \<open>Multiple returns: two distinct intra branches reach \<open>FunctionResult pf\<close>, both states
  occur in \<open>ltr_collect (FunctionResult pf)\<close>, and both resume through the same continuation.
  Built on \<^const>\<open>valid_ltr\<close> witness \<open>multi_return_join\<close>.\<close>
lemma ltr_collect_multi_return:
  "\<exists>s1 s2 r1 r2.
      s1 \<in> ltr_collect mret_cfg UNIV (FunctionResult pf)
    \<and> s2 \<in> ltr_collect mret_cfg UNIV (FunctionResult pf)
    \<and> r1 \<in> ltr_collect mret_cfg UNIV (Statement 100)
    \<and> r2 \<in> ltr_collect mret_cfg UNIV (Statement 100)"
proof -
  from multi_return_join obtain t1 t2 c1 c2 where
    T1: "t1 \<in> valid_ltr mret_cfg UNIV" and T2: "t2 \<in> valid_ltr mret_cfg UNIV"
    and sn1: "sink_node t1 = FunctionResult pf" and sn2: "sink_node t2 = FunctionResult pf"
    and R1: "Resume c1 t1 (path c1 @ [(Statement 100, combine_collect None (sink_store c1) (sink_store t1))])
               \<in> valid_ltr mret_cfg UNIV"
    and R2: "Resume c2 t2 (path c2 @ [(Statement 100, combine_collect None (sink_store c2) (sink_store t2))])
               \<in> valid_ltr mret_cfg UNIV"
    by blast
  have "sink_store t1 \<in> ltr_collect mret_cfg UNIV (FunctionResult pf)"
    using ltr_collect_I[OF T1] sn1 by simp
  moreover have "sink_store t2 \<in> ltr_collect mret_cfg UNIV (FunctionResult pf)"
    using ltr_collect_I[OF T2] sn2 by simp
  moreover have "combine_collect None (sink_store c1) (sink_store t1)
                   \<in> ltr_collect mret_cfg UNIV (Statement 100)"
    using ltr_collect_I[OF R1] by (simp add: sink_node_def sink_store_def)
  moreover have "combine_collect None (sink_store c2) (sink_store t2)
                   \<in> ltr_collect mret_cfg UNIV (Statement 100)"
    using ltr_collect_I[OF R2] by (simp add: sink_node_def sink_store_def)
  ultimately show ?thesis by blast
qed

text \<open>Recursion: two nested activations of \<open>pr\<close> are distinct structural traces; under the
  discriminating context \<open>key (\<lambda>c _. Suc c) 0\<close> (call depth) they receive distinct context
  keys.  Built on \<^const>\<open>valid_ltr\<close> witness \<open>recursion_nesting\<close>.\<close>
lemma ltr_collect_recursion_distinct_ctx:
  "\<exists>outer inner.
      outer \<in> valid_ltr rec_cfg UNIV \<and> inner \<in> valid_ltr rec_cfg UNIV
    \<and> outer \<noteq> inner
    \<and> key (\<lambda>c _. Suc c) 0 outer \<noteq> key (\<lambda>c _. Suc c) 0 inner"
proof -
  define s0 :: store where "s0 = (\<lambda>_. 0)(''Gx'' := 1)"
  define root where "root = Root [(cfg_entry rec_cfg, s0)]"
  have R: "root \<in> valid_ltr rec_cfg UNIV" unfolding root_def by (rule valid_ltr.init) simp
  have rt_sn: "sink_node root = FunctionEntry pr" by (simp add: root_def rec_defs)
  have eA: "(sink_node root, EA_Assume bpos, Statement 1) \<in> intra rec_cfg"
    by (simp add: rt_sn rec_defs)
  have stepA: "edge_step (EA_Assume bpos) (sink_store root) = Some (sink_store root)"
    by (simp add: root_def rec_defs s0_def enter_state_def is_global_def)
  define outer where "outer = extend root (Statement 1, sink_store root)"
  have OUTER: "outer \<in> valid_ltr rec_cfg UNIV"
    unfolding outer_def by (rule valid_ltr.intra[OF R eA stepA])
  have so: "sink_node outer = Statement 1" by (simp add: outer_def)
  have ecall: "(sink_node outer, CallEdge None [], FunctionEntry pr, Statement 200) \<in> calls rec_cfg"
    by (simp add: so rec_defs)
  define inner where "inner = Call outer [(FunctionEntry pr, enter_state (sink_store outer))]"
  have INNER: "inner \<in> valid_ltr rec_cfg UNIV"
    unfolding inner_def by (rule valid_ltr.call[OF OUTER ecall])
  have neq: "outer \<noteq> inner" by (simp add: outer_def inner_def)
  \<comment> \<open>outer is a Root (call depth 0); inner is a Call of outer (call depth 1)\<close>
  have kouter: "key (\<lambda>c _. Suc c) 0 outer = 0" by (simp add: outer_def root_def)
  have kinner: "key (\<lambda>c _. Suc c) 0 inner = Suc 0"
    by (simp add: inner_def outer_def root_def)
  have "key (\<lambda>c _. Suc c) 0 outer \<noteq> key (\<lambda>c _. Suc c) 0 inner"
    using kouter kinner by simp
  then show ?thesis using OUTER INNER neq by blast
qed

text \<open>Flat CFG: for a \<open>calls = {}\<close> graph the collector agrees with ordinary intra
  reachability.  \<open>flat_demo\<close> is a two-edge straight line; both edge targets are collected
  exactly as intra propagation yields, and no call-derived activation exists.\<close>

definition flat_demo :: cfg where
  "flat_demo =
     \<lparr> intra = { (Statement 0, EA_Nop, Statement 1), (Statement 1, EA_Nop, Statement 2) },
       calls = {},
       cfg_entry = Statement 0 \<rparr>"

lemma flat_demo_flat: "flat_cfg flat_demo"
  by (simp add: flat_cfg_def flat_demo_def)

lemma ltr_collect_flat_demo:
  fixes s0 :: store
  shows "s0 \<in> ltr_collect flat_demo {s0} (Statement 0)"
    and "s0 \<in> ltr_collect flat_demo {s0} (Statement 1)"
    and "s0 \<in> ltr_collect flat_demo {s0} (Statement 2)"
proof -
  show c0: "s0 \<in> ltr_collect flat_demo {s0} (Statement 0)"
    using ltr_collect_init[of s0 "{s0}" flat_demo] by (simp add: flat_demo_def)
  have e0: "(Statement 0, EA_Nop, Statement 1) \<in> intra flat_demo" by (simp add: flat_demo_def)
  show c1: "s0 \<in> ltr_collect flat_demo {s0} (Statement 1)"
    using ltr_collect_intra[OF c0 e0] by simp
  have e1: "(Statement 1, EA_Nop, Statement 2) \<in> intra flat_demo" by (simp add: flat_demo_def)
  show "s0 \<in> ltr_collect flat_demo {s0} (Statement 2)"
    using ltr_collect_intra[OF c1 e1] by simp
qed

lemma ltr_collect_flat_demo_no_call:
  "Call caller p \<notin> valid_ltr flat_demo S"
  using valid_ltr_flat_no_call[OF flat_demo_flat] by blast

end

