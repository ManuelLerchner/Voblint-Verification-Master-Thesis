theory LTR_Collect
  imports LTR_Def Activation_Context
begin

section \<open>Which stores can occur at each node\<close>

text \<open>
  \<open>ltr_collect gs g S v\<close> is the set of stores a run can actually have at node \<open>v\<close>: take
  every valid trace that ends there and keep its final store.  This is the concrete set an
  analysis has to over-approximate, so it is the target of every soundness statement
  downstream.

  \<^const>\<open>valid_ltr\<close> is also re-presented here as the least fixed point of an explicit
  monotone transformer \<open>ltr_F\<close>, which is what makes induction over "everything reachable"
  available.  \<open>ltr_F\<close> has exactly the four clauses of \<^const>\<open>valid_ltr\<close> --- root, intra
  step, call, return --- each reading exactly the relation for its phenomenon: \<open>intra\<close> for
  local extension, \<open>calls\<close> for entering a callee and for recovering a continuation.  The
  return clause recovers the caller from the completed callee's own ancestry through
  \<^const>\<open>caller_of\<close>, never by an independent choice.

  There is no global exit node: whole-program completion is collection at
  \<open>FunctionResult main\<close>, and a procedure result is an ordinary collected node rather than a
  separate summary mechanism.
\<close>

subsection \<open>The constructor transformer\<close>

definition ltr_F :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> ltr set \<Rightarrow> ltr set" where
  "ltr_F gs g S T =
      {Root [(cfg_entry g, s)] | s. s \<in> S}
    \<union> {extend t (v, s') | t a v s'.
          t \<in> T \<and> (sink_node t, a, v) \<in> intra g \<and> s' \<in> edge_step a (sink_store t)}
    \<union> {Call caller [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))]
          | caller dst pars args p cont.
          caller \<in> T \<and> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g}
    \<union> {Resume caller callee
          (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))])
          | callee caller p dst pars args cont.
          callee \<in> T \<and> caller_of callee = Some caller
          \<and> sink_node callee = FunctionResult p
          \<and> (sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g}"

subsection \<open>Monotonicity\<close>

lemma ltr_F_mono: "mono (ltr_F gs g S)"
proof (rule monoI)
  fix T T' :: "ltr set"
  assume "T \<subseteq> T'"
  then show "ltr_F gs g S T \<subseteq> ltr_F gs g S T'"
    unfolding ltr_F_def by blast
qed

lemma ltr_F_lfp_fold:
  "x \<in> ltr_F gs g S (lfp (ltr_F gs g S)) \<Longrightarrow> x \<in> lfp (ltr_F gs g S)"
  by (subst lfp_unfold[OF ltr_F_mono]) assumption

subsection \<open>Fixed-point characterization\<close>

text \<open>\<open>ltr_F\<close> maps \<^const>\<open>valid_ltr\<close> into itself: each summand is discharged by the
  corresponding \<^const>\<open>valid_ltr\<close> introduction rule.\<close>
lemma ltr_F_valid_ltr_closed:
  "ltr_F gs g S (valid_ltr gs g S) \<subseteq> valid_ltr gs g S"
  unfolding ltr_F_def
  by (blast intro: valid_ltr.intros)

lemma lfp_ltr_F_subset_valid_ltr:
  "lfp (ltr_F gs g S) \<subseteq> valid_ltr gs g S"
  by (rule lfp_lowerbound) (rule ltr_F_valid_ltr_closed)

text \<open>The converse follows by \<^const>\<open>valid_ltr\<close> rule induction: every constructor step lands
  in \<open>ltr_F gs g S (lfp (ltr_F gs g S))\<close> via the induction hypotheses, then folds back into the
  least fixed point.\<close>
lemma valid_ltr_subset_lfp:
  "valid_ltr gs g S \<subseteq> lfp (ltr_F gs g S)"
proof (rule subsetI)
  fix t assume "t \<in> valid_ltr gs g S"
  then show "t \<in> lfp (ltr_F gs g S)"
  proof (induction rule: valid_ltr.induct)
    case (init s)
    have "Root [(cfg_entry g, s)] \<in> ltr_F gs g S (lfp (ltr_F gs g S))"
      unfolding ltr_F_def[of gs g S "lfp (ltr_F gs g S)"] using init by blast
    then show ?case by (rule ltr_F_lfp_fold)
  next
    case (intra t a v s')
    have "extend t (v, s') \<in> ltr_F gs g S (lfp (ltr_F gs g S))"
      unfolding ltr_F_def[of gs g S "lfp (ltr_F gs g S)"] using intra.hyps intra.IH by blast
    then show ?case by (rule ltr_F_lfp_fold)
  next
    case (call caller dst pars args p cont)
    have "Call caller [(FunctionEntry p, call_enter gs (CallEdge dst pars args)
                        (sink_store caller))] \<in> ltr_F gs g S (lfp (ltr_F gs g S))"
      unfolding ltr_F_def[of gs g S "lfp (ltr_F gs g S)"] using call.hyps call.IH by blast
    then show ?case by (rule ltr_F_lfp_fold)
  next
    case (ret callee caller p dst pars args cont)
    have "Resume caller callee
            (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))])
            \<in> ltr_F gs g S (lfp (ltr_F gs g S))"
      unfolding ltr_F_def[of gs g S "lfp (ltr_F gs g S)"] using ret.hyps ret.IH by blast
    then show ?case by (rule ltr_F_lfp_fold)
  qed
qed

theorem valid_ltr_eq_lfp:
  "valid_ltr gs g S = lfp (ltr_F gs g S)"
  by (rule antisym[OF valid_ltr_subset_lfp lfp_ltr_F_subset_valid_ltr])

subsection \<open>Seed structure: monotonicity and union in the initial set\<close>

text \<open>Enlarging the initial store set only adds traces.  \<open>ltr_F\<close>'s dependence on \<open>S\<close> is
  confined to the root clause --- \<open>extend\<close>/\<open>Call\<close>/\<open>Resume\<close> read only their argument set, never
  \<open>S\<close> --- so \<open>ltr_F gs g S\<close> is pointwise below \<open>ltr_F gs g S'\<close> and \<open>lfp_mono\<close> applies directly,
  with no case split over \<^const>\<open>valid_ltr\<close>'s four constructors.\<close>
lemma valid_ltr_mono_S:
  assumes "S \<subseteq> S'"
  shows "valid_ltr gs g S \<subseteq> valid_ltr gs g S'"
proof -
  have "ltr_F gs g S T \<subseteq> ltr_F gs g S' T" for T
    unfolding ltr_F_def using assms by blast
  then have "lfp (ltr_F gs g S) \<subseteq> lfp (ltr_F gs g S')"
    by (rule lfp_mono)
  then show ?thesis by (simp add: valid_ltr_eq_lfp)
qed

text \<open>Every trace is seeded by a single initial store: the valid set is the union of the
  single-seed valid sets.  A return recovers its caller from the completed callee's own
  ancestry, so caller and callee share the seed --- the \<open>ret\<close> case needs only the callee.\<close>
lemma valid_ltr_eq_UN_singleton:
  "valid_ltr gs g S = (\<Union>s\<in>S. valid_ltr gs g {s})"
proof (rule equalityI)
  show "valid_ltr gs g S \<subseteq> (\<Union>s\<in>S. valid_ltr gs g {s})"
  proof (rule subsetI)
    fix t assume "t \<in> valid_ltr gs g S"
    then show "t \<in> (\<Union>s\<in>S. valid_ltr gs g {s})"
    proof (induction rule: valid_ltr.induct)
      case (init s) then show ?case using valid_ltr.init[of s "{s}" g gs] by auto
    next
      case (intra t a v s')
      then obtain s where "s \<in> S" "t \<in> valid_ltr gs g {s}" by auto
      then show ?case using valid_ltr.intra[OF _ intra.hyps(2,3)] by auto
    next
      case (call caller dst pars args p cont)
      then obtain s where "s \<in> S" "caller \<in> valid_ltr gs g {s}" by auto
      then show ?case using valid_ltr.call[OF _ call.hyps(2)] by auto
    next
      case (ret callee caller p dst pars args cont)
      then obtain s where "s \<in> S" "callee \<in> valid_ltr gs g {s}" by auto
      then show ?case using valid_ltr.ret[OF _ ret.hyps(2,3,4)] by auto
    qed
  qed
next
  show "(\<Union>s\<in>S. valid_ltr gs g {s}) \<subseteq> valid_ltr gs g S"
    using valid_ltr_mono_S by blast
qed

text \<open>Collection distributes over a union of initial sets.\<close>
lemma valid_ltr_Un_S:
  "valid_ltr gs g (S \<union> S') = valid_ltr gs g S \<union> valid_ltr gs g S'"
  using valid_ltr_eq_UN_singleton[of gs g "S \<union> S'"]
        valid_ltr_eq_UN_singleton[of gs g S] valid_ltr_eq_UN_singleton[of gs g S']
  by auto

subsection \<open>Forgetful projections\<close>

text \<open>\<open>ltr_collect\<close> is the concrete collecting view: the sink stores of valid traces
  reaching node \<open>v\<close>.  \<^const>\<open>activation_collect\<close> (\<open>LTR_Def\<close>) is the context-indexed
  collector, filtering those by the structural activation key; the key type is not
  required finite, so a keyed bucket is not claimed to be an exact activation identity.\<close>

definition ltr_collect :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> store set" where
  "ltr_collect gs g S v =
     {sink_store t | t. t \<in> valid_ltr gs g S \<and> sink_node t = v}"

lemma ltr_collect_I [intro]:
  "t \<in> valid_ltr gs g S \<Longrightarrow> sink_store t \<in> ltr_collect gs g S (sink_node t)"
  unfolding ltr_collect_def by blast

text \<open>Every collected state has a valid trace witness.\<close>
lemma ltr_collect_E [elim]:
  assumes "s \<in> ltr_collect gs g S v"
  obtains t where "t \<in> valid_ltr gs g S" "sink_node t = v" "sink_store t = s"
  using assms unfolding ltr_collect_def by blast

text \<open>
  \<^const>\<open>ltr_collect\<close> is closed under intra flow: extending a witness trace by one
  \<^const>\<open>intra\<close> edge is \<open>valid_ltr.intra\<close>.  Closure under \<^emph>\<open>call\<close> and \<^emph>\<open>return\<close>
  steps is deliberately absent here --- \<open>valid_ltr.ret\<close> requires the popped activation to be the
  witness trace's own caller, which a bare CFG step does not supply.
\<close>

lemma ltr_collect_intra_step:
  assumes s: "s \<in> ltr_collect gs g S u"
    and e: "(u, a, v) \<in> intra g"
    and st: "s' \<in> edge_step a s"
  shows "s' \<in> ltr_collect gs g S v"
proof -
  from s obtain t where t: "t \<in> valid_ltr gs g S" and n: "sink_node t = u" and w: "sink_store t = s"
    by (rule ltr_collect_E)
  have "extend t (v, s') \<in> valid_ltr gs g S"
    by (rule valid_ltr.intra[OF t]) (use e st n w in simp_all)
  from ltr_collect_I[OF this] show ?thesis by simp
qed

text \<open>
  The activation-preserving form.  Following an \<^const>\<open>intra_path\<close> only \<open>extend\<close>s the trace, so
  the resulting witness is the \<^emph>\<open>same\<close> activation: same caller and same entry node.  Callers
  that must know \<^emph>\<open>which\<close> activation reached a node need this: the collection at a node
  merges every activation that reaches it.
\<close>

lemma valid_ltr_intra_path_extend_pair:
  "intra_path g x y \<Longrightarrow> t \<in> valid_ltr gs g S \<Longrightarrow> sink_node t = fst x \<Longrightarrow> sink_store t = snd x
   \<Longrightarrow> \<exists>t'. t' \<in> valid_ltr gs g S \<and> sink_node t' = fst y \<and> sink_store t' = snd y
            \<and> caller_of t' = caller_of t \<and> fst (hd (path t')) = fst (hd (path t))"
proof (induction arbitrary: t rule: star.induct)
  case (refl x)
  then show ?case by blast
next
  case (step x y z)
  obtain u s where x: "x = (u, s)" by (cases x)
  obtain w s1 where y: "y = (w, s1)" by (cases y)
  from step.hyps(1) x y obtain a where
    e: "(u, a, w) \<in> intra g" and st: "s1 \<in> edge_step a s"
    by auto
  have ext: "extend t (w, s1) \<in> valid_ltr gs g S"
    by (rule valid_ltr.intra[OF step.prems(1)])
       (use e st step.prems(2,3) x in simp_all)
  have hd_ext: "fst (hd (path (extend t (w, s1)))) = fst (hd (path t))"
    using valid_ltr_path_nonempty[OF step.prems(1)] by simp
  from step.IH[OF ext] y obtain t' where
    "t' \<in> valid_ltr gs g S" "sink_node t' = fst z" "sink_store t' = snd z"
    "caller_of t' = caller_of (extend t (w, s1))"
    "fst (hd (path t')) = fst (hd (path (extend t (w, s1))))" by auto
  then show ?case using hd_ext by auto
qed

lemma valid_ltr_intra_path_extend:
  assumes p: "intra_path g (sink_node t, sink_store t) (v, s')"
    and t: "t \<in> valid_ltr gs g S"
  obtains t' where "t' \<in> valid_ltr gs g S" "sink_node t' = v" "sink_store t' = s'"
    "caller_of t' = caller_of t" "fst (hd (path t')) = fst (hd (path t))"
  using valid_ltr_intra_path_extend_pair[OF p t] by auto

subsection \<open>Collecting equations\<close>

text \<open>(1) Initial stores are collected at \<^const>\<open>cfg_entry\<close>.\<close>
lemma ltr_collect_init:
  "s \<in> S \<Longrightarrow> s \<in> ltr_collect gs g S (cfg_entry g)"
  using ltr_collect_I[OF valid_ltr.init] by simp

subsection \<open>Context-sensitive / context-insensitive bridge\<close>

text \<open>Bridge (1): context-sensitive collection is included in context-insensitive
  collection.\<close>
theorem activation_collect_le_ltr_collect:
  "activation_collect gs enterc initial_ctx g S v c \<subseteq> ltr_collect gs g S v"
  unfolding activation_collect_def ltr_collect_def by blast

text \<open>Bridge (2): context-insensitive collection is the union over contexts --- every trace
  has exactly one context, since \<^const>\<open>key\<close> is a total function.  No finiteness assumption.\<close>
theorem ltr_collect_eq_Union_activation:
  "ltr_collect gs g S v = (\<Union>c. activation_collect gs enterc initial_ctx g S v c)"
proof
  show "ltr_collect gs g S v \<subseteq> (\<Union>c. activation_collect gs enterc initial_ctx g S v c)"
  proof
    fix x assume "x \<in> ltr_collect gs g S v"
    then obtain t where t: "t \<in> valid_ltr gs g S" "sink_node t = v" "sink_store t = x"
      by (rule ltr_collect_E)
    then show "x \<in> (\<Union>c. activation_collect gs enterc initial_ctx g S v c)"
      unfolding activation_collect_def by blast
  qed
next
  show "(\<Union>c. activation_collect gs enterc initial_ctx g S v c) \<subseteq> ltr_collect gs g S v"
    unfolding activation_collect_def ltr_collect_def by blast
qed


section \<open>The collecting semantics is inhabited\<close>

text \<open>
  \<^const>\<open>valid_ltr\<close> and \<^const>\<open>ltr_collect\<close> are defined over an arbitrary graph, and every
  soundness statement downstream is an over-approximation claim about them; if they were
  empty, all of it would hold vacuously.  A two-node graph with one assignment edge settles
  that inside this session, without borrowing a graph from the compiler: the entry store is
  collected at the entry, and the assigned store is collected one edge later.
\<close>

definition ltr_witness_cfg :: cfg where
  "ltr_witness_cfg =
     \<lparr> intra = {(Statement 0, EA_Assign (STR ''x'') (N 1), Statement 1)},
       calls = {},
       cfg_entry = Statement 0,
       checks = {} \<rparr>"

lemma ltr_witness_entry [simp]: "cfg_entry ltr_witness_cfg = Statement 0"
  by (simp add: ltr_witness_cfg_def)

lemma ltr_witness_edge [simp]:
  "(Statement 0, EA_Assign (STR ''x'') (N 1), Statement 1) \<in> intra ltr_witness_cfg"
  by (simp add: ltr_witness_cfg_def)

lemma ltr_witness_root:
  "Root [(Statement 0, s)] \<in> valid_ltr gs ltr_witness_cfg {s}"
proof -
  have "Root [(cfg_entry ltr_witness_cfg, s)] \<in> valid_ltr gs ltr_witness_cfg {s}"
    by (rule valid_ltr.init) simp
  then show ?thesis by simp
qed

theorem ltr_collect_witness:
  "s \<in> ltr_collect gs ltr_witness_cfg {s} (Statement 0)"
  "s(STR ''x'' := 1) \<in> ltr_collect gs ltr_witness_cfg {s} (Statement 1)"
proof -
  have root: "Root [(Statement 0, s)] \<in> valid_ltr gs ltr_witness_cfg {s}"
    by (rule ltr_witness_root)
  show "s \<in> ltr_collect gs ltr_witness_cfg {s} (Statement 0)"
    using ltr_collect_I[OF root] by (simp add: sink_node_def sink_store_def)
  have "extend (Root [(Statement 0, s)]) (Statement 1, s(STR ''x'' := 1))
          \<in> valid_ltr gs ltr_witness_cfg {s}"
    by (rule valid_ltr.intra[OF root, where a = "EA_Assign (STR ''x'') (N 1)"
                                        and v = "Statement 1"])
       (simp_all add: ltr_witness_cfg_def sink_node_def sink_store_def)
  from ltr_collect_I[OF this]
  show "s(STR ''x'' := 1) \<in> ltr_collect gs ltr_witness_cfg {s} (Statement 1)"
    by (simp add: sink_node_def sink_store_def)
qed

end
