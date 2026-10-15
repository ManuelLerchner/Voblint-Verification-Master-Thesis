theory Activation_Trace_Collect
  imports Activation_Trace_Context
begin

section \<open>Which stores can occur at each node\<close>

text \<open>
  \<open>\<C>\<^bsub>\<G>,g,S\<^esub> v\<close> is the set of stores a run can actually have at node \<open>v\<close>: take
  every valid activation trace that ends there and keep its final store.  This is the concrete set an
  analysis has to over-approximate, so it is the target of every soundness statement
  downstream.

  \<^const>\<open>trace_sem.gvalid_activation_trace\<close> has four clauses --- root, intra
  step, call, return --- each reading exactly the relation for its phenomenon: \<open>intra\<close> for
  local extension, \<open>calls\<close> for entering a callee and for recovering a continuation.  The
  return clause recovers the caller from the completed callee's own ancestry through
  \<^const>\<open>caller_of\<close>, never by an independent choice.

  There is no global exit node: whole-program completion is collection at
  \<open>FunctionResult main\<close>, and a procedure result is an ordinary collected node rather than a
  separate summary mechanism.
\<close>

subsection \<open>Forgetful projections\<close>

text \<open>\<open>gnode_collect\<close> is the concrete collecting view: the sink stores of valid activation traces
  reaching node \<open>v\<close>.  \<^const>\<open>ctx_sem.gactivation_collect\<close> is the context-indexed collector, keeping
  those whose trace may carry the queried context; the context type is not required
  finite, and a bucket is not claimed to be an exact activation identity.\<close>

locale collect_sem = ctx_sem ev rv conv glob
  for ev :: "'e \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> int" and rv :: 'v
    and conv :: "'v option \<Rightarrow> int \<Rightarrow> int" and glob :: "'v \<Rightarrow> bool"
begin

definition gnode_collect ::
    "('v, 'e) gcfg \<Rightarrow> ('v \<Rightarrow> int) set \<Rightarrow> cfg_node \<Rightarrow> ('v \<Rightarrow> int) set" where
  "gnode_collect g S v =
     {sink_store t | t. t \<in> gvalid_activation_trace g S \<and> sink_node t = v}"

text \<open>Up to the inhabitation witness, every lemma concerns one graph and one set of
  initial stores, so the block fixes \<open>\<G>\<close>, \<open>g\<close> and \<open>S\<close> and writes
  \<open>(gvalid_activation_trace g S)\<close> and \<open>(gnode_collect g S) v\<close> for \<open>gvalid_activation_trace g S\<close> and
  \<open>\<C>\<^bsub>\<G>,g,S\<^esub> v\<close>.\<close>

context
  fixes g :: "('v, 'e) gcfg" and S :: "('v \<Rightarrow> int) set"
begin

lemma node_collect_I [intro]:
  "t \<in> (gvalid_activation_trace g S) \<Longrightarrow> sink_store t \<in> (gnode_collect g S) (sink_node t)"
  unfolding gnode_collect_def by blast

text \<open>Every collected state has a valid activation trace witness.\<close>
lemma node_collect_E [elim]:
  assumes "s \<in> (gnode_collect g S) v"
  obtains t where "t \<in> (gvalid_activation_trace g S)" "sink_node t = v" "sink_store t = s"
  using assms unfolding gnode_collect_def by blast

text \<open>
  \<open>gnode_collect\<close> is closed under intra flow: extending a witness trace by one
  \<^const>\<open>intra\<close> edge is \<open>gvalid_activation_trace.intra\<close>.  Closure under \<^emph>\<open>call\<close> and \<^emph>\<open>return\<close>
  steps is deliberately absent here --- \<open>gvalid_activation_trace.ret\<close> requires the popped activation to be the
  witness trace's own caller, which a bare CFG step does not supply.
\<close>

lemma node_collect_intra_step:
  assumes s: "s \<in> (gnode_collect g S) u"
    and e: "(u, a, v) \<in> intra g"
    and st: "s' \<in> gedge_step a s"
  shows "s' \<in> (gnode_collect g S) v"
proof -
  from s
  obtain t where t: "t \<in> (gvalid_activation_trace g S)" and n: "sink_node t = u" and w:
    "sink_store t = s"
    by (rule node_collect_E)
  have "extend t (v, s') \<in> (gvalid_activation_trace g S)"
    by (rule gvalid_activation_trace.intra[OF t]) (use e st n w in simp_all)
  from node_collect_I[OF this] show ?thesis by simp
qed

text \<open>
  The activation-preserving form.  Following an intra path only \<open>extend\<close>s the trace, so
  the resulting witness is the \<^emph>\<open>same\<close> activation: same caller and same entry node.  Callers
  that must know \<^emph>\<open>which\<close> activation reached a node need this: the collection at a node
  merges every activation that reaches it.
\<close>

lemma valid_activation_trace_intra_path_extend_pair:
  "star (gcfg_intra_step g) x y \<Longrightarrow> t \<in> (gvalid_activation_trace g S) \<Longrightarrow> sink_node t = fst x \<Longrightarrow> sink_store t = snd x
   \<Longrightarrow> \<exists>t'. t' \<in> (gvalid_activation_trace g S) \<and> sink_node t' = fst y \<and> sink_store t' = snd y
            \<and> caller_of t' = caller_of t \<and> fst (hd (path_of t')) = fst (hd (path_of t))"
proof (induction arbitrary: t rule: star.induct)
  case (refl x)
  then show ?case by blast
next
  case (step x y z)
  obtain u s where x: "x = (u, s)" by (cases x)
  obtain w s1 where y: "y = (w, s1)" by (cases y)
  from step.hyps(1) x y obtain a where
    e: "(u, a, w) \<in> intra g" and st: "s1 \<in> gedge_step a s"
    by auto
  have ext: "extend t (w, s1) \<in> (gvalid_activation_trace g S)"
    by (rule gvalid_activation_trace.intra[OF step.prems(1)])
       (use e st step.prems(2,3) x in simp_all)
  have hd_ext: "fst (hd (path_of (extend t (w, s1)))) = fst (hd (path_of t))"
    using valid_activation_trace_path_nonempty[OF step.prems(1)] by simp
  from step.IH[OF ext] y obtain t' where
    "t' \<in> (gvalid_activation_trace g S)" "sink_node t' = fst z" "sink_store t' = snd z"
    "caller_of t' = caller_of (extend t (w, s1))"
    "fst (hd (path_of t')) = fst (hd (path_of (extend t (w, s1))))" by auto
  then show ?case using hd_ext by auto
qed

lemma valid_activation_trace_intra_path_extend:
  assumes p: "star (gcfg_intra_step g) (sink_node t, sink_store t) (v, s')"
    and t: "t \<in> (gvalid_activation_trace g S)"
  obtains t' where "t' \<in> (gvalid_activation_trace g S)" "sink_node t' = v" "sink_store t' = s'"
    "caller_of t' = caller_of t" "fst (hd (path_of t')) = fst (hd (path_of t))"
  using valid_activation_trace_intra_path_extend_pair[OF p t] by auto

text \<open>
  A call and its matching return \<^emph>\<open>do\<close> compose, which is what makes the missing
  single-step closure above harmless in practice.  The callee trace is built from
  the caller's by \<open>gvalid_activation_trace.call\<close>, so \<open>gvalid_activation_trace.ret\<close>'s side condition --- that the
  activation being popped is this trace's own caller --- holds by construction,
  and running the callee to its \<^const>\<open>FunctionResult\<close> along an intra path
  preserves it.  What a caller supplies is the call edge and an intra path through
  the callee; what it gets back is the continuation node with the combined ('v \<Rightarrow> int).
\<close>

lemma node_collect_call_return_step:
  assumes s: "s \<in> (gnode_collect g S) u"
      and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls g"
      and body: "star (gcfg_intra_step g) (FunctionEntry q, gcall_enter (CallEdge dst pars args) s)
                   (FunctionResult q, t)"
  shows "gcombine_collect dst s t \<in> (gnode_collect g S) cont"
proof -
  from s obtain caller where cv: "caller \<in> (gvalid_activation_trace g S)"
    and cn: "sink_node caller = u" and cs: "sink_store caller = s"
    by (rule node_collect_E)
  let ?entered = "Call caller [(FunctionEntry q, gcall_enter (CallEdge dst pars args) s)]"
  have ev: "?entered \<in> (gvalid_activation_trace g S)"
    using gvalid_activation_trace.call [OF cv, where dst = dst and pars = pars and args = args
                            and p = q and cont = cont]
      ce cn cs by simp
  obtain callee where dv: "callee \<in> (gvalid_activation_trace g S)"
    and dn: "sink_node callee = FunctionResult q" and ds: "sink_store callee = t"
    and dc: "caller_of callee = caller_of ?entered"
    by (rule valid_activation_trace_intra_path_extend [OF _ ev]) (use body in simp_all)
  have "Resume caller callee
          (path_of caller @ [(cont, gcombine_collect dst (sink_store caller) (sink_store callee))])
          \<in> (gvalid_activation_trace g S)"
    by (rule gvalid_activation_trace.ret [OF dv _ dn]) (use dc ce cn in simp_all)
  from node_collect_I [OF this] show ?thesis
    using cs ds by (simp add: sink_node_def sink_store_def)
qed

subsection \<open>Collecting equations\<close>

text \<open>(1) Initial stores are collected at \<^const>\<open>cfg_entry\<close>.\<close>
lemma node_collect_init:
  "s \<in> S \<Longrightarrow> s \<in> (gnode_collect g S) (cfg_entry g)"
  using node_collect_I[OF gvalid_activation_trace.root] by simp

subsection \<open>Context-sensitive / context-insensitive bridge\<close>

text \<open>Bridge (1): every context bucket, and so their union, is included in the
  context-insensitive collection.\<close>
theorem activation_collect_le_node_collect:
  "gactivation_collect adm c\<^sub>0 g S v c \<subseteq> (gnode_collect g S) v"
  unfolding gactivation_collect_def gnode_collect_def by blast

theorem Union_activation_collect_le_node_collect:
  "(\<Union>c. gactivation_collect adm c\<^sub>0 g S v c) \<subseteq> (gnode_collect g S) v"
  using activation_collect_le_node_collect by blast

text \<open>Bridge (2): the converse needs every valid activation trace to carry some context.  That premise is
  the whole content of the direction -- a policy that leaves some trace uncontexted loses the
  stores on it, and the union then falls short.  A functional policy has it outright, since
  \<^const>\<open>activation_context_of\<close> is total; a relational one earns it from conditional totality, which is
  \<open>Activation_Trace_Abstract\<close>'s business.  No finiteness assumption either way.\<close>
theorem node_collect_eq_Union_activation_of_has_context:
  assumes has_ctx:
    "\<And>t. t \<in> (gvalid_activation_trace g S) \<Longrightarrow> \<exists>c. gactivation_context_rel adm c\<^sub>0 g t c"
  shows "(gnode_collect g S) v = (\<Union>c. gactivation_collect adm c\<^sub>0 g S v c)"
proof
  show "(gnode_collect g S) v \<subseteq> (\<Union>c. gactivation_collect adm c\<^sub>0 g S v c)"
  proof
    fix x assume "x \<in> (gnode_collect g S) v"
    then obtain t where t: "t \<in> (gvalid_activation_trace g S)" "sink_node t = v" "sink_store t = x"
      by (rule node_collect_E)
    from has_ctx [OF t(1)] obtain c where "gactivation_context_rel adm c\<^sub>0 g t c" ..
    with t show "x \<in> (\<Union>c. gactivation_collect adm c\<^sub>0 g S v c)"
      by blast
  qed
next
  show "(\<Union>c. gactivation_collect adm c\<^sub>0 g S v c) \<subseteq> (gnode_collect g S) v"
    by (rule Union_activation_collect_le_node_collect)
qed

theorem node_collect_eq_Union_activation_of_fun:
  "(gnode_collect g S) v
     = (\<Union>c. gactivation_collect (context_policy_of_fun f) c\<^sub>0 g S v c)"
  by (rule node_collect_eq_Union_activation_of_has_context)
     (simp add: activation_context_rel_of_fun_iff)

end

end

section \<open>The typed instance\<close>

text \<open>The stores valid activation traces of the typed graph reach at a node.\<close>

definition node_collect :: "kenv \<Rightarrow> (var_id, exp) gcfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> store set"
    ("\<C>\<^bsub>_,_,_\<^esub>") where
  "node_collect \<kappa> = collect_sem.gnode_collect eval ReturnVar (kind_conv \<kappa>) is_global"

global_interpretation vimp: collect_sem eval ReturnVar "kind_conv \<kappa>" is_global
  rewrites "collect_sem.gnode_collect eval ReturnVar (kind_conv \<kappa>) is_global = node_collect \<kappa>"
    and "trace_sem.gvalid_activation_trace eval ReturnVar (kind_conv \<kappa>) is_global
           = valid_activation_trace \<kappa>"
    and "ctx_sem.gactivation_collect eval ReturnVar (kind_conv \<kappa>) is_global = activation_collect \<kappa>"
  for \<kappa> :: kenv
  by (simp_all add: node_collect_def valid_activation_trace_def activation_collect_def)

section \<open>The collecting semantics is inhabited\<close>

text \<open>
  \<^const>\<open>trace_sem.gvalid_activation_trace\<close> and \<^const>\<open>collect_sem.gnode_collect\<close> are defined over an arbitrary graph, and every
  soundness statement downstream is an over-approximation claim about them; if they were
  empty, all of it would hold vacuously.  A two-node graph with one assignment edge settles
  that inside this session, without borrowing a graph from the compiler: the initial store is
  collected at the entry, and the assigned store is collected one edge later.
\<close>

abbreviation activation_trace_witness_var :: var_id where
  "activation_trace_witness_var \<equiv> GlobalId (STR ''x'')"

definition activation_trace_witness_cfg :: "(var_id, exp) gcfg" where
  "activation_trace_witness_cfg =
     \<lparr> intra = {(Statement 0, EA_Assign activation_trace_witness_var (TN I32 1), Statement 1)},
       calls = {},
       cfg_entry = Statement 0 \<rparr>"

lemma activation_trace_witness_entry [simp]: "cfg_entry activation_trace_witness_cfg = Statement 0"
  by (simp add: activation_trace_witness_cfg_def)

lemma activation_trace_witness_edge [simp]:
  "(Statement 0, EA_Assign activation_trace_witness_var (TN I32 1), Statement 1)
     \<in> intra activation_trace_witness_cfg"
  by (simp add: activation_trace_witness_cfg_def)

text \<open>The witness runs at the typed instance, for every kind environment.\<close>

lemma activation_trace_witness_root:
  "Root [(Statement 0, s)] \<in> \<T>\<^bsub>\<kappa>,activation_trace_witness_cfg,{s}\<^esub>"
proof -
  have "Root [(cfg_entry activation_trace_witness_cfg, s)]
          \<in> \<T>\<^bsub>\<kappa>,activation_trace_witness_cfg,{s}\<^esub>"
    by (rule vimp.gvalid_activation_trace.root) simp
  then show ?thesis by simp
qed

theorem node_collect_witness:
  "s \<in> \<C>\<^bsub>\<kappa>,activation_trace_witness_cfg,{s}\<^esub> (Statement 0)"
  "s(activation_trace_witness_var := kind_conv \<kappa> (Some activation_trace_witness_var) (ik_norm I32 1))
     \<in> \<C>\<^bsub>\<kappa>,activation_trace_witness_cfg,{s}\<^esub> (Statement 1)"
proof -
  have root: "Root [(Statement 0, s)] \<in> \<T>\<^bsub>\<kappa>,activation_trace_witness_cfg,{s}\<^esub>"
    by (rule activation_trace_witness_root)
  show "s \<in> \<C>\<^bsub>\<kappa>,activation_trace_witness_cfg,{s}\<^esub> (Statement 0)"
    using vimp.node_collect_I[OF root] by (simp add: sink_node_def sink_store_def)
  have "extend (Root [(Statement 0, s)])
          (Statement 1, s(activation_trace_witness_var
             := kind_conv \<kappa> (Some activation_trace_witness_var) (ik_norm I32 1)))
          \<in> \<T>\<^bsub>\<kappa>,activation_trace_witness_cfg,{s}\<^esub>"
    by (rule vimp.gvalid_activation_trace.intra[OF root,
          where a = "EA_Assign activation_trace_witness_var (TN I32 1)" and v = "Statement 1"])
       (simp_all add: activation_trace_witness_cfg_def sink_node_def sink_store_def)
  from vimp.node_collect_I[OF this]
  show "s(activation_trace_witness_var := kind_conv \<kappa> (Some activation_trace_witness_var) (ik_norm I32 1))
          \<in> \<C>\<^bsub>\<kappa>,activation_trace_witness_cfg,{s}\<^esub> (Statement 1)"
    by (simp add: sink_node_def sink_store_def)
qed

end
