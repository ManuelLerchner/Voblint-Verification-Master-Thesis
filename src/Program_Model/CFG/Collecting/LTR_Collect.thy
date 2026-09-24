theory LTR_Collect
  imports LTR_Def LTR_Activation_Context
begin

section \<open>Which stores can occur at each node\<close>

text \<open>
  \<open>\<C>\<^bsub>\<G>,g,S\<^esub> v\<close> is the set of stores a run can actually have at node \<open>v\<close>: take
  every valid trace that ends there and keep its final store.  This is the concrete set an
  analysis has to over-approximate, so it is the target of every soundness statement
  downstream.

  \<^const>\<open>valid_ltr\<close> has four clauses --- root, intra
  step, call, return --- each reading exactly the relation for its phenomenon: \<open>intra\<close> for
  local extension, \<open>calls\<close> for entering a callee and for recovering a continuation.  The
  return clause recovers the caller from the completed callee's own ancestry through
  \<^const>\<open>caller_of\<close>, never by an independent choice.

  There is no global exit node: whole-program completion is collection at
  \<open>FunctionResult main\<close>, and a procedure result is an ordinary collected node rather than a
  separate summary mechanism.
\<close>

subsection \<open>Forgetful projections\<close>

text \<open>\<open>ltr_collect\<close> is the concrete collecting view: the sink stores of valid traces
  reaching node \<open>v\<close>.  \<^const>\<open>activation_collect\<close> is the context-indexed collector, keeping
  those whose trace may carry the queried context; the context type is not required
  finite, and a bucket is not claimed to be an exact activation identity.\<close>

definition ltr_collect ::
    "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> store set \<Rightarrow> cfg_node \<Rightarrow> store set"
    ("\<C>\<^bsub>_,_,_\<^esub>") where
  "\<C>\<^bsub>\<G>,g,S\<^esub> v =
     {sink_store t | t. t \<in> \<T>\<^bsub>\<G>,g,S\<^esub> \<and> sink_node t = v}"

text \<open>Up to the inhabitation witness, every lemma concerns one graph and one set of
  initial stores, so the block fixes \<open>\<G>\<close>, \<open>g\<close> and \<open>S\<close> and writes
  \<open>\<T>\<close> and \<open>\<C> v\<close> for \<open>\<T>\<^bsub>\<G>,g,S\<^esub>\<close> and
  \<open>\<C>\<^bsub>\<G>,g,S\<^esub> v\<close>.\<close>

context
  fixes \<G> :: "vname \<Rightarrow> bool" and g :: cfg and S :: "store set"
begin

private abbreviation (input) traces :: "ltr set" where "traces \<equiv> \<T>\<^bsub>\<G>,g,S\<^esub>"
private abbreviation (input) collect :: "cfg_node \<Rightarrow> store set"
  where "collect \<equiv> \<C>\<^bsub>\<G>,g,S\<^esub>"
notation traces ("\<T>") and collect ("\<C>")

lemma ltr_collect_I [intro]:
  "t \<in> \<T> \<Longrightarrow> sink_store t \<in> \<C> (sink_node t)"
  unfolding ltr_collect_def by blast

text \<open>Every collected state has a valid trace witness.\<close>
lemma ltr_collect_E [elim]:
  assumes "s \<in> \<C> v"
  obtains t where "t \<in> \<T>" "sink_node t = v" "sink_store t = s"
  using assms unfolding ltr_collect_def by blast

text \<open>
  \<^const>\<open>ltr_collect\<close> is closed under intra flow: extending a witness trace by one
  \<^const>\<open>intra\<close> edge is \<open>valid_ltr.intra\<close>.  Closure under \<^emph>\<open>call\<close> and \<^emph>\<open>return\<close>
  steps is deliberately absent here --- \<open>valid_ltr.ret\<close> requires the popped activation to be the
  witness trace's own caller, which a bare CFG step does not supply.
\<close>

lemma ltr_collect_intra_step:
  assumes s: "s \<in> \<C> u"
    and e: "(u, a, v) \<in> intra g"
    and st: "s' \<in> edge_step a s"
  shows "s' \<in> \<C> v"
proof -
  from s obtain t where t: "t \<in> \<T>" and n: "sink_node t = u" and w: "sink_store t = s"
    by (rule ltr_collect_E)
  have "extend t (v, s') \<in> \<T>"
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
  "intra_path g x y \<Longrightarrow> t \<in> \<T> \<Longrightarrow> sink_node t = fst x \<Longrightarrow> sink_store t = snd x
   \<Longrightarrow> \<exists>t'. t' \<in> \<T> \<and> sink_node t' = fst y \<and> sink_store t' = snd y
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
  have ext: "extend t (w, s1) \<in> \<T>"
    by (rule valid_ltr.intra[OF step.prems(1)])
       (use e st step.prems(2,3) x in simp_all)
  have hd_ext: "fst (hd (path (extend t (w, s1)))) = fst (hd (path t))"
    using valid_ltr_path_nonempty[OF step.prems(1)] by simp
  from step.IH[OF ext] y obtain t' where
    "t' \<in> \<T>" "sink_node t' = fst z" "sink_store t' = snd z"
    "caller_of t' = caller_of (extend t (w, s1))"
    "fst (hd (path t')) = fst (hd (path (extend t (w, s1))))" by auto
  then show ?case using hd_ext by auto
qed

lemma valid_ltr_intra_path_extend:
  assumes p: "intra_path g (sink_node t, sink_store t) (v, s')"
    and t: "t \<in> \<T>"
  obtains t' where "t' \<in> \<T>" "sink_node t' = v" "sink_store t' = s'"
    "caller_of t' = caller_of t" "fst (hd (path t')) = fst (hd (path t))"
  using valid_ltr_intra_path_extend_pair[OF p t] by auto

text \<open>
  A call and its matching return \<^emph>\<open>do\<close> compose, which is what makes the missing
  single-step closure above harmless in practice.  The callee trace is built from
  the caller's by \<open>valid_ltr.call\<close>, so \<open>valid_ltr.ret\<close>'s side condition --- that the
  activation being popped is this trace's own caller --- holds by construction,
  and running the callee to its \<^const>\<open>FunctionResult\<close> along \<^const>\<open>intra_path\<close>
  preserves it.  What a caller supplies is the call edge and an intra path through
  the callee; what it gets back is the continuation node with the combined store.
\<close>

lemma ltr_collect_call_return_step:
  assumes s: "s \<in> \<C> u"
      and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls g"
      and body: "intra_path g (FunctionEntry q, call_enter \<G> (CallEdge dst pars args) s)
                   (FunctionResult q, t)"
  shows "combine_collect \<G> dst s t \<in> \<C> cont"
proof -
  from s obtain caller where cv: "caller \<in> \<T>"
    and cn: "sink_node caller = u" and cs: "sink_store caller = s"
    by (rule ltr_collect_E)
  let ?entered = "Call caller [(FunctionEntry q, call_enter \<G> (CallEdge dst pars args) s)]"
  have ev: "?entered \<in> \<T>"
    using valid_ltr.call [OF cv, where dst = dst and pars = pars and args = args
                            and p = q and cont = cont]
      ce cn cs by simp
  obtain callee where dv: "callee \<in> \<T>"
    and dn: "sink_node callee = FunctionResult q" and ds: "sink_store callee = t"
    and dc: "caller_of callee = caller_of ?entered"
    by (rule valid_ltr_intra_path_extend [OF _ ev]) (use body in simp_all)
  have "Resume caller callee
          (path caller @ [(cont, combine_collect \<G> dst (sink_store caller) (sink_store callee))])
          \<in> \<T>"
    by (rule valid_ltr.ret [OF dv _ dn]) (use dc ce cn in simp_all)
  from ltr_collect_I [OF this] show ?thesis
    using cs ds by (simp add: sink_node_def sink_store_def)
qed

subsection \<open>Collecting equations\<close>

text \<open>(1) Initial stores are collected at \<^const>\<open>cfg_entry\<close>.\<close>
lemma ltr_collect_init:
  "s \<in> S \<Longrightarrow> s \<in> \<C> (cfg_entry g)"
  using ltr_collect_I[OF valid_ltr.init] by simp

subsection \<open>Context-sensitive / context-insensitive bridge\<close>

text \<open>Bridge (1): every context bucket, and so their union, is included in the
  context-insensitive collection.\<close>
theorem activation_collect_le_ltr_collect:
  "\<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c \<subseteq> \<C> v"
  unfolding activation_collect_def ltr_collect_def by blast

theorem Union_activation_collect_le_ltr_collect:
  "(\<Union>c. \<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c) \<subseteq> \<C> v"
  using activation_collect_le_ltr_collect by blast

text \<open>Bridge (2): the converse needs every valid trace to carry some context.  That premise is
  the whole content of the direction -- a policy that leaves some trace uncontexted loses the
  stores on it, and the union then falls short.  A functional policy has it outright, since
  \<^const>\<open>key\<close> is total; a relational one earns it from conditional totality, which is
  \<open>LTR_Abstract\<close>'s business.  No finiteness assumption either way.\<close>
theorem ltr_collect_eq_Union_activation_of_has_context:
  assumes has_ctx: "\<And>t. t \<in> \<T> \<Longrightarrow> \<exists>c. trace_context \<G> R startcontext g t c"
  shows "\<C> v = (\<Union>c. \<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c)"
proof
  show "\<C> v \<subseteq> (\<Union>c. \<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c)"
  proof
    fix x assume "x \<in> \<C> v"
    then obtain t where t: "t \<in> \<T>" "sink_node t = v" "sink_store t = x"
      by (rule ltr_collect_E)
    from has_ctx [OF t(1)] obtain c where "trace_context \<G> R startcontext g t c" ..
    with t show "x \<in> (\<Union>c. \<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c)"
      by blast
  qed
next
  show "(\<Union>c. \<A>\<^bsub>\<G>,R,startcontext,g,S\<^esub> v c) \<subseteq> \<C> v"
    by (rule Union_activation_collect_le_ltr_collect)
qed

theorem ltr_collect_eq_Union_activation_of_fun:
  "\<C> v
     = (\<Union>c. \<A>\<^bsub>\<G>,call_context_rel_of_fun f,startcontext,g,S\<^esub> v c)"
  by (rule ltr_collect_eq_Union_activation_of_has_context)
     (simp add: trace_context_of_fun_iff)

end


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
  "Root [(Statement 0, s)] \<in> \<T>\<^bsub>\<G>,ltr_witness_cfg,{s}\<^esub>"
proof -
  have "Root [(cfg_entry ltr_witness_cfg, s)] \<in> \<T>\<^bsub>\<G>,ltr_witness_cfg,{s}\<^esub>"
    by (rule valid_ltr.init) simp
  then show ?thesis by simp
qed

theorem ltr_collect_witness:
  "s \<in> \<C>\<^bsub>\<G>,ltr_witness_cfg,{s}\<^esub> (Statement 0)"
  "s(STR ''x'' := 1) \<in> \<C>\<^bsub>\<G>,ltr_witness_cfg,{s}\<^esub> (Statement 1)"
proof -
  have root: "Root [(Statement 0, s)] \<in> \<T>\<^bsub>\<G>,ltr_witness_cfg,{s}\<^esub>"
    by (rule ltr_witness_root)
  show "s \<in> \<C>\<^bsub>\<G>,ltr_witness_cfg,{s}\<^esub> (Statement 0)"
    using ltr_collect_I[OF root] by (simp add: sink_node_def sink_store_def)
  have "extend (Root [(Statement 0, s)]) (Statement 1, s(STR ''x'' := 1))
          \<in> \<T>\<^bsub>\<G>,ltr_witness_cfg,{s}\<^esub>"
    by (rule valid_ltr.intra[OF root, where a = "EA_Assign (STR ''x'') (N 1)"
                                        and v = "Statement 1"])
       (simp_all add: ltr_witness_cfg_def sink_node_def sink_store_def)
  from ltr_collect_I[OF this]
  show "s(STR ''x'' := 1) \<in> \<C>\<^bsub>\<G>,ltr_witness_cfg,{s}\<^esub> (Statement 1)"
    by (simp add: sink_node_def sink_store_def)
qed

end
