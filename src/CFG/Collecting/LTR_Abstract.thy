theory LTR_Abstract
  imports LTR_Collect
begin

section \<open>A correlation-preserving abstract interface for valid_ltr\<close>

text \<open>
  The smallest domain-free proof interface through which an abstract over-approximation
  soundly covers the stack-faithful semantics \<^const>\<open>valid_ltr\<close>.  The abstract object is a
  context-indexed concretization

  \<^item> \<open>acc :: cfg_node \<Rightarrow> 'c \<Rightarrow> store set\<close>

  --- the set of stores the analysis admits at node \<open>v\<close> in abstract context \<open>c\<close>.  No
  \<open>sound_domain\<close>, \<open>abs_state\<close>, solver, or DG dependency appears here.

  The interface fixes five closure obligations --- a root seed (\<open>ROOT\<close>), an intra edge
  (\<open>EDGE\<close>), totality of context selection (\<open>ADMISS_TOTAL\<close>), a call routing (\<open>CALL\<close>), and a
  return combine (\<open>COMB\<close>) --- and proves that every valid trace's sink store lands in every
  activation slot it is admissibly assigned to.  The load-bearing clause is \<open>COMB\<close>: the
  callee is read at whichever context \<open>c2\<close> the SAME \<open>admiss\<close> fact used to justify the
  callee's own admissibility relates to the caller's context \<open>c1\<close> --- so a return can only
  compose the callee whose context was chosen from the caller it resumes, not any context
  that happens to cover the callee's concrete entry.  The correlation is not an extra
  parameter: \<open>ctx_key_entry_invariant_iff\<close> makes this a theorem of \<^const>\<open>valid_ltr\<close>, so a
  proof-level activation record is unnecessary.

  \<open>admiss u c s c'\<close> means: given a call from \<open>u\<close> under caller context \<open>c\<close> entering at
  concrete store \<open>s\<close>, \<open>c'\<close> is an admissible context for the callee.  This generalizes a
  deterministic \<open>enterc\<close> (\<open>admiss_exact\<close>, \<^theory>\<open>Voblint_CFG.CFG_Local_Trace\<close>) to a
  relation: several \<open>c'\<close> may be admissible for the same call, which is what lets an abstract
  analysis choose a WIDE context (e.g. covering every concrete argument to \<open>random()\<close>) rather
  than being forced to compute one exactly per concrete store.  The abstract context type
  \<open>'c\<close> is arbitrary; \<^const>\<open>ctx_key\<close> may quotient distinct activations to the same context,
  and several contexts may be admissible for one activation.  Nothing here claims a context
  is an exact activation identity --- only that each valid trace lands in every admissible
  slot, matched at return via the SAME \<open>admiss\<close> derivation, not rediscovered afterward.
\<close>

subsection \<open>The abstract interface\<close>

locale ltr_gamma =
  fixes g :: cfg and S :: "store set"
    and acc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    and admiss :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c \<Rightarrow> bool"
    and startc :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes ROOT[intro]: "\<And>s. s \<in> S \<Longrightarrow> s \<in> acc (cfg_entry g) startc"
    and EDGE[intro]: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> acc u c \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> s' \<in> acc v c"
    and ADMISS_TOTAL: "\<And>u c s. \<exists>c'. admiss u c s c'"
    and CALL[intro]: "\<And>u dst pars args p cont c s c'.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> acc u c \<Longrightarrow> admiss u c (call_enter gs (CallEdge dst pars args) s) c'
        \<Longrightarrow> call_enter gs (CallEdge dst pars args) s \<in> acc (FunctionEntry p) c'"
    and COMB[intro]: "\<And>cl dst pars args p cont c1 c2 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> acc cl c1 \<Longrightarrow> admiss cl c1 es c2 \<Longrightarrow> t \<in> acc (FunctionResult p) c2
        \<Longrightarrow> call_enter_store gs g cl s es
        \<Longrightarrow> combine_collect gs dst s t \<in> acc cont c1"
begin

text \<open>\<open>bnd u\<close>: the sink store of \<open>u\<close> is admitted at \<open>u\<close>'s own node under every context
  \<open>admiss\<close>/\<open>ctx_key\<close> admissibly assigns to \<open>u\<close>. Vacuously true at any non-admissible \<open>c\<close>.\<close>
abbreviation bnd :: "ltr \<Rightarrow> bool" where
  "bnd u \<equiv> \<forall>c. ctx_key admiss startc u c \<longrightarrow> sink_store u \<in> acc (sink_node u) c"

definition gamma_ltr :: "ltr set" where
  "gamma_ltr = {t. bnd t}"

subsection \<open>Closure under the four ltr_F clauses\<close>

text \<open>\<open>root_closed\<close>: the main activation's seed store is admitted at every context admissibly
  reachable from the entry seed --- only \<open>startc\<close> itself, per \<open>ctx_key_Root\<close>.\<close>
lemma root_closed: "s \<in> S \<Longrightarrow> bnd (Root [(cfg_entry g, s)])"
  using ROOT by (auto simp: sink_node_def sink_store_def elim: ctx_key_RootE)

text \<open>\<open>intra_closed\<close>: an intra edge preserves every admissible context (\<^const>\<open>ctx_key\<close> is
  unchanged by \<^const>\<open>extend\<close> on a non-empty path, \<open>ctx_key_extend_nonempty\<close>) and covers the
  concrete step through \<open>EDGE\<close> at that same context.\<close>
lemma intra_closed:
  assumes e: "(sink_node t, a, v) \<in> intra g"
    and st: "s' \<in> edge_step a (sink_store t)" and pne: "path t \<noteq> []" and iht: "bnd t"
  shows "bnd (extend t (v, s'))"
proof (intro allI impI)
  fix c assume "ctx_key admiss startc (extend t (v, s')) c"
  hence ck: "ctx_key admiss startc t c" using pne by (simp add: ctx_key_extend_nonempty)
  have mem: "sink_store t \<in> acc (sink_node t) c" using iht ck by blast
  have "s' \<in> acc v c" by (rule EDGE[OF e mem st])
  then show "sink_store (extend t (v, s')) \<in> acc (sink_node (extend t (v, s'))) c"
    by simp
qed

text \<open>\<open>call_closed\<close>: the entered store is admitted in the callee slot at any context
  \<open>admiss\<close> relates to the caller's own admissible context --- exactly the contexts
  \<open>ctx_key_Call\<close> assigns to the new \<^const>\<open>Call\<close>.\<close>
lemma call_closed:
  assumes e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ihc: "bnd caller"
  shows "bnd (Call caller [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
proof (intro allI impI)
  fix c' assume "ctx_key admiss startc
      (Call caller [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))]) c'"
  then obtain c where c: "ctx_key admiss startc caller c"
    and adm: "admiss (sink_node caller) c (call_enter gs (CallEdge dst pars args) (sink_store caller)) c'"
    by (auto elim: ctx_key_CallE)
  have mem: "sink_store caller \<in> acc (sink_node caller) c" using ihc c by blast
  have "call_enter gs (CallEdge dst pars args) (sink_store caller) \<in> acc (FunctionEntry p) c'"
    by (rule CALL[OF e mem adm])
  then show "sink_store (Call caller [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])
               \<in> acc (sink_node (Call caller [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])) c'"
    by simp
qed

text \<open>\<open>return_closed\<close>: the matched return.  \<open>ctx_key_entry_invariant_iff\<close> lets the callee's
  context \<open>c2\<close> be constructed directly from the caller's own admissible context \<open>c1\<close> via
  \<open>admiss\<close> (\<open>ADMISS_TOTAL\<close> supplies a witness), so \<open>COMB\<close> is applied at the SAME \<open>c1\<close>/\<open>c2\<close>
  pair the callee's own binding used --- never rediscovered independently.\<close>
lemma return_closed:
  assumes callee_val: "callee \<in> valid_ltr gs g S"
    and cof: "caller_of callee = Some caller"
    and res: "sink_node callee = FunctionResult p"
    and comb: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ih_caller: "bnd caller"
    and ih_callee: "bnd callee"
  shows "bnd (Resume caller callee
               (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
proof (intro allI impI)
  fix c1 assume "ctx_key admiss startc (Resume caller callee
      (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))])) c1"
  hence ck1: "ctx_key admiss startc caller c1" by (auto elim: ctx_key_ResumeE)
  have s1: "sink_store caller \<in> acc (sink_node caller) c1" using ih_caller ck1 by blast
  obtain c2 where adm: "admiss (sink_node caller) c1 (entry_store callee) c2"
    using ADMISS_TOTAL by blast
  have ck2: "ctx_key admiss startc callee c2"
    using ctx_key_entry_invariant_iff[OF callee_val cof] ck1 adm by fastforce
  have call_enter: "call_enter_store gs g (sink_node caller) (sink_store caller) (entry_store callee)"
    using ctx_key_entry_invariant_call_enterD[OF callee_val cof] .
  have t2': "sink_store callee \<in> acc (sink_node callee) c2" using ih_callee ck2 by blast
  have t2: "sink_store callee \<in> acc (FunctionResult p) c2" using t2' res by simp
  have "combine_collect gs dst (sink_store caller) (sink_store callee) \<in> acc cont c1"
    by (rule COMB[OF comb s1 adm t2 call_enter])
  then show "sink_store (Resume caller callee
               (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))
             \<in> acc (sink_node (Resume caller callee
               (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))) c1"
    by (simp add: sink_node_def sink_store_def)
qed

subsection \<open>The generic soundness theorem\<close>

text \<open>The bound holds along the whole caller chain, by \<^const>\<open>valid_ltr\<close> rule induction
  feeding the four closure lemmas.  The chain, not a per-node statement, is what the \<open>ret\<close>
  case needs: it recovers its caller structurally, and the caller lies in the callee's
  chain.\<close>
lemma gamma_chain:
  "t \<in> valid_ltr gs g S \<Longrightarrow> \<forall>u \<in> callers t. bnd u"
proof (rule caller_chain_closure)
  fix s assume "s \<in> S"
  then show "bnd (Root [(cfg_entry g, s)])" by (rule root_closed)
next
  fix t a v s' assume ht: "t \<in> valid_ltr gs g S" and ch: "\<forall>u \<in> callers t. bnd u"
    and e: "(sink_node t, a, v) \<in> intra g" and st: "s' \<in> edge_step a (sink_store t)"
  have pt: "path t \<noteq> []" using ht valid_ltr_path_nonempty by blast
  have iht: "bnd t" using ch callers_refl by blast
  show "bnd (extend t (v, s'))" by (rule intra_closed[OF e st pt iht])
next
  fix caller dst pars args p cont
  assume ch: "\<forall>u \<in> callers caller. bnd u"
    and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  have ihc: "bnd caller" using ch callers_refl by blast
  show "bnd (Call caller [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
    by (rule call_closed[OF e ihc])
next
  fix callee caller p dst pars args cont
  assume cv: "callee \<in> valid_ltr gs g S" and ch: "\<forall>u \<in> callers callee. bnd u"
    and cof: "caller_of callee = Some caller" and res: "sink_node callee = FunctionResult p"
    and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  have ih_caller: "bnd caller" using ch cof callers_caller_subset callers_refl by blast
  have ih_callee: "bnd callee" using ch callers_refl by blast
  show "bnd (Resume caller callee
             (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
    by (rule return_closed[OF cv cof res e ih_caller ih_callee])
qed

text \<open>Every valid trace's sink lies in its own activation slot: \<^const>\<open>valid_ltr\<close> is
  soundly over-approximated by \<open>gamma_ltr\<close>.\<close>
theorem valid_ltr_subset_gamma_ltr: "valid_ltr gs g S \<subseteq> gamma_ltr"
proof (rule subsetI)
  fix t assume "t \<in> valid_ltr gs g S"
  then have "\<forall>u \<in> callers t. bnd u" by (rule gamma_chain)
  then have "bnd t" using callers_refl by blast
  then show "t \<in> gamma_ltr" by (simp add: gamma_ltr_def)
qed

text \<open>The same statement in fixed-point form, via \<open>valid_ltr_eq_lfp\<close>.\<close>
corollary lfp_ltr_F_subset_gamma_ltr: "lfp (ltr_F gs g S) \<subseteq> gamma_ltr"
  using valid_ltr_subset_gamma_ltr by (simp add: valid_ltr_eq_lfp)

subsection \<open>Node and context projection of the soundness bound\<close>

text \<open>Node projection: at any node \<open>v\<close>, the concrete collection is covered by the union of
  the abstract slots at \<open>v\<close> over all contexts. \<open>ADMISS_TOTAL\<close> gives every trace at least one
  admissible context (\<open>ctx_key_exists\<close>), so the union is never taken over an empty witness
  set.\<close>
theorem ltr_collect_subset_acc_Union:
  "ltr_collect gs g S v \<subseteq> (\<Union>c. acc v c)"
proof (rule subsetI)
  fix x assume "x \<in> ltr_collect gs g S v"
  then obtain t where t: "t \<in> valid_ltr gs g S" "sink_node t = v" "sink_store t = x"
    by (rule ltr_collect_E)
  have bt: "bnd t" using valid_ltr_subset_gamma_ltr t(1) by (auto simp: gamma_ltr_def)
  obtain c where "ctx_key admiss startc t c"
    using ctx_key_exists[where admiss = admiss, OF ADMISS_TOTAL] by blast
  with bt have "x \<in> acc v c" using t(2,3) by blast
  then show "x \<in> (\<Union>c. acc v c)" by blast
qed

text \<open>\<open>activation_collect\<close>'s context projection is restated directly against \<^const>\<open>ctx_key\<close>
  once \<open>activation_collect\<close> itself is redefined against it (\<open>Routed_Context.thy\<close> instance
  layer); the exact-match corollaries formerly here (\<open>activation_collect_subset_acc\<close>,
  \<open>return_uses_matched_callee\<close>, \<open>two_callers_separated\<close>) are subsumed by \<open>return_closed\<close> at
  \<open>admiss = admiss_exact enterc\<close>, so they are not restated separately.\<close>

end

subsection \<open>Non-vacuity\<close>

text \<open>The interface is satisfiable for every graph, seed set, admissibility relation (given
  totality), and seed context --- the top abstraction \<open>acc = (\<lambda>_ _. UNIV)\<close> discharges the
  remaining four obligations.\<close>
lemma ltr_gamma_UNIV:
  assumes "\<And>u c s. \<exists>c'. admiss u c s c'"
  shows "ltr_gamma g S (\<lambda>_ _. UNIV) admiss startc gs"
  using assms by unfold_locales auto

subsection \<open>Monovariant semantic post-fixpoint\<close>

text \<open>
  Set-valued entry, edge, call, and combine closure of a candidate node map \<open>B\<close> bounds the
  stack-faithful \<^const>\<open>ltr_collect\<close> at every node.  The proof interprets \<^locale>\<open>ltr_gamma\<close>
  at \<open>acc v _ = B v\<close> with the trivial one-point context; its combine obligation follows one
  caller and one callee exit.
\<close>
lemma ltr_collect_semantic_postfix:
  fixes g :: cfg and B :: "cfg_node \<Rightarrow> store set" and S0 :: "store set" and v :: cfg_node
    and gs :: "vname \<Rightarrow> bool"
  assumes entry: "S0 \<subseteq> B (cfg_entry g)"
    and edge: "\<And>u a w s s'. (u, a, w) \<in> intra g \<Longrightarrow> s \<in> B u \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> s' \<in> B w"
    and call: "\<And>u dst pars args p cont s. (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> B u \<Longrightarrow> call_enter gs (CallEdge dst pars args) s \<in> B (FunctionEntry p)"
    and combine: "\<And>cl dst pars args p cont s t. (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> B cl \<Longrightarrow> t \<in> B (FunctionResult p) \<Longrightarrow> combine_collect gs dst s t \<in> B cont"
  shows "ltr_collect gs g S0 v \<subseteq> B v"
proof -
  interpret G: ltr_gamma g S0 "\<lambda>v _. B v" "admiss_exact (\<lambda>_ _ _. ())" "()" gs
  proof (standard, goal_cases ROOT EDGE ADMISS_TOTAL CALL COMB)
    case (ROOT s) then show ?case using entry by auto
  next
    case (EDGE u a w c s s') then show ?case using edge by simp
  next
    case (ADMISS_TOTAL u c s) then show ?case by (simp add: admiss_exact_def)
  next
    case (CALL u dst args p cont c s c') then show ?case using call by simp
  next
    case (COMB cl dst args p cont c1 c2 s t es) then show ?case using combine by simp
  qed
  show ?thesis
  proof (rule subsetI)
    fix x assume "x \<in> ltr_collect gs g S0 v"
    then obtain u where u: "u \<in> valid_ltr gs g S0" "sink_node u = v" "sink_store u = x"
      by (rule ltr_collect_E)
    have gt: "G.bnd u" using G.valid_ltr_subset_gamma_ltr u(1) by (auto simp: G.gamma_ltr_def)
    have ck: "ctx_key (admiss_exact (\<lambda>_ _ _. ())) () u ()"
      by (simp add: ctx_key_exact_iff)
    have "sink_store u \<in> B (sink_node u)" using gt ck by blast
    then show "x \<in> B v" using u(2,3) by simp
  qed
qed

end

