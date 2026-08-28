theory LTR_Abstract
  imports LTR_Collect
begin

section \<open>A correlation-preserving abstract interface for valid_ltr\<close>

text \<open>
  The smallest domain-free proof interface through which an abstract over-approximation
  soundly covers the stack-faithful semantics \<^const>\<open>valid_ltr\<close>.  The abstract object is a
  context-indexed concretization

  \<bullet> \<open>acc :: cfg_node \<Rightarrow> 'c \<Rightarrow> store set\<close>

  --- the set of stores the analysis admits at node \<open>v\<close> in abstract context \<open>c\<close>.  No
  \<open>sound_domain\<close>, \<open>abs_state\<close>, solver, or DG dependency appears here.

  The interface fixes four closure obligations --- a root seed (\<open>ROOT\<close>), an intra edge
  (\<open>EDGE\<close>), a call routing (\<open>CALL\<close>), and a return combine (\<open>COMB\<close>) --- and proves that every
  valid trace's sink store lands in its own activation slot, keyed by \<^const>\<open>key\<close>.  The
  load-bearing clause is \<open>COMB\<close>: the callee is read at exactly the context \<open>enterc\<close> computes
  from the caller's own context and the callee-entry store --- so a return can only compose
  the callee whose context was derived from the caller it resumes, not any context that
  happens to cover the callee's concrete entry.  The correlation is not an extra parameter:
  \<open>key_entry_invariant_eq\<close> makes this a theorem of \<^const>\<open>valid_ltr\<close>, so a proof-level
  activation record is unnecessary.

  \<open>enterc u c s\<close> means: given a call from \<open>u\<close> under caller context \<open>c\<close> entering at concrete
  store \<open>s\<close>, this is THE context for the callee.  Every routing instance this project
  supports (unit, call-site/k-call-string, entry-state) is exactly this shape --- a total
  function, never a relation admitting several contexts for one concrete call --- and the
  executable routed solver's own \<open>route\<close> is typed to return a single context.  The abstract
  context type \<open>'c\<close> is arbitrary; \<^const>\<open>key\<close> may still quotient distinct activations to the
  same context.  Nothing here claims a context is an exact activation identity --- only that
  each valid trace lands in its own slot, matched at return via the SAME \<open>enterc\<close>
  application, not rediscovered afterward.
\<close>

subsection \<open>The abstract interface\<close>

locale ltr_gamma =
  fixes g :: cfg and S :: "store set"
    and acc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
    and startcontext :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes ROOT[intro]: "\<And>s. s \<in> S \<Longrightarrow> s \<in> acc (cfg_entry g) startcontext"
    and EDGE[intro]: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> acc u c \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> s' \<in> acc v c"
    and CALL[intro]: "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> acc u c
        \<Longrightarrow> call_enter gs (CallEdge dst pars args) s
              \<in> acc (FunctionEntry p) (enterc u c (call_enter gs (CallEdge dst pars args) s))"
    and COMB[intro]: "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> acc cl c1 \<Longrightarrow> t \<in> acc (FunctionResult p) (enterc cl c1 es)
        \<Longrightarrow> call_enter_store gs g cl s es
        \<Longrightarrow> combine_collect gs dst s t \<in> acc cont c1"
begin

text \<open>\<open>bnd u\<close>: the sink store of \<open>u\<close> is admitted at \<open>u\<close>'s own node under \<open>u\<close>'s own
  \<^const>\<open>key\<close>-assigned context.\<close>
abbreviation bnd :: "ltr \<Rightarrow> bool" where
  "bnd u \<equiv> sink_store u \<in> acc (sink_node u) (key enterc startcontext u)"

definition gamma_ltr :: "ltr set" where
  "gamma_ltr = {t. bnd t}"

subsection \<open>Closure under the four ltr_F clauses\<close>

text \<open>\<open>root_closed\<close>: the main activation's seed store is admitted at \<open>startcontext\<close>, the
  \<^const>\<open>key\<close> of every \<^const>\<open>Root\<close>.\<close>
lemma root_closed: "s \<in> S \<Longrightarrow> bnd (Root [(cfg_entry g, s)])"
  using ROOT by (simp add: sink_node_def sink_store_def)

text \<open>\<open>intra_closed\<close>: an intra edge preserves \<^const>\<open>key\<close> (unchanged by \<^const>\<open>extend\<close> on a
  non-empty path, \<open>key_extend_nonempty\<close>) and covers the concrete step through \<open>EDGE\<close> at that
  same context.\<close>
lemma intra_closed:
  assumes e: "(sink_node t, a, v) \<in> intra g"
    and st: "s' \<in> edge_step a (sink_store t)" and pne: "path t \<noteq> []" and iht: "bnd t"
  shows "bnd (extend t (v, s'))"
proof -
  have keq: "key enterc startcontext (extend t (v, s')) = key enterc startcontext t"
    using pne by (rule key_extend_nonempty)
  have "s' \<in> acc v (key enterc startcontext t)" by (rule EDGE[OF e iht st])
  then show ?thesis by (simp add: keq)
qed

text \<open>\<open>call_closed\<close>: the entered store is admitted in the callee slot at exactly the context
  \<open>enterc\<close> computes from the caller's own \<^const>\<open>key\<close> --- exactly the context \<^const>\<open>key\<close>
  assigns to the new \<^const>\<open>Call\<close>.\<close>
lemma call_closed:
  assumes e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ihc: "bnd caller"
  shows "bnd (Call caller
           [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
  using CALL[OF e ihc] by simp

text \<open>\<open>return_closed\<close>: the matched return.  \<open>key_entry_invariant_eq\<close> lets the callee's
  context be constructed directly from the caller's own \<^const>\<open>key\<close> via \<open>enterc\<close>, so \<open>COMB\<close>
  is applied at exactly the context the callee's own binding used --- never rediscovered
  independently.\<close>
lemma return_closed:
  assumes callee_val: "callee \<in> valid_ltr gs g S"
    and cof: "caller_of callee = Some caller"
    and res: "sink_node callee = FunctionResult p"
    and comb: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ih_caller: "bnd caller"
    and ih_callee: "bnd callee"
  shows "bnd (Resume caller callee (path caller
               @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
proof -
  let ?u = "Resume caller callee (path caller
    @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))])"
  have keq: "key enterc startcontext ?u = key enterc startcontext caller" by simp
  have keyeq: "key enterc startcontext callee
      = enterc (sink_node caller) (key enterc startcontext caller) (entry_store callee)"
    by (rule key_entry_invariant_eq[OF callee_val cof])
  have call_enter:
    "call_enter_store gs g (sink_node caller) (sink_store caller) (entry_store callee)"
    using key_entry_invariant_call_enterD[OF callee_val cof] .
  have t2: "sink_store callee \<in> acc (FunctionResult p)
              (enterc (sink_node caller) (key enterc startcontext caller) (entry_store callee))"
    using ih_callee res keyeq by simp
  have "combine_collect gs dst (sink_store caller) (sink_store callee)
          \<in> acc cont (key enterc startcontext caller)"
    by (rule COMB[OF comb ih_caller t2 call_enter])
  then show "bnd ?u" by (simp add: keq sink_node_def sink_store_def)
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
  show "bnd (Call caller
          [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
    by (rule call_closed[OF e ihc])
next
  fix callee caller p dst pars args cont
  assume cv: "callee \<in> valid_ltr gs g S" and ch: "\<forall>u \<in> callers callee. bnd u"
    and cof: "caller_of callee = Some caller" and res: "sink_node callee = FunctionResult p"
    and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  have ih_caller: "bnd caller" using ch cof callers_caller_subset callers_refl by blast
  have ih_callee: "bnd callee" using ch callers_refl by blast
  show "bnd (Resume caller callee (path caller
             @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
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

end

subsection \<open>Non-vacuity\<close>

text \<open>The interface is satisfiable for every graph, seed set, routing function, and seed
  context --- the top abstraction \<open>acc = (\<lambda>_ _. UNIV)\<close> discharges the remaining three
  obligations.\<close>
lemma ltr_gamma_UNIV: "ltr_gamma g S (\<lambda>_ _. UNIV) enterc startcontext gs"
  by unfold_locales auto

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
    and call: "\<And>u dst pars args p cont s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> B u \<Longrightarrow> call_enter gs (CallEdge dst pars args) s \<in> B (FunctionEntry p)"
    and combine: "\<And>cl dst pars args p cont s t.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> B cl \<Longrightarrow> t \<in> B (FunctionResult p) \<Longrightarrow> combine_collect gs dst s t \<in> B cont"
  shows "ltr_collect gs g S0 v \<subseteq> B v"
proof -
  interpret G: ltr_gamma g S0 "\<lambda>v _. B v" "\<lambda>_ _ _. ()" "()" gs
  proof (standard, goal_cases ROOT EDGE CALL COMB)
    case (ROOT s) then show ?case using entry by auto
  next
    case (EDGE u a w c s s') then show ?case using edge by simp
  next
    case (CALL u dst args p cont c s) then show ?case using call by simp
  next
    case (COMB cl dst args p cont c1 s t es) then show ?case using combine by simp
  qed
  show ?thesis
  proof (rule subsetI)
    fix x assume "x \<in> ltr_collect gs g S0 v"
    then obtain u where u: "u \<in> valid_ltr gs g S0" "sink_node u = v" "sink_store u = x"
      by (rule ltr_collect_E)
    have gt: "G.bnd u" using G.valid_ltr_subset_gamma_ltr u(1) by (auto simp: G.gamma_ltr_def)
    then have "sink_store u \<in> B (sink_node u)" by simp
    then show "x \<in> B v" using u(2,3) by simp
  qed
qed


end

