theory LTR_Abstract
  imports LTR_Collect
begin

section \<open>What an analysis must satisfy to be sound\<close>

text \<open>
  An analysis claims: "at node \<open>v\<close>, in context \<open>c\<close>, only these stores can occur".  This
  theory says what such a claim must satisfy to be believed, and proves that satisfying it
  is enough --- every valid trace's final store really does lie in the set claimed for its
  own node and context.  No domain, solver or dependency graph appears here; they
  instantiate this.

  The claim is just a function \<open>cover\<close> from a node and a context to a set of stores, and
  there are four obligations on it: the seed stores are covered at the entry (\<open>INIT\<close>),
  each intra edge keeps them covered (\<open>INTRA\<close>), a call covers the entered store at the
  callee (\<open>CALL\<close>), and a return covers the combined store back at the caller (\<open>RETURN\<close>).

  \<open>RETURN\<close> is the load-bearing one.  The callee is read at exactly the context \<open>enterc\<close>
  computes from the caller's own context and the callee-entry store, so a return may only
  compose the callee whose context came from the caller it is resuming --- not any context
  that happens to cover that callee's entry.  This correlation is not an extra parameter to
  assume: \<open>key_entry_invariant_eq\<close> makes it a theorem about \<^const>\<open>valid_ltr\<close>, which is
  why no activation record is needed at proof level.

  A context is not claimed to identify an activation.  \<^const>\<open>key\<close> may well give two
  distinct activations the same context; the theorem is only that each trace lands in its
  own slot, matched at return through the same \<open>enterc\<close> application rather than
  rediscovered afterwards.
\<close>

subsection \<open>The abstract interface\<close>

locale ltr_coverage =
  fixes g :: cfg and S :: "store set"
    and cover :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
    and initial_ctx :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes INIT[intro]: "\<And>s. s \<in> S \<Longrightarrow> s \<in> cover (cfg_entry g) initial_ctx"
    and INTRA[intro]: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> cover u c \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> s' \<in> cover v c"
    and CALL[intro]: "\<And>u dst pars args p cont c s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover u c
        \<Longrightarrow> call_enter gs (CallEdge dst pars args) s
              \<in> cover (FunctionEntry p) (enterc u c (call_enter gs (CallEdge dst pars args) s))"
    and RETURN[intro]: "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover cl c1 \<Longrightarrow> t \<in> cover (FunctionResult p) (enterc cl c1 es)
        \<Longrightarrow> call_enter_store gs g cl s es
        \<Longrightarrow> combine_collect gs dst s t \<in> cover cont c1"
begin

text \<open>\<open>trace_covered u\<close>: the sink store of \<open>u\<close> is admitted at \<open>u\<close>'s own node under \<open>u\<close>'s own
  \<^const>\<open>key\<close>-assigned context.\<close>
abbreviation trace_covered :: "ltr \<Rightarrow> bool" where
  "trace_covered u \<equiv> sink_store u \<in> cover (sink_node u) (key enterc initial_ctx u)"

subsection \<open>Closure under the four ltr_F clauses\<close>

text \<open>\<open>init_covered\<close>: the main activation's seed store is admitted at \<open>initial_ctx\<close>, the
  \<^const>\<open>key\<close> of every \<^const>\<open>Root\<close>.\<close>
lemma init_covered: "s \<in> S \<Longrightarrow> trace_covered (Root [(cfg_entry g, s)])"
  using INIT by (simp add: sink_node_def sink_store_def)

text \<open>\<open>intra_covered\<close>: an intra edge preserves \<^const>\<open>key\<close> (unchanged by \<^const>\<open>extend\<close> on a
  non-empty path, \<open>key_extend_nonempty\<close>) and covers the concrete step through \<open>INTRA\<close> at
  that same context.\<close>
lemma intra_covered:
  assumes e: "(sink_node t, a, v) \<in> intra g"
    and st: "s' \<in> edge_step a (sink_store t)" and pne: "path t \<noteq> []" and iht: "trace_covered t"
  shows "trace_covered (extend t (v, s'))"
proof -
  have keq: "key enterc initial_ctx (extend t (v, s')) = key enterc initial_ctx t"
    using pne by (rule key_extend_nonempty)
  have "s' \<in> cover v (key enterc initial_ctx t)" by (rule INTRA[OF e iht st])
  then show ?thesis by (simp add: keq)
qed

text \<open>\<open>call_covered\<close>: the entered store is admitted in the callee slot at exactly the context
  \<open>enterc\<close> computes from the caller's own \<^const>\<open>key\<close> --- exactly the context \<^const>\<open>key\<close>
  assigns to the new \<^const>\<open>Call\<close>.\<close>
lemma call_covered:
  assumes e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ihc: "trace_covered caller"
  shows "trace_covered (Call caller
           [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
  using CALL[OF e ihc] by simp

text \<open>\<open>return_covered\<close>: the matched return.  \<open>key_entry_invariant_eq\<close> lets the callee's
  context be constructed directly from the caller's own \<^const>\<open>key\<close> via \<open>enterc\<close>, so
  \<open>RETURN\<close> is applied at exactly the context the callee's own binding used --- never
  rediscovered independently.\<close>
lemma return_covered:
  assumes callee_val: "callee \<in> valid_ltr gs g S"
    and cof: "caller_of callee = Some caller"
    and res: "sink_node callee = FunctionResult p"
    and comb: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ih_caller: "trace_covered caller"
    and ih_callee: "trace_covered callee"
  shows "trace_covered (Resume caller callee (path caller
               @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
proof -
  let ?u = "Resume caller callee (path caller
    @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))])"
  have keq: "key enterc initial_ctx ?u = key enterc initial_ctx caller" by simp
  have keyeq: "key enterc initial_ctx callee
      = enterc (sink_node caller) (key enterc initial_ctx caller) (entry_store callee)"
    by (rule key_entry_invariant_eq[OF callee_val cof])
  have call_enter:
    "call_enter_store gs g (sink_node caller) (sink_store caller) (entry_store callee)"
    using key_entry_invariant_call_enterD[OF callee_val cof] .
  have t2: "sink_store callee \<in> cover (FunctionResult p)
              (enterc (sink_node caller) (key enterc initial_ctx caller) (entry_store callee))"
    using ih_callee res keyeq by simp
  have "combine_collect gs dst (sink_store caller) (sink_store callee)
          \<in> cover cont (key enterc initial_ctx caller)"
    by (rule RETURN[OF comb ih_caller t2 call_enter])
  then show "trace_covered ?u" by (simp add: keq sink_node_def sink_store_def)
qed

subsection \<open>The generic soundness theorem\<close>

text \<open>The bound holds along the whole caller chain, by \<^const>\<open>valid_ltr\<close> rule induction
  feeding the four closure lemmas.  The chain, not a per-node statement, is what the
  \<open>RETURN\<close> case needs: it recovers its caller structurally, and the caller lies in the
  callee's chain.\<close>
lemma caller_chain_covered:
  "t \<in> valid_ltr gs g S \<Longrightarrow> \<forall>u \<in> callers t. trace_covered u"
proof (rule caller_chain_closure)
  fix s assume "s \<in> S"
  then show "trace_covered (Root [(cfg_entry g, s)])" by (rule init_covered)
next
  fix t a v s' assume ht: "t \<in> valid_ltr gs g S" and ch: "\<forall>u \<in> callers t. trace_covered u"
    and e: "(sink_node t, a, v) \<in> intra g" and st: "s' \<in> edge_step a (sink_store t)"
  have pt: "path t \<noteq> []" using ht valid_ltr_path_nonempty by blast
  have iht: "trace_covered t" using ch callers_refl by blast
  show "trace_covered (extend t (v, s'))" by (rule intra_covered[OF e st pt iht])
next
  fix caller dst pars args p cont
  assume ch: "\<forall>u \<in> callers caller. trace_covered u"
    and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  have ihc: "trace_covered caller" using ch callers_refl by blast
  show "trace_covered (Call caller
          [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
    by (rule call_covered[OF e ihc])
next
  fix callee caller p dst pars args cont
  assume cv: "callee \<in> valid_ltr gs g S" and ch: "\<forall>u \<in> callers callee. trace_covered u"
    and cof: "caller_of callee = Some caller" and res: "sink_node callee = FunctionResult p"
    and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  have ih_caller: "trace_covered caller" using ch cof callers_caller_subset callers_refl by blast
  have ih_callee: "trace_covered callee" using ch callers_refl by blast
  show "trace_covered (Resume caller callee (path caller
             @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
    by (rule return_covered[OF cv cof res e ih_caller ih_callee])
qed

text \<open>Every valid trace's sink lies in its own activation slot: \<^const>\<open>valid_ltr\<close> is
  soundly over-approximated by \<open>trace_covered\<close>.\<close>
theorem valid_ltr_covered: "t \<in> valid_ltr gs g S \<Longrightarrow> trace_covered t"
proof -
  assume "t \<in> valid_ltr gs g S"
  then have "\<forall>u \<in> callers t. trace_covered u" by (rule caller_chain_covered)
  then show "trace_covered t" using callers_refl by blast
qed

end

subsection \<open>Non-vacuity\<close>

text \<open>The interface is satisfiable for every graph, seed set, routing function, and seed
  context --- the top abstraction \<open>cover = (\<lambda>_ _. UNIV)\<close> discharges the remaining three
  obligations.\<close>
lemma ltr_coverage_UNIV: "ltr_coverage g S (\<lambda>_ _. UNIV) enterc initial_ctx gs"
  by unfold_locales auto

subsection \<open>Monovariant semantic post-fixpoint\<close>

text \<open>
  Set-valued entry, edge, call, and combine closure of a candidate node map \<open>B\<close> bounds the
  stack-faithful \<^const>\<open>ltr_collect\<close> at every node.  The proof interprets
  \<^locale>\<open>ltr_coverage\<close> at \<open>cover v _ = B v\<close> with the trivial one-point context; its combine
  obligation follows one caller and one callee exit.
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
  interpret G: ltr_coverage g S0 "\<lambda>v _. B v" "\<lambda>_ _ _. ()" "()" gs
  proof (standard, goal_cases INIT INTRA CALL RETURN)
    case (INIT s) then show ?case using entry by auto
  next
    case (INTRA u a w c s s') then show ?case using edge by simp
  next
    case (CALL u dst args p cont c s) then show ?case using call by simp
  next
    case (RETURN cl dst args p cont c1 s t es) then show ?case using combine by simp
  qed
  show ?thesis
  proof (rule subsetI)
    fix x assume "x \<in> ltr_collect gs g S0 v"
    then obtain u where u: "u \<in> valid_ltr gs g S0" "sink_node u = v" "sink_store u = x"
      by (rule ltr_collect_E)
    have gt: "G.trace_covered u" using G.valid_ltr_covered[OF u(1)] .
    then have "sink_store u \<in> B (sink_node u)" by simp
    then show "x \<in> B v" using u(2,3) by simp
  qed
qed


end

