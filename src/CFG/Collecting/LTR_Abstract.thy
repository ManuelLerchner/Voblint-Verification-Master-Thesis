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

  The interface fixes four closure obligations --- a root seed (\<open>ROOT\<close>), an intra edge
  (\<open>EDGE\<close>), a call routing (\<open>CALL\<close>), and a return combine (\<open>COMB\<close>) --- one per phenomenon,
  and proves that every valid trace's sink store lands in its own activation slot.  The
  load-bearing clause is \<open>COMB\<close>: the callee is read at context \<open>enterc c1 es\<close> --- the
  caller context \<open>c1\<close> routed through the callee's own bound entry store --- so a return can
  only compose the callee whose context descends from the caller it resumes.  The
  correlation is not an extra parameter: \<open>callee_entry_invariant\<close> makes \<open>enterc c1
  es\<close> a theorem of \<^const>\<open>valid_ltr\<close>, so a proof-level activation record is unnecessary.

  The abstract context type \<open>'c\<close> is arbitrary; \<^const>\<open>key\<close> may quotient distinct
  activations to the same context.  Nothing here claims a key is an exact activation
  identity --- only that each valid trace lands in some slot, matched at return.
\<close>

subsection \<open>The abstract interface\<close>

locale ltr_gamma =
  fixes g :: cfg and S :: "store set"
    and acc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
    and seedc :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes ROOT[intro]: "\<And>s. s \<in> S \<Longrightarrow> s \<in> acc (cfg_entry g) seedc"
    and EDGE[intro]: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> acc u c \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> s' \<in> acc v c"
    and CALL[intro]: "\<And>u dst pars args p cont c s. (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> acc u c \<Longrightarrow> call_enter gs (CallEdge dst pars args) s
              \<in> acc (FunctionEntry p) (enterc u c (call_enter gs (CallEdge dst pars args) s))"
    and COMB[intro]: "\<And>cl dst pars args p cont c1 s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> acc cl c1 \<Longrightarrow> t \<in> acc (FunctionResult p) (enterc cl c1 es)
        \<Longrightarrow> call_enter_store gs g cl s es
        \<Longrightarrow> combine_collect gs dst s t \<in> acc cont c1"
begin

text \<open>\<open>bnd u\<close>: the sink store of \<open>u\<close> is admitted at \<open>u\<close>'s own node and activation
  context.\<close>
abbreviation bnd :: "ltr \<Rightarrow> bool" where
  "bnd u \<equiv> sink_store u \<in> acc (sink_node u) (key enterc seedc u)"

definition gamma_ltr :: "ltr set" where
  "gamma_ltr = {t. bnd t}"

subsection \<open>Closure under the four ltr_F clauses\<close>

text \<open>\<open>root_closed\<close>: the main activation's seed store is admitted at the entry seed
  context.\<close>
lemma root_closed: "s \<in> S \<Longrightarrow> bnd (Root [(cfg_entry g, s)])"
  using ROOT by (simp add: sink_node_def sink_store_def)

text \<open>\<open>intra_closed\<close>: an intra edge preserves the context (\<^const>\<open>key\<close> is unchanged by
  \<^const>\<open>extend\<close> on a non-empty path) and covers the concrete step through \<open>EDGE\<close>.\<close>
lemma intra_closed:
  assumes e: "(sink_node t, a, v) \<in> intra g"
    and st: "s' \<in> edge_step a (sink_store t)" and pne: "path t \<noteq> []" and iht: "bnd t"
  shows "bnd (extend t (v, s'))"
proof -
  have "s' \<in> acc v (key enterc seedc t)"
    by (rule EDGE[OF e iht st])
  then show ?thesis using pne by (simp add: key_extend_nonempty)
qed

text \<open>\<open>call_closed\<close>: the entered store is admitted in the callee slot at the routed callee
  context \<open>enterc (key caller) (enter_state (sink_store caller))\<close> --- exactly \<^const>\<open>key\<close>
  of the new \<^const>\<open>Call\<close>.\<close>
lemma call_closed:
  assumes e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ihc: "bnd caller"
  shows "bnd (Call caller [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
proof -
  have "call_enter gs (CallEdge dst pars args) (sink_store caller)
          \<in> acc (FunctionEntry p)
                (enterc (sink_node caller) (key enterc seedc caller)
                   (call_enter gs (CallEdge dst pars args) (sink_store caller)))"
    by (rule CALL[OF e ihc])
  then show ?thesis by (simp add: sink_node_def sink_store_def)
qed

text \<open>\<open>return_closed\<close>: the matched return.  \<open>callee_entry_invariant\<close> forces the
  callee context to \<open>enterc (key caller) (entry_store callee)\<close> and supplies the concrete
  enter store, so \<open>COMB\<close> lands the return combine at the CALLER context \<open>key caller\<close>.\<close>
lemma return_closed:
  assumes callee_val: "callee \<in> valid_ltr gs g S"
    and cof: "caller_of callee = Some caller"
    and res: "sink_node callee = FunctionResult p"
    and comb: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ih_caller: "bnd caller"
    and ih_callee: "bnd callee"
  shows "bnd (Resume caller callee
               (path caller @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
proof -
  have key_eq: "key enterc seedc callee
      = enterc (sink_node caller) (key enterc seedc caller) (entry_store callee)"
    using callee_entry_invariant_keyD[OF callee_val cof] .
  have call_enter: "call_enter_store gs g (sink_node caller) (sink_store caller) (entry_store callee)"
    using callee_entry_invariant_call_enterD[OF callee_val cof] .
  have ih_callee': "sink_store callee
        \<in> acc (FunctionResult p) (enterc (sink_node caller) (key enterc seedc caller) (entry_store callee))"
    using ih_callee key_eq res by simp
  have "combine_collect gs dst (sink_store caller) (sink_store callee)
          \<in> acc cont (key enterc seedc caller)"
    by (rule COMB[OF comb ih_caller ih_callee' call_enter])
  then show ?thesis by (simp add: sink_node_def sink_store_def)
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
  the abstract slots at \<open>v\<close> over all contexts.\<close>
theorem ltr_collect_subset_acc_Union:
  "ltr_collect gs g S v \<subseteq> (\<Union>c. acc v c)"
proof (rule subsetI)
  fix x assume "x \<in> ltr_collect gs g S v"
  then obtain t where t: "t \<in> valid_ltr gs g S" "sink_node t = v" "sink_store t = x"
    by (rule ltr_collect_E)
  have "bnd t" using valid_ltr_subset_gamma_ltr t(1) by (auto simp: gamma_ltr_def)
  then show "x \<in> (\<Union>c. acc v c)" using t(2,3) by auto
qed

text \<open>Context projection: the context-indexed concrete collection is covered by the abstract
  slot at that exact context. \<open>acc\<close> carries no cross-context monotonicity here, so this is
  stated at the exact match \<open>ctx_rep = (=)\<close>; a covering query would need \<open>acc\<close> itself
  monotone in the covering relation, which is a further obligation on this locale, not a
  restatement of this fact.\<close>
theorem activation_collect_subset_acc:
  "activation_collect gs enterc seedc (=) g S v c \<subseteq> acc v c"
proof (rule subsetI)
  fix x assume "x \<in> activation_collect gs enterc seedc (=) g S v c"
  then obtain t where t: "t \<in> valid_ltr gs g S" "sink_node t = v" "key enterc seedc t = c"
    "sink_store t = x"
    by (rule activation_collect_E)
  have "bnd t" using valid_ltr_subset_gamma_ltr t(1) by (auto simp: gamma_ltr_def)
  then show "x \<in> acc v c" using t(2,3,4) by simp
qed

subsection \<open>Matched-return validation\<close>

text \<open>At any reachable return, the callee consumed is the one \<^const>\<open>caller_of\<close> recovers,
  its abstract bound is read at a context DERIVED from the caller, and the result lands at
  the caller context.\<close>
theorem return_uses_matched_callee:
  assumes res: "Resume caller callee p \<in> valid_ltr gs g S"
    and rn: "sink_node callee = FunctionResult pp"
    and comb: "(sink_node caller, CallEdge dst pars args, FunctionEntry pp, cont) \<in> calls g"
  shows "caller_of callee = Some caller
       \<and> sink_store callee
           \<in> acc (FunctionResult pp) (enterc (sink_node caller) (key enterc seedc caller) (entry_store callee))
       \<and> combine_collect gs dst (sink_store caller) (sink_store callee)
           \<in> acc cont (key enterc seedc caller)"
proof -
  from valid_ltr_Resume_fields[OF res refl]
  have cv: "callee \<in> valid_ltr gs g S" and cof: "caller_of callee = Some caller" by auto
  have caller_v: "caller \<in> valid_ltr gs g S" by (rule valid_ltr_caller_valid[OF cv cof])
  have bc: "bnd caller"
    using valid_ltr_subset_gamma_ltr caller_v by (auto simp: gamma_ltr_def)
  have bcl: "bnd callee"
    using valid_ltr_subset_gamma_ltr cv by (auto simp: gamma_ltr_def)
  have key_eq: "key enterc seedc callee
      = enterc (sink_node caller) (key enterc seedc caller) (entry_store callee)"
    using callee_entry_invariant_keyD[OF cv cof] .
  have call_enter: "call_enter_store gs g (sink_node caller) (sink_store caller) (entry_store callee)"
    using callee_entry_invariant_call_enterD[OF cv cof] .
  have mid: "sink_store callee
        \<in> acc (FunctionResult pp) (enterc (sink_node caller) (key enterc seedc caller) (entry_store callee))"
    using bcl key_eq rn by simp
  have res_bound: "combine_collect gs dst (sink_store caller) (sink_store callee)
          \<in> acc cont (key enterc seedc caller)"
    by (rule COMB[OF comb bc mid call_enter])
  show ?thesis using cof mid res_bound by blast
qed

text \<open>Two callers reaching the same continuation \<open>cont\<close> with distinguishable contexts land
  in DISTINCT abstract slots, each composed with its OWN matched callee.\<close>
theorem two_callers_separated:
  assumes r0: "Resume caller0 callee0 p0 \<in> valid_ltr gs g S"
    and r1: "Resume caller1 callee1 p1 \<in> valid_ltr gs g S"
    and rn0: "sink_node callee0 = FunctionResult q0"
    and rn1: "sink_node callee1 = FunctionResult q1"
    and c0: "(sink_node caller0, CallEdge dst0 pars0 args0, FunctionEntry q0, cont) \<in> calls g"
    and c1: "(sink_node caller1, CallEdge dst1 pars1 args1, FunctionEntry q1, cont) \<in> calls g"
    and dist: "key enterc seedc caller0 \<noteq> key enterc seedc caller1"
  shows "combine_collect gs dst0 (sink_store caller0) (sink_store callee0)
           \<in> acc cont (key enterc seedc caller0)
       \<and> combine_collect gs dst1 (sink_store caller1) (sink_store callee1)
           \<in> acc cont (key enterc seedc caller1)
       \<and> key enterc seedc caller0 \<noteq> key enterc seedc caller1"
  using return_uses_matched_callee[OF r0 rn0 c0] return_uses_matched_callee[OF r1 rn1 c1] dist
  by blast

end

subsection \<open>Non-vacuity\<close>

text \<open>The interface is satisfiable for every graph, seed set, routing, and seed context ---
  the top abstraction \<open>acc = (\<lambda>_ _. UNIV)\<close> discharges all four obligations.\<close>
lemma ltr_gamma_UNIV: "ltr_gamma g S (\<lambda>_ _. UNIV) enterc seedc gs"
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
    and call: "\<And>u dst pars args p cont s. (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> B u \<Longrightarrow> call_enter gs (CallEdge dst pars args) s \<in> B (FunctionEntry p)"
    and combine: "\<And>cl dst pars args p cont s t. (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
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
    have "u \<in> G.gamma_ltr" using G.valid_ltr_subset_gamma_ltr u(1) by blast
    then show "x \<in> B v" using u(2,3) by (simp add: G.gamma_ltr_def)
  qed
qed

end

