theory LTR_Abstract
  imports LTR_Collect
begin

section \<open>A correlation-preserving abstract interface for valid_ltr\<close>

text \<open>
  The smallest domain-free proof interface through which an abstract over-approximation soundly
  covers the stack-faithful semantics \<^const>\<open>valid_ltr\<close>.  The abstract object is a
  context-indexed concretization

  \<^item> \<open>acc :: pp \<Rightarrow> 'c \<Rightarrow> store set\<close>

  --- the set of stores the analysis admits at program point \<open>v\<close> in abstract context \<open>c\<close>.  This
  is the skeleton every concrete carrier in the development instantiates: the  activation backbone's
  \<open>\<lbrakk>sg (Inl (v, c))\<rbrakk>\<close> and the flow-insensitive-globals reader are both an \<open>acc v c\<close>.  No
  \<open>sound_domain\<close>, \<open>abs_state\<close>, solver, or DG dependency appears here.

  The interface fixes four closure obligations (a root seed, an intra edge, a call routing, and a
  return combine) and proves that every valid trace's sink store lands in its own activation slot.
  The load-bearing clause is \<open>COMB\<close>: the callee is read at context \<open>enterc c1 es\<close> --- the caller
  context \<open>c1\<close> routed through the callee's own bound entry store --- so a return can only compose
  the callee whose context descends from the caller it resumes.  The correlation is not an extra
  parameter: \<open>callee_entry_invariant\<close> makes \<open>enterc c1 es\<close> a theorem of \<^const>\<open>valid_ltr\<close>,
  so a proof-level activation record or an explicit stored continuation is unnecessary.  This is
  Candidate A (an abstract continuation) collapsed to its functional core: the continuation of an
  activation is its context slot, and the callee is bound to it by the derivable law rather than by
  storing an unbounded trace.

  The abstract context type \<open>'c\<close> is arbitrary; \<^const>\<open>key\<close> may quotient distinct activations to
  the same context.  Nothing here claims a key is an exact activation identity or that a single
  context slot preserves all activation correlation --- only that each valid trace lands in some
  slot, matched at return.
\<close>

subsection \<open>The abstract interface\<close>

locale ltr_gamma =
  fixes g :: cfg and S :: "store set"
    and acc :: "pp \<Rightarrow> 'c \<Rightarrow> store set"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c"
    and seedc :: 'c
  assumes ROOT: "\<And>s. s \<in> S \<Longrightarrow> s \<in> acc (cfg_entry g) seedc"
    and EDGE: "\<And>u a v c s s'. (u, a, v) \<in> edges g \<Longrightarrow> \<not> is_enter_action a
        \<Longrightarrow> s \<in> acc u c \<Longrightarrow> edge_step a s = Some s' \<Longrightarrow> s' \<in> acc v c"
    and SEED: "\<And>u v c s s' xs es. (u, EA_Enter xs es, v) \<in> edges g \<Longrightarrow> s \<in> acc u c
        \<Longrightarrow> edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow> s' \<in> acc v (enterc c s')"
    and COMB: "\<And>cl ex v dst c1 s t es. (cl, ex, v, dst) \<in> combines g
        \<Longrightarrow> s \<in> acc cl c1 \<Longrightarrow> t \<in> acc ex (enterc c1 es)
        \<Longrightarrow> call_enter_store g cl s es
        \<Longrightarrow> combine_collect dst s t \<in> acc v c1"
begin

text \<open>\<open>bnd u\<close>: the sink store of \<open>u\<close> is admitted at \<open>u\<close>'s own node and activation context.\<close>
abbreviation bnd :: "ltr \<Rightarrow> bool" where
  "bnd u \<equiv> sink_store u \<in> acc (sink_node u) (key enterc seedc u)"

definition gamma_ltr :: "ltr set" where
  "gamma_ltr = {t. bnd t}"

subsection \<open>Closure under the four ltr_F clauses\<close>

text \<open>\<open>ROOT_CLOSED\<close>: the main activation's seed store is admitted at the entry seed context.\<close>
lemma root_closed: "s \<in> S \<Longrightarrow> bnd (Root [(cfg_entry g, s)])"
  using ROOT by (simp add: sink_node_def sink_store_def)

text \<open>\<open>INTRA_CLOSED\<close>: an intra edge preserves the context (\<^const>\<open>key\<close> is unchanged by
  \<^const>\<open>extend\<close> on a non-empty path) and covers the concrete step through \<open>EDGE\<close>.\<close>
lemma intra_closed:
  assumes e: "(sink_node t, a, v) \<in> edges g" and ne: "\<not> is_enter_action a"
    and st: "edge_step a (sink_store t) = Some s'" and pne: "path t \<noteq> []" and iht: "bnd t"
  shows "bnd (extend t (v, s'))"
proof -
  have "s' \<in> acc v (key enterc seedc t)"
    by (rule EDGE[OF e ne iht st])
  then show ?thesis using pne by (simp add: key_extend_nonempty)
qed

text \<open>\<open>CALL_CLOSED\<close>: the entered store is admitted in the callee slot at the routed callee
  context \<open>enterc (key caller) se\<close> --- exactly \<^const>\<open>key\<close> of the new \<^const>\<open>Call\<close>.\<close>
lemma call_closed:
  assumes e: "(sink_node caller, EA_Enter xs es, fe) \<in> edges g"
    and st: "edge_step (EA_Enter xs es) (sink_store caller) = Some se"
    and ihc: "bnd caller"
  shows "bnd (Call caller [(fe, se)])"
proof -
  have "se \<in> acc fe (enterc (key enterc seedc caller) se)"
    by (rule SEED[OF e ihc st])
  then show ?thesis by (simp add: sink_node_def sink_store_def)
qed

text \<open>\<open>RETURN_CLOSED\<close>: the matched return.  The premise consumes the callee correlated with the
  caller: \<open>callee_entry_invariant\<close> forces the callee context to \<open>enterc (key caller)
  (entry_store callee)\<close> and supplies the concrete enter store, so \<open>COMB\<close> lands the return combine
  at the CALLER context \<open>key caller\<close>.  No re-rooting and no arbitrary callee context.\<close>
lemma return_closed:
  assumes callee_val: "callee \<in> valid_ltr g S"
    and cof: "caller_of callee = Some caller"
    and comb: "(sink_node caller, sink_node callee, v, dst) \<in> combines g"
    and ih_caller: "bnd caller"
    and ih_callee: "bnd callee"
  shows "bnd (Resume caller callee
               (path caller @ [(v, combine_collect dst (sink_store caller) (sink_store callee))]))"
proof -
  have inst: "key enterc seedc callee = enterc (key enterc seedc caller) (entry_store callee)
              \<and> call_enter_store g (sink_node caller) (sink_store caller) (entry_store callee)"
    using callee_entry_invariant[OF callee_val, THEN bspec, OF callers_refl, rule_format, OF cof] .
  have ih_callee': "sink_store callee
        \<in> acc (sink_node callee) (enterc (key enterc seedc caller) (entry_store callee))"
    using ih_callee inst[THEN conjunct1] by simp
  have "combine_collect dst (sink_store caller) (sink_store callee)
          \<in> acc v (key enterc seedc caller)"
    by (rule COMB[OF comb ih_caller ih_callee' inst[THEN conjunct2]])
  then show ?thesis by (simp add: sink_node_def sink_store_def)
qed

subsection \<open>The generic soundness theorem\<close>

text \<open>The bound holds along the whole caller chain, by \<^const>\<open>valid_ltr\<close> rule induction feeding the
  four closure lemmas.  The chain, not a per-node statement, is what the \<open>ret\<close> case needs: it
  recovers its caller structurally, and the caller lies in the callee's chain --- the matched
  caller bound is therefore already available from the callee hypothesis.\<close>
lemma gamma_chain:
  "t \<in> valid_ltr g S \<Longrightarrow> \<forall>u \<in> callers t. bnd u"
proof (induction rule: valid_ltr.induct)
  case (init s)
  show ?case using root_closed[OF init] by (simp add: callers_Root)
next
  case (intra t a v s')
  show ?case
  proof
    fix u assume "u \<in> callers (extend t (v, s'))"
    then have "u = extend t (v, s') \<or> u \<in> callers t"
      using callers_extend_subset by blast
    then show "bnd u"
    proof
      assume u: "u = extend t (v, s')"
      have pt: "path t \<noteq> []" using intra.hyps(1) valid_ltr_path_nonempty by blast
      have iht: "bnd t" using intra.IH callers_refl by blast
      show ?thesis unfolding u
        by (rule intra_closed[OF intra.hyps(2,3) intra.hyps(4) pt iht])
    next
      assume "u \<in> callers t"
      then show ?thesis using intra.IH by blast
    qed
  qed
next
  case (call caller xs es fe ex ret dst se)
  show ?case
  proof
    fix u assume "u \<in> callers (Call caller [(fe, se)])"
    then have "u = Call caller [(fe, se)] \<or> u \<in> callers caller"
      by (simp add: callers_Call)
    then show "bnd u"
    proof
      assume u: "u = Call caller [(fe, se)]"
      have ihc: "bnd caller" using call.IH callers_refl by blast
      show ?thesis unfolding u
        by (rule call_closed[OF call.hyps(2) call.hyps(4) ihc])
    next
      assume "u \<in> callers caller"
      then show ?thesis using call.IH by blast
    qed
  qed
next
  case (ret callee caller v dst r)
  show ?case
  proof
    fix u assume "u \<in> callers (Resume caller callee (path caller @ [(v, r)]))"
    then have "u = Resume caller callee (path caller @ [(v, r)]) \<or> u \<in> callers callee"
      using callers_Resume_subset[OF ret.hyps(2)] by blast
    then show "bnd u"
    proof
      assume u: "u = Resume caller callee (path caller @ [(v, r)])"
      have ih_caller: "bnd caller"
        using ret.IH ret.hyps(2) callers_caller_subset callers_refl by blast
      have ih_callee: "bnd callee" using ret.IH callers_refl by blast
      show ?thesis unfolding u ret.hyps(4)
        by (rule return_closed[OF ret.hyps(1,2,3) ih_caller ih_callee])
    next
      assume "u \<in> callers callee"
      then show ?thesis using ret.IH by blast
    qed
  qed
qed

text \<open>Every valid trace's sink lies in its own activation slot: \<^const>\<open>valid_ltr\<close> is soundly
  over-approximated by \<open>gamma_ltr\<close>.\<close>
theorem valid_ltr_subset_gamma_ltr: "valid_ltr g S \<subseteq> gamma_ltr"
proof
  fix t assume "t \<in> valid_ltr g S"
  then have "\<forall>u \<in> callers t. bnd u" by (rule gamma_chain)
  then have "bnd t" using callers_refl by blast
  then show "t \<in> gamma_ltr" by (simp add: gamma_ltr_def)
qed

text \<open>The same statement in fixed-point form, via  \<open>valid_ltr_eq_lfp\<close>: the least fixed point of
  \<^const>\<open>ltr_F\<close> is covered by the abstract interface.\<close>
corollary lfp_ltr_F_subset_gamma_ltr: "lfp (ltr_F g S) \<subseteq> gamma_ltr"
  using valid_ltr_subset_gamma_ltr by (simp add: valid_ltr_eq_lfp)

subsection \<open>Matched-return validation\<close>

text \<open>At any reachable return, the callee consumed is the one \<^const>\<open>caller_of\<close> recovers, its
  abstract bound is read at a context DERIVED from the caller (\<open>enterc (key caller)
  (entry_store callee)\<close>), and the result lands at the caller context.  The object that connects
  the callee to the caller continuation is precisely that derived callee context --- not a choice
  over all reachable callee exits.\<close>
theorem return_uses_matched_callee:
  assumes res: "Resume caller callee p \<in> valid_ltr g S"
    and comb: "(sink_node caller, sink_node callee, v, dst) \<in> combines g"
  shows "caller_of callee = Some caller
       \<and> sink_store callee
           \<in> acc (sink_node callee) (enterc (key enterc seedc caller) (entry_store callee))
       \<and> combine_collect dst (sink_store caller) (sink_store callee)
           \<in> acc v (key enterc seedc caller)"
proof -
  from valid_ltr_Resume_fields[OF res refl]
  have cv: "callee \<in> valid_ltr g S" and cof: "caller_of callee = Some caller" by auto
  have caller_v: "caller \<in> valid_ltr g S" by (rule valid_ltr_caller_valid[OF cv cof])
  have bc: "bnd caller"
    using valid_ltr_subset_gamma_ltr caller_v by (auto simp: gamma_ltr_def)
  have bcl: "bnd callee"
    using valid_ltr_subset_gamma_ltr cv by (auto simp: gamma_ltr_def)
  have inst: "key enterc seedc callee = enterc (key enterc seedc caller) (entry_store callee)
              \<and> call_enter_store g (sink_node caller) (sink_store caller) (entry_store callee)"
    using callee_entry_invariant[OF cv, THEN bspec, OF callers_refl, rule_format, OF cof] .
  have mid: "sink_store callee
        \<in> acc (sink_node callee) (enterc (key enterc seedc caller) (entry_store callee))"
    using bcl inst[THEN conjunct1] by simp
  have res_bound: "combine_collect dst (sink_store caller) (sink_store callee)
          \<in> acc v (key enterc seedc caller)"
    by (rule COMB[OF comb bc mid inst[THEN conjunct2]])
  show ?thesis using cof mid res_bound by blast
qed

text \<open>Two callers reaching the same return node \<open>v\<close> with distinguishable contexts land in
  DISTINCT abstract slots, each composed with its OWN matched callee --- the return proof never
  ranges over the product of all callers and all callee exits.\<close>
theorem two_callers_separated:
  assumes r0: "Resume caller0 callee0 p0 \<in> valid_ltr g S"
    and r1: "Resume caller1 callee1 p1 \<in> valid_ltr g S"
    and c0: "(sink_node caller0, sink_node callee0, v, dst0) \<in> combines g"
    and c1: "(sink_node caller1, sink_node callee1, v, dst1) \<in> combines g"
    and dist: "key enterc seedc caller0 \<noteq> key enterc seedc caller1"
  shows "combine_collect dst0 (sink_store caller0) (sink_store callee0)
           \<in> acc v (key enterc seedc caller0)
       \<and> combine_collect dst1 (sink_store caller1) (sink_store callee1)
           \<in> acc v (key enterc seedc caller1)
       \<and> key enterc seedc caller0 \<noteq> key enterc seedc caller1"
  using return_uses_matched_callee[OF r0 c0] return_uses_matched_callee[OF r1 c1] dist
  by blast

end

subsection \<open>Non-vacuity\<close>

text \<open>The interface is satisfiable for every graph, seed set, routing, and seed context --- the top
  abstraction \<open>acc = (\<lambda>_ _. UNIV)\<close> discharges all four obligations.  This rules out a vacuous
  locale; a precise instantiation is a downstream (domain) concern, not part of this interface.\<close>
lemma ltr_gamma_UNIV: "ltr_gamma g S (\<lambda>_ _. UNIV) enterc seedc"
  by unfold_locales auto

end
