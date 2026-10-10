theory Backward_Domain
  imports Nonrelational_Reachability Forward_Domain
begin

section \<open>Refining an abstract state against a guard\<close>

text \<open>
  A forward transfer over-approximates what an assignment does; a backward one narrows a
  state against a condition that is known to hold, which is what a branch on \<open>b\<close> learns
  about the stores that pass it. \<open>sound_refinement\<close> is the interface a domain
  supplies for that: inverse operators for arithmetic and comparison (\<open>inv_less\<close>,
  \<open>inv_plus\<close>, ...), each sound in the sense that every concrete pair the operator
  admits before the operation is still admitted after narrowing, from which \<open>afilter\<close>
  and \<open>bfilter\<close> -- the expression- and boolean-level filters -- are derived once with
  their soundness and reductiveness. \<open>mono_refinement\<close> adds the
  monotone operators a domain can provide on top.
  This abstracts the backward-refinement operations Goblint's \<open>BaseInvariant\<close> implements
  concretely for its Base analysis; Goblint has no generic module signature this locale
  is a formalization of.
\<close>

subsection \<open>Backward-analysis locale\<close>

text \<open>
  A semantic intersection preserves every concrete value shared by both
  operands and lies below both. It need not be the lattice infimum: a domain
  may normalize an empty result while its representation order still
  distinguishes several empty elements. Soundness of the filters needs only
  \<open>intersect_sound\<close>. The lower bounds make every refinement step reductive,
  so a state emptied by one step stays empty through the rest, which is what
  lets the executable filter stop at the first empty step
  (\<open>Exec_Backward\<close>). Every domain's intersection has both, so they form one
  contract; \<open>mono_intersection\<close> adds monotonicity as a separate
  strengthening.
\<close>

locale sound_intersection =
  fixes intersect :: "'a::numeric_domain => 'a => 'a"
  assumes intersect_sound[intro]:
    "n \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> n \<in> \<gamma> (intersect a b)"
    and intersect_reductive1[intro]: "intersect a b \<le> a"
    and intersect_reductive2[intro]: "intersect a b \<le> b"

text \<open>
  Monotone intersection is a separate layer for the same reason as in the forward
  interfaces: soundness needs only \<open>sound_intersection\<close>, while the solver's
  least-solution theorem asks \<open>intersect\<close> to preserve the order in both arguments.
\<close>

locale mono_intersection = sound_intersection +
  assumes intersect_mono[intro]:
    "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> intersect a1 b1 \<le> intersect a2 b2"

text \<open>
  The inverse operators work on abstract values alone: given the result an
  operation must have produced, each narrows its operands to values that still
  admit every concrete pair producing it. \<open>sound_inverse_ops\<close> states them and their
  soundness with no state in sight, which is all the derived numeric queries
  (\<open>Backward_Numeric_Queries\<close>) read.
\<close>

locale sound_inverse_ops = sound_intersection intersect
  for intersect :: "'a::numeric_domain => 'a => 'a" +
  fixes
    inv_less  :: "bool => 'a => 'a => 'a * 'a"
    and inv_eq    :: "bool => 'a => 'a => 'a * 'a"
    and inv_plus  :: "'a => 'a => 'a => 'a * 'a"
    and inv_minus :: "'a => 'a => 'a => 'a * 'a"
    and inv_times :: "'a => 'a => 'a => 'a * 'a"
  assumes
      inv_less_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> (n1 < n2) = res
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_less res a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_less res a1 a2))"
    and inv_eq_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> (n1 = n2) = res
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_eq res a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_eq res a1 a2))"
    and inv_plus_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> n1 + n2 \<in> \<gamma> r
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_plus r a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_plus r a1 a2))"
    and inv_minus_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> n1 - n2 \<in> \<gamma> r
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_minus r a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_minus r a1 a2))"
    and inv_times_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> n1 * n2 \<in> \<gamma> r
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_times r a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_times r a1 a2))"
begin

text \<open>
  Projections of the five \<open>inv_*_sound\<close> assumptions above, one membership
  fact per operand instead of the pair conjunction the raw assumption gives.
  These, not the raw assumptions, are the \<open>[intro]\<close> rules: their conclusion
  has a distinctive \<open>fst (inv_* ...)\<close>/\<open>snd (inv_* ...)\<close> head, so a goal of
  exactly that shape picks the matching rule directly, whereas the raw
  conjunction-valued assumption would leave automation to split a conjunction
  goal it did not ask for.
\<close>

lemmas inv_less_sound_fst [intro] = inv_less_sound[THEN conjunct1]
lemmas inv_less_sound_snd [intro] = inv_less_sound[THEN conjunct2]

lemmas inv_eq_sound_fst [intro] = inv_eq_sound[THEN conjunct1]
lemmas inv_eq_sound_snd [intro] = inv_eq_sound[THEN conjunct2]

lemmas inv_plus_sound_fst [intro] = inv_plus_sound[THEN conjunct1]
lemmas inv_plus_sound_snd [intro] = inv_plus_sound[THEN conjunct2]

lemmas inv_minus_sound_fst [intro] = inv_minus_sound[THEN conjunct1]
lemmas inv_minus_sound_snd [intro] = inv_minus_sound[THEN conjunct2]

lemmas inv_times_sound_fst [intro] = inv_times_sound[THEN conjunct1]
lemmas inv_times_sound_snd [intro] = inv_times_sound[THEN conjunct2]

end

text \<open>
  \<open>sound_refinement\<close> takes the inverse operators to pointwise states. With the
  forward operations of @{locale sound_evaluator} and @{locale sound_truth_test}
  it derives the guard filters \<open>afilter\<close> and \<open>bfilter\<close>, whose soundness
  follows by induction. A domain that already interpreted the forward locales
  (through its expression domain) is not asked for their laws again.
\<close>

locale sound_refinement =
  sound_intersection intersect + sound_evaluator gamma_state aval_abs
    + sound_truth_test tobool
    + sound_inverse_ops intersect inv_less inv_eq inv_plus inv_minus inv_times
    for intersect :: "'a::numeric_domain => 'a => 'a"
    and aval_abs :: "exp => 'a abs_state => 'a" ("\<lbrakk>_\<rbrakk>\<^sup>\<sharp>")
    and tobool :: "'a => bool option"
    and inv_less  :: "bool => 'a => 'a => 'a * 'a"
    and inv_eq    :: "bool => 'a => 'a => 'a * 'a"
    and inv_plus  :: "'a => 'a => 'a => 'a * 'a"
    and inv_minus :: "'a => 'a => 'a => 'a * 'a"
    and inv_times :: "'a => 'a => 'a => 'a * 'a"
begin

fun afilter :: "exp => 'a => 'a abs_state => 'a abs_state" where
    "afilter (V x) a d = d(x := intersect a (d x))"
  | "afilter (Plus  e1 e2) a d =
       (let (a1, a2) = inv_plus a (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)
        in afilter e1 a1 (afilter e2 a2 d))"
  | "afilter (Minus e1 e2) a d =
       (let (a1, a2) = inv_minus a (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)
        in afilter e1 a1 (afilter e2 a2 d))"
  | "afilter (Times e1 e2) a d =
       (let (a1, a2) = inv_times a (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)
        in afilter e1 a1 (afilter e2 a2 d))"
  | "afilter _ a d = d"

text \<open>
  \<open>feasible\<close> is the forward half of Goblint's two-phase branch handling, as a
  predicate: evaluate \<open>e\<close> forward and ask whether the abstract value that
  yields leaves the selected polarity possible at all. A bottom value denotes
  no store, and a definite \<open>tobool\<close> answer disagreeing with \<open>pol\<close> rules the
  polarity out; every other case keeps it open. Backward narrowing cannot
  replace this test: a Boolean-valued subexpression in an operand position
  inverts to a target \<open>afilter\<close> has no rule to push through a comparison node,
  so the target is dropped and the state survives unrefined even where no state
  satisfies the condition.

  The leading \<open>is_empty\<close> test is not redundant with the \<open>tobool\<close> one. An
  author's \<open>tobool\<close> is free to answer arbitrarily at its own domain's bottom
  (every answer is vacuously sound there, since \<open>gamma bot = {}\<close>), so it need
  not, and generally does not, agree across a bottom/non-bottom pair
  \<open>d1 \<le> d2\<close> the way \<open>tobool_mono\<close> requires. Answering \<open>is_empty\<close> directly,
  ahead of \<open>tobool\<close>, sidesteps that disagreement instead of relying on it, and
  is what makes \<open>feasible_mono\<close> hold.
\<close>

definition feasible :: "exp => bool => 'a abs_state => bool" where
  "feasible e pol d =
     (\<not> is_empty (\<lbrakk>e\<rbrakk>\<^sup>\<sharp> d) \<and> tobool (\<lbrakk>e\<rbrakk>\<^sup>\<sharp> d) \<noteq> Some (\<not> pol))"

text \<open>
  Every state a concrete store witnesses is feasible for the polarity that
  store takes: \<open>aval_abs_sound\<close> rules out the bottom case and \<open>tobool_sound\<close>
  the disagreeing-answer case. This is what makes the gate's \<open>bot\<close> outcome
  sound wherever it fires -- it fires only when no represented store exists.
\<close>

lemma feasible_of_concrete [intro]:
  assumes "s \<in> \<gamma> d" and "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = pol"
  shows "feasible e pol d"
  unfolding feasible_def using assms is_empty_correct tobool_sound by blast

text \<open>
  \<open>bfilter\<close> narrows a state under an assumed truth value of \<open>e\<close>: \<open>bfilter e
  True\<close> is \<open>assume e\<close>, \<open>bfilter e False\<close> is \<open>assume-not e\<close>. \<open>Not\<close>/\<open>And\<close>/\<open>Or\<close>
  distribute structurally (De Morgan, over \<open>\<squnion>\<close> for the disjunctive branch);
  \<open>Less\<close>/\<open>Eq\<close> go straight through \<open>inv_less\<close>/\<open>inv_eq\<close> on their two operands.
  Every other constructor -- \<open>N\<close>, \<open>V\<close>, \<open>Plus\<close>, \<open>Minus\<close>, \<open>Times\<close> -- has no
  Boolean-shaped narrowing operator of its own, so the fallback case reduces
  truthiness to the one comparison every domain already inverts: \<open>truthy
  (\<lbrakk>e\<rbrakk>\<^sub>e s) = res\<close> iff \<open>(\<lbrakk>e\<rbrakk>\<^sub>e s = 0) = (\<not> res)\<close>, so \<open>inv_eq (\<not> res)\<close>
  against the abstract constant \<open>0\<close> narrows \<open>e\<close>'s own target value, and
  \<open>afilter\<close> propagates that target through \<open>e\<close>'s structure. This reuses
  \<open>inv_eq\<close>/\<open>afilter\<close> rather than adding a new domain-author operator.

  The two disjunctive cases -- \<open>Or _ _ True\<close> and \<open>And _ _ False\<close> -- gate each
  side on \<open>feasible\<close> before joining, matching Goblint's \<open>inv_exp\<close>, which
  refines the arms of a disjunction separately and drops one whose refinement
  contradicts. Without the gate, a side no state satisfies still contributes
  its own unrefined incoming state and the join discards what the other side
  established: the empty target such a side inverts to is dropped wherever
  \<open>afilter\<close> has no rule for the node carrying it, so the narrowing that would
  have signalled the contradiction never happens. \<open>bot\<close> is the unit of \<open>\<squnion>\<close>,
  so gating an infeasible side removes it from the join exactly.

  \<open>feasible\<close> is only a necessary forward gate, though: a side it approves can
  still have its own \<open>bfilter\<close> recursion discover a stronger, backward-only
  contradiction, landing on a witness-bottom state (@{const is_empty_state})
  that need not be the literal pointwise \<open>bot\<close> -- e.g. empty at the one
  location the side's own condition constrains, but still carrying whatever
  \<open>d\<close> already held everywhere else. Joining that raw state \<^emph>\<open>pointwise\<close>
  then contributes those other, unrefined locations to the join exactly as if
  the side were live, silently discarding what the other side established
  there. Canonicalizing each gated side before the join (collapsing a
  witness-bottom side to the literal \<open>bot\<close>, the unit of \<open>\<squnion>\<close>) would close this,
  but @{const is_empty_state} has no code equation over an infinite \<open>vname\<close>
  domain, and embedding it inside \<open>bfilter\<close>'s own primitive-recursive
  equations would make the whole function -- every constructor, not only
  \<open>And\<close>/\<open>Or\<close> -- lose code-generatability with it. \<open>bfilter\<close> therefore stays
  exactly this pointwise join, and the correction lives one level up, in
  \<open>bfilter_lifted\<close>, which does not need to code-generate.
\<close>

fun bfilter :: "exp => bool => 'a abs_state => 'a abs_state" where
    "bfilter (Less e1 e2) res d =
       (let (a1, a2) = inv_less res (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)
        in afilter e1 a1 (afilter e2 a2 d))"
  | "bfilter (GreaterEq e1 e2) res d =
       (let (a1, a2) = inv_less (\<not> res) (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)
        in afilter e1 a1 (afilter e2 a2 d))"
  | "bfilter (Greater e1 e2) res d =
       (let (a1, a2) = inv_less res (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)
        in afilter e2 a1 (afilter e1 a2 d))"
  | "bfilter (LessEq e1 e2) res d =
       (let (a1, a2) = inv_less (\<not> res) (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)
        in afilter e2 a1 (afilter e1 a2 d))"
  | "bfilter (Not b) res d = bfilter b (\<not> res) d"
  | "bfilter (And b1 b2) True  d = bfilter b1 True  (bfilter b2 True  d)"
  | "bfilter (And b1 b2) False d =
       (if feasible b1 False d then bfilter b1 False d else bot)
       \<squnion> (if feasible b2 False d then bfilter b2 False d else bot)"
  | "bfilter (Or  b1 b2) True  d =
       (if feasible b1 True d then bfilter b1 True d else bot)
       \<squnion> (if feasible b2 True d then bfilter b2 True d else bot)"
  | "bfilter (Or  b1 b2) False d = bfilter b1 False (bfilter b2 False d)"
  | "bfilter (Eq  e1 e2) res  d =
       (let (a1, a2) = inv_eq res (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)
        in afilter e1 a1 (afilter e2 a2 d))"
  | "bfilter (NotEq  e1 e2) res  d =
       (let (a1, a2) = inv_eq (\<not> res) (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)
        in afilter e1 a1 (afilter e2 a2 d))"
  | "bfilter e res d =
       (let (a1, a2) = inv_eq (\<not> res) (\<lbrakk>e\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>N 0\<rbrakk>\<^sup>\<sharp> d)
        in afilter e a1 d)"

text \<open>
  The state-level fact behind \<open>afilter\<close>'s \<open>V\<close> case: narrowing one location
  by \<open>intersect\<close> keeps every location represented, the narrowed one because
  \<open>intersect_sound\<close> says so and every other because it is untouched. Named
  once here so \<open>afilter_sound\<close>'s \<open>V\<close> case cites it instead of unfolding
  \<open>gamma_state_def\<close> and case-splitting on \<open>y = x\<close> inline.
\<close>

lemma gamma_state_update_intersect [intro]:
  assumes "s \<in> \<gamma> d" and "s x \<in> \<gamma> a"
  shows "s \<in> \<gamma> (d(x := intersect a (d x)))"
  using assms by (simp add: gamma_stateD gamma_stateI intersect_sound)

lemma afilter_sound [intro]:
  assumes "s \<in> \<gamma> d" "\<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> a"
  shows "s \<in> \<gamma> (afilter e a d)"
using assms proof (induction e arbitrary: a d)
  case (V x)
  then show ?case
    unfolding afilter.simps aval.simps by (rule gamma_state_update_intersect)
next
  case (Plus e1 e2)
  have e1a: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)" and e2a: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)"
    using aval_abs_sound[OF Plus.prems(1)] by simp_all
  have asum: "\<lbrakk>e1\<rbrakk>\<^sub>e s + \<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> a" using Plus.prems(2) by simp
  show ?case
    unfolding afilter.simps Let_def case_prod_beta
    using e1a e2a asum Plus.prems(1)
    by (blast intro: Plus.IH)
next
  case (Minus e1 e2)
  have e1a: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)" and e2a: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)"
    using aval_abs_sound[OF Minus.prems(1)] by simp_all
  have adiff: "\<lbrakk>e1\<rbrakk>\<^sub>e s - \<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> a" using Minus.prems(2) by simp
  show ?case
    unfolding afilter.simps Let_def case_prod_beta
    using e1a e2a adiff Minus.prems(1)
    by (blast intro: Minus.IH)
next
  case (Times e1 e2)
  have e1a: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)" and e2a: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)"
    using aval_abs_sound[OF Times.prems(1)] by simp_all
  have aprod: "\<lbrakk>e1\<rbrakk>\<^sub>e s * \<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> a" using Times.prems(2) by simp
  show ?case
    unfolding afilter.simps Let_def case_prod_beta
    using e1a e2a aprod Times.prems(1)
    by (blast intro: Times.IH)
qed simp_all

text \<open>
  The two-operand filtering step \<open>Less\<close>/\<open>Eq\<close> each apply once \<open>inv_less\<close>/
  \<open>inv_eq\<close> has narrowed their operand pair: filter the second operand by
  its narrowed target, then the first by its narrowed target against the
  result. Stated generically here, using the completed \<open>afilter_sound\<close>
  rather than an induction hypothesis, so \<open>bfilter_sound\<close>'s own \<open>Less\<close>/\<open>Eq\<close>
  cases apply it directly instead of repeating this chaining.
\<close>

lemma afilter_pair_sound [intro]:
  assumes st: "s \<in> \<gamma> d"
      and fst: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (fst p)"
      and snd: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (snd p)"
  shows "s \<in> \<gamma> (afilter e1 (fst p) (afilter e2 (snd p) d))"
proof -
  have inner: "s \<in> \<gamma> (afilter e2 (snd p) d)" by (rule afilter_sound[OF st snd])
  show ?thesis by (rule afilter_sound[OF inner fst])
qed


text \<open>
  Every constructor without its own Boolean-shaped narrowing operator --
  \<open>N\<close>, \<open>V\<close>, \<open>Plus\<close>, \<open>Minus\<close>, \<open>Times\<close> -- reduces \<open>bfilter\<close>'s target truth
  value to an \<open>inv_eq\<close> narrowing against the abstract constant \<open>0\<close> (see
  \<open>bfilter\<close>'s own comment), then propagates the narrowed target through
  \<open>afilter\<close>. Proved once here, generically in \<open>e\<close>, so the induction below
  cites it instead of repeating the same \<open>inv_eq\<close>/\<open>afilter_sound\<close> chain per
  arithmetic constructor.
\<close>
lemma bfilter_default_sound:
  assumes "s \<in> \<gamma> d" "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = res"
  shows "s \<in> \<gamma> (afilter e (fst (inv_eq (\<not> res) (\<lbrakk>e\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>N 0\<rbrakk>\<^sup>\<sharp> d))) d)"
proof -
  have ea: "\<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e\<rbrakk>\<^sup>\<sharp> d)"
    using aval_abs_sound[OF assms(1)] by simp
  have e0: "\<lbrakk>N 0\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>N 0\<rbrakk>\<^sup>\<sharp> d)"
    by (rule aval_abs_sound[of s d "N 0", OF assms(1)])
  have eq0: "(\<lbrakk>e\<rbrakk>\<^sub>e s = \<lbrakk>N 0\<rbrakk>\<^sub>e s) = (\<not> res)"
    using assms(2) by auto
  have "\<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> (fst (inv_eq (\<not> res) (\<lbrakk>e\<rbrakk>\<^sup>\<sharp> d) (\<lbrakk>N 0\<rbrakk>\<^sup>\<sharp> d)))"
    using inv_eq_sound[OF ea e0 eq0] by simp
  then show ?thesis using afilter_sound[OF assms(1)]
    by simp
qed

text \<open>
  Soundness of a feasibility-gated join, the shape of \<open>bfilter\<close>'s
  \<open>And _ _ False\<close> and \<open>Or _ _ True\<close> cases: a store taking the polarity on
  one side makes that side feasible, so the gate keeps it and the join
  admits the store through it.
\<close>

lemma gated_join_sound:
  fixes f1 f2 :: "'a abs_state"
  assumes st: "s \<in> \<gamma> d"
    and "truthy (\<lbrakk>b1\<rbrakk>\<^sub>e s) = pol \<or> truthy (\<lbrakk>b2\<rbrakk>\<^sub>e s) = pol"
    and f1: "truthy (\<lbrakk>b1\<rbrakk>\<^sub>e s) = pol \<Longrightarrow> s \<in> \<gamma> f1"
    and f2: "truthy (\<lbrakk>b2\<rbrakk>\<^sub>e s) = pol \<Longrightarrow> s \<in> \<gamma> f2"
  shows "s \<in> \<gamma> ((if feasible b1 pol d then f1 else bot)
                \<squnion> (if feasible b2 pol d then f2 else bot))"
  using assms(2)
proof
  assume h: "truthy (\<lbrakk>b1\<rbrakk>\<^sub>e s) = pol"
  have "feasible b1 pol d" by (rule feasible_of_concrete[OF st h])
  with f1[OF h] show ?thesis by (simp add: gamma_state_supI1)
next
  assume h: "truthy (\<lbrakk>b2\<rbrakk>\<^sub>e s) = pol"
  have "feasible b2 pol d" by (rule feasible_of_concrete[OF st h])
  with f2[OF h] show ?thesis by (simp add: gamma_state_supI2)
qed

lemma bfilter_sound [intro]:
  assumes "s \<in> \<gamma> d" "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = res"
  shows "s \<in> \<gamma> (bfilter e res d)"
using assms proof (induction e arbitrary: res d)
  case (Not e)
  have bv': "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = (\<not> res)" using Not.prems(2) by (auto split: if_splits)
  from Not.IH[OF Not.prems(1) bv'] show ?case by simp
next
  case (And e1 e2)
  show ?case
  proof (cases res)
    case True
    have v1: "truthy (\<lbrakk>e1\<rbrakk>\<^sub>e s) = True" and v2: "truthy (\<lbrakk>e2\<rbrakk>\<^sub>e s) = True"
      using And.prems(2) True unfolding truthy_aval_And by simp_all
    show ?thesis
      using And.IH(1)[OF And.IH(2)[OF And.prems(1) v2] v1] by (simp add: True)
  next
    case False
    then have res: "res = False" by simp
    have "truthy (\<lbrakk>e1\<rbrakk>\<^sub>e s) = False \<or> truthy (\<lbrakk>e2\<rbrakk>\<^sub>e s) = False"
      using And.prems(2) res by (auto split: if_splits)
    then show ?thesis
      unfolding res bfilter.simps
      by (rule gated_join_sound[OF And.prems(1) _ And.IH[OF And.prems(1)]])
  qed
next
  case (Or e1 e2)
  show ?case
  proof (cases res)
    case True
    then have res: "res = True" by simp
    have "truthy (\<lbrakk>e1\<rbrakk>\<^sub>e s) = True \<or> truthy (\<lbrakk>e2\<rbrakk>\<^sub>e s) = True"
      using Or.prems(2) res by auto
    then show ?thesis
      unfolding res bfilter.simps
      by (rule gated_join_sound[OF Or.prems(1) _ Or.IH[OF Or.prems(1)]])
  next
    case False
    have v1: "truthy (\<lbrakk>e1\<rbrakk>\<^sub>e s) = False" and v2: "truthy (\<lbrakk>e2\<rbrakk>\<^sub>e s) = False"
      using Or.prems(2) False unfolding truthy_aval_Or by simp_all
    show ?thesis
      using Or.IH(1)[OF Or.IH(2)[OF Or.prems(1) v2] v1] by (simp add: False)
  qed
next
  case (Less e1 e2)
  have e1a: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)" and e2a: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)"
    using aval_abs_sound[OF Less.prems(1)] by simp_all
  have less: "(\<lbrakk>e1\<rbrakk>\<^sub>e s < \<lbrakk>e2\<rbrakk>\<^sub>e s) = res" using Less.prems(2) by (auto split: if_splits)
  show ?case
    unfolding bfilter.simps Let_def case_prod_beta
    by (blast intro: Less.prems(1) inv_less_sound_fst[OF e1a e2a less]
                      inv_less_sound_snd[OF e1a e2a less])
next
  case (GreaterEq e1 e2)
  have e1a: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)" and e2a: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)"
    using aval_abs_sound[OF GreaterEq.prems(1)] by simp_all
  have less: "(\<lbrakk>e1\<rbrakk>\<^sub>e s < \<lbrakk>e2\<rbrakk>\<^sub>e s) = (\<not> res)" using GreaterEq.prems(2) by (auto split: if_splits)
  show ?case
    unfolding bfilter.simps Let_def case_prod_beta
    by (blast intro: GreaterEq.prems(1) inv_less_sound_fst[OF e1a e2a less]
                      inv_less_sound_snd[OF e1a e2a less])
next
  case (Greater e1 e2)
  have e1a: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)" and e2a: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)"
    using aval_abs_sound[OF Greater.prems(1)] by simp_all
  have less: "(\<lbrakk>e2\<rbrakk>\<^sub>e s < \<lbrakk>e1\<rbrakk>\<^sub>e s) = res" using Greater.prems(2) by (auto split: if_splits)
  show ?case
    unfolding bfilter.simps Let_def case_prod_beta
    by (blast intro: Greater.prems(1) inv_less_sound_fst[OF e2a e1a less]
                      inv_less_sound_snd[OF e2a e1a less])
next
  case (LessEq e1 e2)
  have e1a: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)" and e2a: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)"
    using aval_abs_sound[OF LessEq.prems(1)] by simp_all
  have less: "(\<lbrakk>e2\<rbrakk>\<^sub>e s < \<lbrakk>e1\<rbrakk>\<^sub>e s) = (\<not> res)" using LessEq.prems(2) by (auto split: if_splits)
  show ?case
    unfolding bfilter.simps Let_def case_prod_beta
    by (blast intro: LessEq.prems(1) inv_less_sound_fst[OF e2a e1a less]
                      inv_less_sound_snd[OF e2a e1a less])
next
  case (Eq e1 e2)
  have e1a: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)" and e2a: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)"
    using aval_abs_sound[OF Eq.prems(1)] by simp_all
  have eq: "(\<lbrakk>e1\<rbrakk>\<^sub>e s = \<lbrakk>e2\<rbrakk>\<^sub>e s) = res" using Eq.prems(2) by (auto split: if_splits)
  show ?case
    unfolding bfilter.simps Let_def case_prod_beta
    by (blast intro: Eq.prems(1) inv_eq_sound_fst[OF e1a e2a eq] inv_eq_sound_snd[OF e1a e2a eq])

next
  case (NotEq e1 e2)
  have e1a: "\<lbrakk>e1\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e1\<rbrakk>\<^sup>\<sharp> d)" and e2a: "\<lbrakk>e2\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e2\<rbrakk>\<^sup>\<sharp> d)"
    using aval_abs_sound[OF NotEq.prems(1)] by simp_all
  have eq: "(\<lbrakk>e1\<rbrakk>\<^sub>e s = \<lbrakk>e2\<rbrakk>\<^sub>e s) = (\<not> res)" using NotEq.prems(2) by (auto split: if_splits)
  show ?case
    unfolding bfilter.simps Let_def case_prod_beta
    by (blast intro: NotEq.prems(1) inv_eq_sound_fst[OF e1a e2a eq] inv_eq_sound_snd[OF e1a e2a eq])
qed (simp_all only: bfilter.simps Let_def case_prod_beta bfilter_default_sound)

text \<open>
  \<open>branch_lifted\<close> is the Goblint-aligned branch semantics: the forward
  \<open>feasible\<close> gate on the whole condition ahead of \<open>bfilter\<close>, matching
  \<open>Base.branch\<close>'s \<open>eval_rv\<close> / \<open>to_bool\<close> dead-code gate ahead of \<open>invariant\<close>.
  An infeasible condition denotes \<open>Bot\<close> -- no concrete successor, matching
  Goblint's \<open>Deadcode\<close> as an outer control-flow fact rather than a value of the
  domain -- while every other case narrows via \<open>bfilter\<close> and returns
  \<open>Lifted\<close>. \<open>tobool\<close>'s definite answer, when present, is exactly \<open>truthy\<close> of
  every concrete value \<open>aval_abs e d\<close> represents; \<open>truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = pol\<close>
  for a represented \<open>s\<close> then forces that answer to equal \<open>pol\<close>, so the \<open>Bot\<close>
  case below is exercised only when no represented \<open>s\<close> exists at all.

  It is the same gate \<open>bfilter\<close> applies per disjunct inside its two join cases,
  here run on the whole condition -- which is what makes it a control-flow fact
  rather than a narrowing.

  A feasible condition's \<open>bfilter\<close> narrowing can itself still land on a
  witness-bottom store (@{const is_empty_state}, without being the raw
  \<open>Lifted\<close>'s structural \<open>Bot\<close>): \<open>feasible\<close> is only a necessary forward gate,
  and \<open>bfilter\<close>'s backward narrowing may subsequently discover a stronger
  contradiction. \<open>branch_lifted\<close> therefore re-normalizes \<open>bfilter\<close>'s result
  against \<open>is_empty_state\<close> (\<^const>\<open>normalize_lift\<close>), matching Goblint's
  \<open>BaseInvariant\<close> raising \<open>Deadcode\<close> when its own refinement reaches bottom:
  \<open>branch_lifted\<close> is always \<^const>\<open>normalized_lift\<close>
  (\<open>branch_lifted_normalized\<close>), so a caller can rely on structural \<open>Bot\<close>
  alone rather than re-testing \<open>is_empty_state\<close> on a \<open>Lifted\<close> result.
\<close>

text \<open>
  \<open>bfilter_lifted\<close> is not \<open>bfilter\<close>'s wrapper: a wrapper can only test the
  \<^emph>\<open>whole\<close> recursion's final result for emptiness, one collapse after every
  arm has already been joined pointwise, so it cannot undo pollution already
  baked into that pointwise result -- the failure mode documented at
  \<open>bfilter\<close>'s own \<open>And\<close>/\<open>Or\<close> equations. \<open>bfilter_lifted\<close> is instead an
  independent primitive recursion, structurally mirroring \<open>bfilter\<close> one
  constructor at a time, that canonicalizes each \<open>And\<close>/\<open>Or\<close> arm (\<^const>\<open>Bot\<close>
  on an infeasible or witness-bottom side, the join's own identity) \<^emph>\<open>before\<close>
  joining, at the \<open>lifted\<close> level, exactly where \<open>bfilter\<close> itself cannot
  afford to: @{const is_empty_state} has no code equation, so embedding it in
  \<open>bfilter\<close>'s own equations would carry that non-executability to every
  constructor, whereas \<open>bfilter_lifted\<close> is never code-generated. Every atomic
  case (\<open>afilter\<close>'s pointwise update has no pollution to fix) still reduces
  to plain \<open>bfilter\<close>, so the two recursions agree everywhere they overlap and
  cannot silently drift on those shared cases; all Boolean structure --
  \<open>Not\<close>, and both polarities of \<open>And\<close>/\<open>Or\<close> -- is instead interpreted
  recursively in the \<open>lifted\<close> carrier: \<open>Not\<close> just flips polarity and
  recurses, the non-join polarity chains through \<^const>\<open>bind_lift\<close> to
  propagate an arm's \<open>Bot\<close> immediately, and the two join equations are the
  deliberately independent pollution fix.
\<close>

fun bfilter_lifted :: "exp => bool => 'a abs_state => 'a abs_state lifted" where
    "bfilter_lifted (Not b) res d = bfilter_lifted b (\<not> res) d"
  | "bfilter_lifted (And b1 b2) True  d =
       bind (bfilter_lifted b2 True d) (bfilter_lifted b1 True)"
  | "bfilter_lifted (And b1 b2) False d =
       (if feasible b1 False d then bfilter_lifted b1 False d else Bot)
       \<squnion> (if feasible b2 False d then bfilter_lifted b2 False d else Bot)"
  | "bfilter_lifted (Or  b1 b2) True  d =
       (if feasible b1 True d then bfilter_lifted b1 True d else Bot)
       \<squnion> (if feasible b2 True d then bfilter_lifted b2 True d else Bot)"
  | "bfilter_lifted (Or  b1 b2) False d =
       bind (bfilter_lifted b2 False d) (bfilter_lifted b1 False)"
  | "bfilter_lifted (Eq  e1 e2) res  d = normalize_lift is_empty_state (bfilter (Eq e1 e2) res d)"
  | "bfilter_lifted e res d = normalize_lift is_empty_state (bfilter e res d)"

lemma bfilter_lifted_normalized [simp]:
  "normalized_lift is_empty_state (bfilter_lifted e pol d)"
proof (induction e arbitrary: pol d)
  case (And b1 b2)
  then show ?case
    by (cases pol) (auto intro: normalized_lift_bind)
next
  case (Or b1 b2)
  then show ?case
    by (cases pol) (auto intro: normalized_lift_bind)
qed simp_all

text \<open>\<open>gated_join_sound\<close> for \<open>bfilter_lifted\<close>'s join cases, against \<^const>\<open>Bot\<close>.\<close>

lemma gated_join_lifted_sound:
  assumes st: "s \<in> \<gamma> d"
    and "truthy (\<lbrakk>b1\<rbrakk>\<^sub>e s) = pol \<or> truthy (\<lbrakk>b2\<rbrakk>\<^sub>e s) = pol"
    and f1: "truthy (\<lbrakk>b1\<rbrakk>\<^sub>e s) = pol \<Longrightarrow> s \<in> \<gamma>\<^sub>\<bottom> f1"
    and f2: "truthy (\<lbrakk>b2\<rbrakk>\<^sub>e s) = pol \<Longrightarrow> s \<in> \<gamma>\<^sub>\<bottom> f2"
  shows
    "s \<in> \<gamma>\<^sub>\<bottom> ((if feasible b1 pol d then f1 else Bot) \<squnion> (if feasible b2 pol d then f2 else Bot))"
  using assms(2)
proof
  assume h: "truthy (\<lbrakk>b1\<rbrakk>\<^sub>e s) = pol"
  have "feasible b1 pol d" by (rule feasible_of_concrete[OF st h])
  with f1[OF h] show ?thesis by (simp add: gamma_state_lift_supI1)
next
  assume h: "truthy (\<lbrakk>b2\<rbrakk>\<^sub>e s) = pol"
  have "feasible b2 pol d" by (rule feasible_of_concrete[OF st h])
  with f2[OF h] show ?thesis by (simp add: gamma_state_lift_supI2)
qed

lemma bfilter_lifted_sound [intro]:
  assumes "s \<in> \<gamma> d" "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = res"
  shows "s \<in> \<gamma>\<^sub>\<bottom> (bfilter_lifted e res d)"
using assms proof (induction e arbitrary: res d)
  case (Not e)
  have bv': "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = (\<not> res)" using Not.prems(2) by (auto split: if_splits)
  from Not.IH[OF Not.prems(1) bv'] show ?case by simp
next
  case (And e1 e2)
  show ?case
  proof (cases res)
    case True
    have v1: "truthy (\<lbrakk>e1\<rbrakk>\<^sub>e s) = True" and v2: "truthy (\<lbrakk>e2\<rbrakk>\<^sub>e s) = True"
      using And.prems(2) True unfolding truthy_aval_And by simp_all
    have h2: "s \<in> \<gamma>\<^sub>\<bottom> (bfilter_lifted e2 True d)"
      using And.IH(2)[OF And.prems(1) v2] .
    have res_eq: "res = True" using True by simp
    show ?thesis
      unfolding res_eq bfilter_lifted.simps
      using h2 v1 by (blast intro: And.IH(1))
  next
    case False
    have "truthy (\<lbrakk>e1\<rbrakk>\<^sub>e s) = False \<or> truthy (\<lbrakk>e2\<rbrakk>\<^sub>e s) = False"
      using And.prems(2) False by (auto split: if_splits)
    from gated_join_lifted_sound[OF And.prems(1) this And.IH[OF And.prems(1)]] False
    show ?thesis by (simp split del: if_split)
  qed
next
  case (Or e1 e2)
  show ?case
  proof (cases res)
    case True
    have "truthy (\<lbrakk>e1\<rbrakk>\<^sub>e s) = True \<or> truthy (\<lbrakk>e2\<rbrakk>\<^sub>e s) = True"
      using Or.prems(2) True by auto
    from gated_join_lifted_sound[OF Or.prems(1) this Or.IH[OF Or.prems(1)]] True
    show ?thesis by (simp split del: if_split)
  next
    case False
    have v1: "truthy (\<lbrakk>e1\<rbrakk>\<^sub>e s) = False" and v2: "truthy (\<lbrakk>e2\<rbrakk>\<^sub>e s) = False"
      using Or.prems(2) False unfolding truthy_aval_Or by simp_all
    have h2: "s \<in> \<gamma>\<^sub>\<bottom> (bfilter_lifted e2 False d)"
      using Or.IH(2)[OF Or.prems(1) v2] .
    have res_eq: "res = False" using False by simp
    show ?thesis
      unfolding res_eq bfilter_lifted.simps
      using h2 v1 by (blast intro: Or.IH(1))
  qed
qed (simp_all only: bfilter_lifted.simps gamma_state_normalize_lift bfilter_sound)

text \<open>
  \<open>branch_lifted\<close> is \<open>branch\<close>'s reachability wrapper, now routed through
  \<open>bfilter_lifted\<close> rather than raw \<open>bfilter\<close>: the top-level \<open>feasible\<close> gate is
  unchanged (that is \<open>branch\<close>'s own concern, not the \<open>And\<close>/\<open>Or\<close> pollution
  \<open>bfilter_lifted\<close> fixes), but the filtering it gates is the corrected
  recursion, so \<open>branch_lifted\<close> inherits the improved precision without
  restating it.
\<close>

definition branch_lifted :: "exp => bool => 'a abs_state => 'a abs_state lifted" where
  "branch_lifted e pol d = (if feasible e pol d then bfilter_lifted e pol d else Bot)"

lemma branch_lifted_normalized [simp]:
  "normalized_lift is_empty_state (branch_lifted e pol d)"
  unfolding branch_lifted_def by simp

lemma branch_lifted_sound [intro]:
  assumes "s \<in> \<gamma> d" "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = pol"
  shows "s \<in> \<gamma>\<^sub>\<bottom> (branch_lifted e pol d)"
proof -
  have g: "feasible e pol d" by (rule feasible_of_concrete[OF assms])
  have "s \<in> \<gamma>\<^sub>\<bottom> (bfilter_lifted e pol d)" by (rule bfilter_lifted_sound[OF assms])
  with g show ?thesis unfolding branch_lifted_def by simp
qed

text \<open>
  A domain's branch operation has no room for \<open>lifted\<close>: it is one
  plain-state-to-plain-state operation among several, dispatched uniformly by
  the edge-action dispatcher with no \<open>Bot\<close>/\<open>Lifted\<close> case at that layer.
  \<open>branch\<close> is \<open>branch_lifted\<close> collapsed back through \<^const>\<open>collapse_lift\<close>,
  so a domain can use the pollution-fixed recursion while still returning a
  plain \<open>abs_state\<close>: an infeasible or witness-bottom result becomes the
  plain type's own \<open>bot\<close>, exactly the value the branch operation's callers already
  treat as a dead program point. This replaces the old feasible-gated-raw-
  \<open>bfilter\<close> \<open>branch\<close>: that definition is strictly less precise on \<open>And\<close>/
  \<open>Or\<close> conditions (the join-arm-pollution \<open>bfilter\<close>'s own comment
  documents), and this project keeps exactly one public plain-state branch
  operation rather than two of different precision.
\<close>

definition branch :: "exp => bool => 'a abs_state => 'a abs_state" where
  "branch e pol d = collapse_lift (branch_lifted e pol d)"

lemma branch_sound [intro]:
  assumes "s \<in> \<gamma> d" "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = pol"
  shows "s \<in> \<gamma> (branch e pol d)"
  unfolding branch_def
  by (rule gamma_collapse_lift[where gam = gamma_state,
        OF branch_lifted_sound[OF assms] gamma_state_bot])

text \<open>
  \<open>branch\<close> and \<open>branch_lifted\<close> denote the same concrete stores: \<open>branch\<close>
  only adapts the carrier to the plain-state shape a domain's branch operation needs,
  it does not lose precision relative to \<open>branch_lifted\<close>. Left bare rather
  than \<open>[simp]\<close>: its right-hand side is a strictly more complex normal
  form than its left, so declaring it a default rewrite would silently
  block every proof that reasons about \<open>branch\<close> directly (\<open>branch_sound\<close>
  among them) -- cite it explicitly where the lifted view is actually
  needed.
\<close>

end


subsection \<open>Conservative inverse operator\<close>

text \<open>
  A domain too coarse to invert an operator (e.g. sign, which cannot narrow
  either operand of a plus/minus/times from its result) instantiates that
  inverse with this shared no-op: both operands pass through unchanged. The
  first argument is the known result or truth value, so the same no-op serves
  the arithmetic inverses and the comparison inverses. Its soundness
  obligation unfolds to the operands' own membership, so each instance
  discharges it with \<open>inv_conservative_def\<close>.
\<close>

definition inv_conservative :: "'r => 'a => 'a => 'a * 'a" where
  "inv_conservative r a1 a2 = (a1, a2)"

end
