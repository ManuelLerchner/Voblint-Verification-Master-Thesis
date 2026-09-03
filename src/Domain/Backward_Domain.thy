theory Backward_Domain
  imports Nonrelational_Reachability "Voblint_VIMP.VIMP_Expr"
begin

section \<open>Refining an abstract state against a guard\<close>

text \<open>
  A forward transfer over-approximates what an assignment does; a backward one narrows a
  state against a condition that is known to hold, which is what a branch on \<open>b\<close> learns
  about the stores that pass it. \<open>backward_domain\<close> is the interface a domain
  supplies for that: inverse operators for arithmetic and comparison (\<open>inv_less\<close>,
  \<open>inv_plus\<close>, ...), each sound in the sense that every concrete pair the operator
  admits before the operation is still admitted after narrowing, from which \<open>afilter\<close>
  and \<open>bfilter\<close> -- the expression- and boolean-level filters -- are derived once with
  their soundness and monotonicity. \<open>backward_domain_refined\<close> adds the reductive
  and monotone inverse operators a domain with a conservative inverse can provide.
  This abstracts the backward-refinement operations Goblint's \<open>BaseInvariant\<close> implements
  concretely for its Base analysis; Goblint has no generic module signature this locale
  is a formalization of.
\<close>

subsection \<open>Backward-analysis locale\<close>

text \<open>
  A semantic intersection preserves every concrete value shared by both
  operands. It need not be the lattice infimum: a domain may normalize an
  empty result while its representation order still distinguishes several
  empty elements. This locale records the preservation obligation;
  \<open>backward_domain_refined\<close> adds the reductiveness and monotonicity needed
  by solver-facing filters.
\<close>


locale semantic_intersection =
  fixes intersect :: "'a::sound_domain => 'a => 'a"
  assumes intersect_sound[intro]:
    "n \<in> gamma a \<Longrightarrow> n \<in> gamma b \<Longrightarrow> n \<in> gamma (intersect a b)"

text \<open>
  Extends @{class sound_domain} with the infrastructure for backward
  (inverse) evaluation of guards and arithmetic expressions. Per-domain:
  provide a @{locale semantic_intersection} instance, aval_abs, and inv_*
  operators; the generic afilter / bfilter and their soundness theorems
  follow by induction.
\<close>

locale backward_domain =
  semantic_intersection intersect
    for intersect :: "'a::sound_domain => 'a => 'a" +
  fixes
    aval_abs  :: "exp => 'a abs_state => 'a"
    and tobool :: "'a => bool option"
    and inv_less  :: "bool => 'a => 'a => 'a * 'a"
    and inv_eq    :: "bool => 'a => 'a => 'a * 'a"
    and inv_plus  :: "'a => 'a => 'a => 'a * 'a"
    and inv_minus :: "'a => 'a => 'a => 'a * 'a"
    and inv_times :: "'a => 'a => 'a => 'a * 'a"
  assumes
      aval_abs_sound[intro]:
      "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> aval e s \<in> gamma (aval_abs e \<sigma>)"
  and inv_less_sound:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> (n1 < n2) = res
       \<Longrightarrow> n1 \<in> gamma (fst (inv_less res a1 a2)) \<and> n2 \<in> gamma (snd (inv_less res a1 a2))"
  and inv_eq_sound:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> (n1 = n2) = res
       \<Longrightarrow> n1 \<in> gamma (fst (inv_eq res a1 a2)) \<and> n2 \<in> gamma (snd (inv_eq res a1 a2))"
  and inv_plus_sound:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> n1 + n2 \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_plus r a1 a2)) \<and> n2 \<in> gamma (snd (inv_plus r a1 a2))"
  and inv_minus_sound:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> n1 - n2 \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_minus r a1 a2)) \<and> n2 \<in> gamma (snd (inv_minus r a1 a2))"
  and inv_times_sound:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> n1 * n2 \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_times r a1 a2)) \<and> n2 \<in> gamma (snd (inv_times r a1 a2))"
  and tobool_sound:
      "tobool p = Some b \<Longrightarrow> i \<in> gamma p \<Longrightarrow> truthy i = b"
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

fun afilter :: "exp => 'a => 'a abs_state => 'a abs_state" where
    "afilter (V x) a \<sigma> = \<sigma>(x := intersect a (\<sigma> x))"
  | "afilter (Plus  e1 e2) a \<sigma> =
       (let (a1, a2) = inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)
        in afilter e1 a1 (afilter e2 a2 \<sigma>))"
  | "afilter (Minus e1 e2) a \<sigma> =
       (let (a1, a2) = inv_minus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)
        in afilter e1 a1 (afilter e2 a2 \<sigma>))"
  | "afilter (Times e1 e2) a \<sigma> =
       (let (a1, a2) = inv_times a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)
        in afilter e1 a1 (afilter e2 a2 \<sigma>))"
  | "afilter _ a \<sigma> = \<sigma>"

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
  \<open>\<sigma>1 \<le> \<sigma>2\<close> the way \<open>tobool_mono\<close> requires. Answering \<open>is_empty\<close> directly,
  ahead of \<open>tobool\<close>, sidesteps that disagreement instead of relying on it, and
  is what makes \<open>feasible_mono\<close> hold.
\<close>

definition feasible :: "exp => bool => 'a abs_state => bool" where
  "feasible e pol \<sigma> =
     (\<not> is_empty (aval_abs e \<sigma>) \<and> tobool (aval_abs e \<sigma>) \<noteq> Some (\<not> pol))"

text \<open>
  Every state a concrete store witnesses is feasible for the polarity that
  store takes: \<open>aval_abs_sound\<close> rules out the bottom case and \<open>tobool_sound\<close>
  the disagreeing-answer case. This is what makes the gate's \<open>bot\<close> outcome
  sound wherever it fires -- it fires only when no represented store exists.
\<close>

lemma feasible_of_concrete [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and "truthy (aval e s) = pol"
  shows "feasible e pol \<sigma>"
  unfolding feasible_def using assms is_empty_correct tobool_sound by blast
 
text \<open>
  \<open>bfilter\<close> narrows a state under an assumed truth value of \<open>e\<close>: \<open>bfilter e
  True\<close> is \<open>assume e\<close>, \<open>bfilter e False\<close> is \<open>assume-not e\<close>. \<open>Not\<close>/\<open>And\<close>/\<open>Or\<close>
  distribute structurally (De Morgan, over \<open>\<squnion>\<close> for the disjunctive branch);
  \<open>Less\<close>/\<open>Eq\<close> go straight through \<open>inv_less\<close>/\<open>inv_eq\<close> on their two operands.
  Every other constructor -- \<open>N\<close>, \<open>V\<close>, \<open>Plus\<close>, \<open>Minus\<close>, \<open>Times\<close> -- has no
  Boolean-shaped narrowing operator of its own, so the fallback case reduces
  truthiness to the one comparison every domain already inverts: \<open>truthy
  (aval e s) = res\<close> iff \<open>(aval e s = 0) = (\<not> res)\<close>, so \<open>inv_eq (\<not> res)\<close>
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
  \<open>\<sigma>\<close> already held everywhere else. Joining that raw state \<^emph>\<open>pointwise\<close>
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
    "bfilter (Less e1 e2) res \<sigma> =
       (let (a1, a2) = inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)
        in afilter e1 a1 (afilter e2 a2 \<sigma>))"
  | "bfilter (Not b) res \<sigma> = bfilter b (\<not> res) \<sigma>"
  | "bfilter (And b1 b2) True  \<sigma> = bfilter b1 True  (bfilter b2 True  \<sigma>)"
  | "bfilter (And b1 b2) False \<sigma> =
       (if feasible b1 False \<sigma> then bfilter b1 False \<sigma> else bot)
       \<squnion> (if feasible b2 False \<sigma> then bfilter b2 False \<sigma> else bot)"
  | "bfilter (Or  b1 b2) True  \<sigma> =
       (if feasible b1 True \<sigma> then bfilter b1 True \<sigma> else bot)
       \<squnion> (if feasible b2 True \<sigma> then bfilter b2 True \<sigma> else bot)"
  | "bfilter (Or  b1 b2) False \<sigma> = bfilter b1 False (bfilter b2 False \<sigma>)"
  | "bfilter (Eq  e1 e2) res  \<sigma> =
       (let (a1, a2) = inv_eq res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)
        in afilter e1 a1 (afilter e2 a2 \<sigma>))"
  | "bfilter e res \<sigma> =
       (let (a1, a2) = inv_eq (\<not> res) (aval_abs e \<sigma>) (aval_abs (N 0) \<sigma>)
        in afilter e a1 \<sigma>)"

text \<open>
  The state-level fact behind \<open>afilter\<close>'s \<open>V\<close> case: narrowing one location
  by \<open>intersect\<close> keeps every location represented, the narrowed one because
  \<open>intersect_sound\<close> says so and every other because it is untouched. Named
  once here so \<open>afilter_sound\<close>'s \<open>V\<close> case cites it instead of unfolding
  \<open>gamma_state_def\<close> and case-splitting on \<open>y = x\<close> inline.
\<close>

lemma gamma_state_update_intersect [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and "s x \<in> gamma a"
  shows "s \<in> \<lbrakk>\<sigma>(x := intersect a (\<sigma> x))\<rbrakk>"
  using assms by (simp add: gamma_stateD gamma_stateI intersect_sound)

lemma afilter_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "aval e s \<in> gamma a"
  shows "s \<in> \<lbrakk>afilter e a \<sigma>\<rbrakk>"
using assms proof (induction e arbitrary: a \<sigma>)
  case (V x)
  then show ?case
    unfolding afilter.simps aval.simps by (rule gamma_state_update_intersect)
next
  case (Plus e1 e2)
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" and e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)"
    using aval_abs_sound[OF Plus.prems(1)] by simp_all
  have asum: "aval e1 s + aval e2 s \<in> gamma a" using Plus.prems(2) by simp
  show ?case
    unfolding afilter.simps Let_def case_prod_beta
    using e1a e2a asum Plus.prems(1)
    by (blast intro: Plus.IH)
next
  case (Minus e1 e2)
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" and e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)"
    using aval_abs_sound[OF Minus.prems(1)] by simp_all
  have adiff: "aval e1 s - aval e2 s \<in> gamma a" using Minus.prems(2) by simp
  show ?case
    unfolding afilter.simps Let_def case_prod_beta
    using e1a e2a adiff Minus.prems(1)
    by (blast intro: Minus.IH)
next
  case (Times e1 e2)
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" and e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)"
    using aval_abs_sound[OF Times.prems(1)] by simp_all
  have aprod: "aval e1 s * aval e2 s \<in> gamma a" using Times.prems(2) by simp
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
  assumes st: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
      and fst: "aval e1 s \<in> gamma (fst p)"
      and snd: "aval e2 s \<in> gamma (snd p)"
  shows "s \<in> \<lbrakk>afilter e1 (fst p) (afilter e2 (snd p) \<sigma>)\<rbrakk>"
proof -
  have inner: "s \<in> \<lbrakk>afilter e2 (snd p) \<sigma>\<rbrakk>" by (rule afilter_sound[OF st snd])
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
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (aval e s) = res"
  shows "s \<in> \<lbrakk>afilter e (fst (inv_eq (\<not> res) (aval_abs e \<sigma>) (aval_abs (N 0) \<sigma>))) \<sigma>\<rbrakk>"
proof -
  have ea: "aval e s \<in> gamma (aval_abs e \<sigma>)"
    using aval_abs_sound[OF assms(1)] by simp
  have e0: "aval (N 0) s \<in> gamma (aval_abs (N 0) \<sigma>)"
    by (rule aval_abs_sound[of s \<sigma> "N 0", OF assms(1)])
  have eq0: "(aval e s = aval (N 0) s) = (\<not> res)"
    using assms(2) by auto
  have "aval e s \<in> gamma (fst (inv_eq (\<not> res) (aval_abs e \<sigma>) (aval_abs (N 0) \<sigma>)))"
    using inv_eq_sound[OF ea e0 eq0] by simp
  then show ?thesis using afilter_sound[OF assms(1)]
    by simp
qed

lemma bfilter_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (aval e s) = res"
  shows "s \<in> \<lbrakk>bfilter e res \<sigma>\<rbrakk>"
using assms proof (induction e arbitrary: res \<sigma>)
  case (N n)
  then show ?case by simp
next
  case (V x)
  then show ?case
    using bfilter_default_sound[OF V.prems(1) V.prems(2)]
    by (simp add: case_prod_beta fun_upd_def)
next
  case (Plus e1 e2)
  show ?case
    using bfilter_default_sound[OF Plus.prems(1) Plus.prems(2)] by (simp add: case_prod_beta)
next
  case (Minus e1 e2)
  show ?case
    using bfilter_default_sound[OF Minus.prems(1) Minus.prems(2)] by (simp add: case_prod_beta)
next
  case (Times e1 e2)
  show ?case
    using bfilter_default_sound[OF Times.prems(1) Times.prems(2)] by (simp add: case_prod_beta)
next
  case (Not e)
  have bv': "truthy (aval e s) = (\<not> res)" using Not.prems(2) by (auto split: if_splits)
  from Not.IH[OF Not.prems(1) bv'] show ?case by simp
next
  case (And e1 e2)
  show ?case
  proof (cases res)
    case True
    have v1: "truthy (aval e1 s) = True" and v2: "truthy (aval e2 s) = True"
      using And.prems(2) True unfolding truthy_aval_And by simp_all
    show ?thesis
      using And.IH(1)[OF And.IH(2)[OF And.prems(1) v2] v1] by (simp add: True)
  next
    case False
    have disj: "\<not> truthy (aval e1 s) \<or> \<not> truthy (aval e2 s)"
      using And.prems(2) False by (auto split: if_splits)
    show ?thesis
    proof (cases "truthy (aval e1 s)")
      case b1F: False
      have v1: "truthy (aval e1 s) = False" using b1F by simp
      have h': "s \<in> \<lbrakk>bfilter e1 False \<sigma>\<rbrakk>" using And.IH(1)[OF And.prems(1) v1] .
      have g: "feasible e1 False \<sigma>" by (rule feasible_of_concrete[OF And.prems(1) v1])
      have eqb: "bfilter (And e1 e2) res \<sigma>
                   = bfilter e1 False \<sigma>
                     \<squnion> (if feasible e2 False \<sigma> then bfilter e2 False \<sigma> else bot)"
        using False g by simp
      show ?thesis unfolding eqb using h' by (rule gamma_state_supI1)
    next
      case b1T: True
      have v2: "truthy (aval e2 s) = False" using disj b1T by simp
      have h': "s \<in> \<lbrakk>bfilter e2 False \<sigma>\<rbrakk>" using And.IH(2)[OF And.prems(1) v2] .
      have g: "feasible e2 False \<sigma>" by (rule feasible_of_concrete[OF And.prems(1) v2])
      have eqb: "bfilter (And e1 e2) res \<sigma>
                   = (if feasible e1 False \<sigma> then bfilter e1 False \<sigma> else bot)
                     \<squnion> bfilter e2 False \<sigma>"
        using False g by simp
      show ?thesis unfolding eqb using h' by (rule gamma_state_supI2)
    qed
  qed
next
  case (Or e1 e2)
  show ?case
  proof (cases res)
    case True
    have disj: "truthy (aval e1 s) \<or> truthy (aval e2 s)"
      using Or.prems(2) True by (auto split: if_splits)
    show ?thesis proof (cases "truthy (aval e1 s)")
      case b1T: True
      have v1: "truthy (aval e1 s) = True" using b1T by simp
      have h': "s \<in> \<lbrakk>bfilter e1 True \<sigma>\<rbrakk>" using Or.IH(1)[OF Or.prems(1) v1] .
      have g: "feasible e1 True \<sigma>" by (rule feasible_of_concrete[OF Or.prems(1) v1])
      have eqb: "bfilter (Or e1 e2) res \<sigma>
                   = bfilter e1 True \<sigma>
                     \<squnion> (if feasible e2 True \<sigma> then bfilter e2 True \<sigma> else bot)"
        using True g by simp
      show ?thesis unfolding eqb using h' by (rule gamma_state_supI1)
    next
      case b1F: False
      have v2: "truthy (aval e2 s) = True" using disj b1F by simp
      have h': "s \<in> \<lbrakk>bfilter e2 True \<sigma>\<rbrakk>" using Or.IH(2)[OF Or.prems(1) v2] .
      have g: "feasible e2 True \<sigma>" by (rule feasible_of_concrete[OF Or.prems(1) v2])
      have eqb: "bfilter (Or e1 e2) res \<sigma>
                   = (if feasible e1 True \<sigma> then bfilter e1 True \<sigma> else bot)
                     \<squnion> bfilter e2 True \<sigma>"
        using True g by simp
      show ?thesis unfolding eqb using h' by (rule gamma_state_supI2)
    qed
  next
    case False
    have v1: "truthy (aval e1 s) = False" and v2: "truthy (aval e2 s) = False"
      using Or.prems(2) False unfolding truthy_aval_Or by simp_all
    show ?thesis
      using Or.IH(1)[OF Or.IH(2)[OF Or.prems(1) v2] v1] by (simp add: False)
  qed
next
  case (Less e1 e2)
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" and e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)"
    using aval_abs_sound[OF Less.prems(1)] by simp_all
  have less: "(aval e1 s < aval e2 s) = res" using Less.prems(2) by (auto split: if_splits)
  show ?case
    unfolding bfilter.simps Let_def case_prod_beta
    by (blast intro: Less.prems(1) inv_less_sound_fst[OF e1a e2a less]
                      inv_less_sound_snd[OF e1a e2a less])
next
  case (Eq e1 e2)
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" and e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)"
    using aval_abs_sound[OF Eq.prems(1)] by simp_all
  have eq: "(aval e1 s = aval e2 s) = res" using Eq.prems(2) by (auto split: if_splits)
  show ?case
    unfolding bfilter.simps Let_def case_prod_beta
    by (blast intro: Eq.prems(1) inv_eq_sound_fst[OF e1a e2a eq] inv_eq_sound_snd[OF e1a e2a eq])
qed

text \<open>
  \<open>branch_lifted\<close> is the Goblint-aligned branch semantics: the forward
  \<open>feasible\<close> gate on the whole condition ahead of \<open>bfilter\<close>, matching
  \<open>Base.branch\<close>'s \<open>eval_rv\<close> / \<open>to_bool\<close> dead-code gate ahead of \<open>invariant\<close>.
  An infeasible condition denotes \<open>Bot\<close> -- no concrete successor, matching
  Goblint's \<open>Deadcode\<close> as an outer control-flow fact rather than a value of the
  domain -- while every other case narrows via \<open>bfilter\<close> and returns
  \<open>Lifted\<close>. \<open>tobool\<close>'s definite answer, when present, is exactly \<open>truthy\<close> of
  every concrete value \<open>aval_abs e \<sigma>\<close> represents; \<open>truthy (aval e s) = pol\<close>
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

  \<open>branch\<close> is the plain-\<open>abs_state\<close> projection of \<open>branch_lifted\<close>, used by
  \<open>domain_transfer\<close>'s \<open>tf_branch\<close> field (and hence \<open>apply_tf\<close>): it collapses
  \<open>Bot\<close> to ordinary \<open>bot\<close>, so a caller that never needs to distinguish "no
  successor" from "successor whose store is bottom" can keep working with
  plain \<open>abs_state\<close>.
\<close>

definition branch :: "exp => bool => 'a abs_state => 'a abs_state" where
  "branch e pol \<sigma> = (if feasible e pol \<sigma> then bfilter e pol \<sigma> else bot)"

text \<open>
  The plain-state case split, recovered as a lemma rather than the primitive
  definition: callers reasoning about \<open>branch\<close> at the plain \<open>abs_state\<close> level
  (\<open>domain_transfer\<close>'s \<open>tf_branch\<close> field, the executable mirror) unfold through
  this instead of \<open>branch_lifted\<close>.
\<close>

lemma branch_unfold:
  "branch e pol \<sigma> = (if feasible e pol \<sigma> then bfilter e pol \<sigma> else bot)"
  by (rule branch_def)

text \<open>
  \<open>bfilter\<close>'s two join cases, restated through \<open>branch\<close>: each disjunct is
  narrowed by exactly the operator the branch transfer applies to a whole
  condition, and the results are joined. This is the shape Goblint's \<open>inv_exp\<close>
  has for \<open>LOr\<close> -- refine each arm, drop an arm whose refinement raises
  \<open>Deadcode\<close> -- with \<open>bot\<close> in place of the exception, since \<open>bot\<close> is the unit
  of \<open>\<squnion>\<close>. Downstream mirrors and their correctness proofs cite these rather
  than re-deriving the gate from \<open>bfilter\<close>'s primitive equations.

  Each equation is stated directly over raw \<open>branch\<close> results, matching
  \<open>bfilter\<close>'s own join-case equations: a disjunct feasible by the forward
  gate can still have its own \<open>bfilter\<close> narrowing discover a stronger
  backward-only contradiction, landing on a witness-bottom, non-canonical
  \<open>abs_state\<close> (@{const is_empty_state} without being the literal pointwise
  \<open>bot\<close>) that pollutes the pointwise join with its unrefined other
  locations -- see \<open>bfilter\<close>'s own comment. \<open>bfilter_lifted\<close> is where this
  is corrected.
\<close>

lemma bfilter_And_False_branch:
  "bfilter (And b1 b2) False \<sigma> = branch b1 False \<sigma> \<squnion> branch b2 False \<sigma>"
  by (simp add: branch_unfold)

lemma bfilter_Or_True_branch:
  "bfilter (Or b1 b2) True \<sigma> = branch b1 True \<sigma> \<squnion> branch b2 True \<sigma>"
  by (simp add: branch_unfold)

lemma branch_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (aval e s) = pol"
  shows "s \<in> \<lbrakk>branch e pol \<sigma>\<rbrakk>"
  using assms feasible_of_concrete[OF assms] bfilter_sound[OF assms]
  by (simp add: branch_unfold)

text \<open>
  \<open>branch\<close> only ever narrows further than \<open>bfilter\<close>: it either falls
  through to \<open>bfilter\<close> unchanged, or short-circuits to \<open>bot\<close>, and \<open>bot\<close> is
  least. Callers that only need an upper bound on \<open>branch\<close>'s result -- e.g.
  post-fixpoint checks -- can reuse their existing \<open>bfilter\<close>-level
  reasoning through this fact instead of re-deriving it against \<open>branch\<close>'s
  case split.
\<close>

lemma branch_le_bfilter: "branch e pol \<sigma> \<le> bfilter e pol \<sigma>"
  by (simp add: branch_unfold)

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
    "bfilter_lifted (Less e1 e2) res \<sigma> = normalize_lift is_empty_state (bfilter (Less e1 e2) res \<sigma>)"
  | "bfilter_lifted (Not b) res \<sigma> = bfilter_lifted b (\<not> res) \<sigma>"
  | "bfilter_lifted (And b1 b2) True  \<sigma> =
       bind_lift (bfilter_lifted b2 True \<sigma>) (bfilter_lifted b1 True)"
  | "bfilter_lifted (And b1 b2) False \<sigma> =
       (if feasible b1 False \<sigma> then bfilter_lifted b1 False \<sigma> else Bot)
       \<squnion> (if feasible b2 False \<sigma> then bfilter_lifted b2 False \<sigma> else Bot)"
  | "bfilter_lifted (Or  b1 b2) True  \<sigma> =
       (if feasible b1 True \<sigma> then bfilter_lifted b1 True \<sigma> else Bot)
       \<squnion> (if feasible b2 True \<sigma> then bfilter_lifted b2 True \<sigma> else Bot)"
  | "bfilter_lifted (Or  b1 b2) False \<sigma> =
       bind_lift (bfilter_lifted b2 False \<sigma>) (bfilter_lifted b1 False)"
  | "bfilter_lifted (Eq  e1 e2) res  \<sigma> = normalize_lift is_empty_state (bfilter (Eq e1 e2) res \<sigma>)"
  | "bfilter_lifted e res \<sigma> = normalize_lift is_empty_state (bfilter e res \<sigma>)"

lemma bfilter_lifted_normalized [simp]:
  "normalized_lift is_empty_state (bfilter_lifted e pol \<sigma>)"
proof (induction e arbitrary: pol \<sigma>)
  case (And b1 b2)
  then show ?case
    by (cases pol) (auto intro: normalized_lift_bind)
next
  case (Or b1 b2)
  then show ?case
    by (cases pol) (auto intro: normalized_lift_bind)
qed simp_all

lemma bfilter_lifted_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (aval e s) = res"
  shows "s \<in> gamma_state_lift (bfilter_lifted e res \<sigma>)"
using assms proof (induction e arbitrary: res \<sigma>)
  case (N n)
  show ?case using bfilter_sound[OF N.prems] by simp
next
  case (V x)
  show ?case using bfilter_sound[OF V.prems] by simp
next
  case (Plus e1 e2)
  show ?case using bfilter_sound[OF Plus.prems] by simp
next
  case (Minus e1 e2)
  show ?case using bfilter_sound[OF Minus.prems] by simp
next
  case (Times e1 e2)
  show ?case using bfilter_sound[OF Times.prems] by simp
next
  case (Less e1 e2)
  show ?case using bfilter_sound[OF Less.prems] by simp
next
  case (Eq e1 e2)
  show ?case using bfilter_sound[OF Eq.prems] by simp
next
  case (Not e)
  have bv': "truthy (aval e s) = (\<not> res)" using Not.prems(2) by (auto split: if_splits)
  from Not.IH[OF Not.prems(1) bv'] show ?case by simp
next
  case (And e1 e2)
  show ?case
  proof (cases res)
    case True
    have v1: "truthy (aval e1 s) = True" and v2: "truthy (aval e2 s) = True"
      using And.prems(2) True unfolding truthy_aval_And by simp_all
    have h2: "s \<in> gamma_state_lift (bfilter_lifted e2 True \<sigma>)"
      using And.IH(2)[OF And.prems(1) v2] .
    have res_eq: "res = True" using True by simp
    show ?thesis
      unfolding res_eq bfilter_lifted.simps
      using h2 v1 by (blast intro: And.IH(1))
  next
    case False
    have disj: "\<not> truthy (aval e1 s) \<or> \<not> truthy (aval e2 s)"
      using And.prems(2) False by (auto split: if_splits)
    show ?thesis proof (cases "truthy (aval e1 s)")
      case b1F: False
      have v1: "truthy (aval e1 s) = False" using b1F by simp
      have h': "s \<in> gamma_state_lift (bfilter_lifted e1 False \<sigma>)"
        using And.IH(1)[OF And.prems(1) v1] .
      have g: "feasible e1 False \<sigma>" by (rule feasible_of_concrete[OF And.prems(1) v1])
      have eqb: "bfilter_lifted (And e1 e2) res \<sigma>
                   = bfilter_lifted e1 False \<sigma>
                     \<squnion> (if feasible e2 False \<sigma> then bfilter_lifted e2 False \<sigma> else Bot)"
        using False g by simp
      show ?thesis unfolding eqb using h' by (rule gamma_state_lift_supI1)
    next
      case b1T: True
      have v2: "truthy (aval e2 s) = False" using disj b1T by simp
      have h': "s \<in> gamma_state_lift (bfilter_lifted e2 False \<sigma>)"
        using And.IH(2)[OF And.prems(1) v2] .
      have g: "feasible e2 False \<sigma>" by (rule feasible_of_concrete[OF And.prems(1) v2])
      have eqb: "bfilter_lifted (And e1 e2) res \<sigma>
                   = (if feasible e1 False \<sigma> then bfilter_lifted e1 False \<sigma> else Bot)
                     \<squnion> bfilter_lifted e2 False \<sigma>"
        using False g by simp
      show ?thesis unfolding eqb using h' by (rule gamma_state_lift_supI2)
    qed
  qed
next
  case (Or e1 e2)
  show ?case
  proof (cases res)
    case True
    have disj: "truthy (aval e1 s) \<or> truthy (aval e2 s)"
      using Or.prems(2) True by (auto split: if_splits)
    show ?thesis proof (cases "truthy (aval e1 s)")
      case b1T: True
      have v1: "truthy (aval e1 s) = True" using b1T by simp
      have h': "s \<in> gamma_state_lift (bfilter_lifted e1 True \<sigma>)"
        using Or.IH(1)[OF Or.prems(1) v1] .
      have g: "feasible e1 True \<sigma>" by (rule feasible_of_concrete[OF Or.prems(1) v1])
      have eqb: "bfilter_lifted (Or e1 e2) res \<sigma>
                   = bfilter_lifted e1 True \<sigma>
                     \<squnion> (if feasible e2 True \<sigma> then bfilter_lifted e2 True \<sigma> else Bot)"
        using True g by simp
      show ?thesis unfolding eqb using h' by (rule gamma_state_lift_supI1)
    next
      case b1F: False
      have v2: "truthy (aval e2 s) = True" using disj b1F by simp
      have h': "s \<in> gamma_state_lift (bfilter_lifted e2 True \<sigma>)"
        using Or.IH(2)[OF Or.prems(1) v2] .
      have g: "feasible e2 True \<sigma>" by (rule feasible_of_concrete[OF Or.prems(1) v2])
      have eqb: "bfilter_lifted (Or e1 e2) res \<sigma>
                   = (if feasible e1 True \<sigma> then bfilter_lifted e1 True \<sigma> else Bot)
                     \<squnion> bfilter_lifted e2 True \<sigma>"
        using True g by simp
      show ?thesis unfolding eqb using h' by (rule gamma_state_lift_supI2)
    qed
  next
    case False
    have v1: "truthy (aval e1 s) = False" and v2: "truthy (aval e2 s) = False"
      using Or.prems(2) False unfolding truthy_aval_Or by simp_all
    have h2: "s \<in> gamma_state_lift (bfilter_lifted e2 False \<sigma>)"
      using Or.IH(2)[OF Or.prems(1) v2] .
    have res_eq: "res = False" using False by simp
    show ?thesis
      unfolding res_eq bfilter_lifted.simps
      using h2 v1 by (blast intro: Or.IH(1))
  qed
qed

text \<open>
  \<open>branch_lifted\<close> is \<open>branch\<close>'s reachability wrapper, now routed through
  \<open>bfilter_lifted\<close> rather than raw \<open>bfilter\<close>: the top-level \<open>feasible\<close> gate is
  unchanged (that is \<open>branch\<close>'s own concern, not the \<open>And\<close>/\<open>Or\<close> pollution
  \<open>bfilter_lifted\<close> fixes), but the filtering it gates is the corrected
  recursion, so \<open>branch_lifted\<close> inherits the improved precision without
  restating it.
\<close>

definition branch_lifted :: "exp => bool => 'a abs_state => 'a abs_state lifted" where
  "branch_lifted e pol \<sigma> = (if feasible e pol \<sigma> then bfilter_lifted e pol \<sigma> else Bot)"

lemma branch_lifted_normalized [simp]:
  "normalized_lift is_empty_state (branch_lifted e pol \<sigma>)"
  unfolding branch_lifted_def by simp

lemma branch_lifted_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (aval e s) = pol"
  shows "s \<in> gamma_state_lift (branch_lifted e pol \<sigma>)"
proof -
  have g: "feasible e pol \<sigma>" by (rule feasible_of_concrete[OF assms])
  have "s \<in> gamma_state_lift (bfilter_lifted e pol \<sigma>)" by (rule bfilter_lifted_sound[OF assms])
  with g show ?thesis unfolding branch_lifted_def by simp
qed

end


subsection \<open>Conservative inverse operator\<close>

text \<open>
  A domain that is too coarse for useful arithmetic inversion (e.g. sign,
  which cannot narrow either operand of a plus/minus/times from its result)
  instantiates @{term inv_plus} / @{term inv_minus} / @{term inv_times} with
  this shared no-op: both operands pass through unchanged. Any
  @{class sound_domain} discharges its soundness for free, so domains share
  one proof instead of each restating the same trivial obligation.
\<close>

definition inv_conservative :: "'a => 'a => 'a => 'a * 'a" where
  "inv_conservative r a1 a2 = (a1, a2)"

lemma inv_conservative_sound:
  fixes a1 a2 :: "'a::sound_domain"
  assumes "n1 \<in> gamma a1" and "n2 \<in> gamma a2"
  shows "n1 \<in> gamma (fst (inv_conservative r a1 a2)) \<and> n2 \<in> gamma (snd (inv_conservative r a1 a2))"
  using assms by (simp add: inv_conservative_def)

lemma inv_conservative_reductive1:
  fixes a1 a2 :: "'a::sound_domain"
  shows "fst (inv_conservative r a1 a2) \<le> a1"
  by (simp add: inv_conservative_def)

lemma inv_conservative_reductive2:
  fixes a1 a2 :: "'a::sound_domain"
  shows "snd (inv_conservative r a1 a2) \<le> a2"
  by (simp add: inv_conservative_def)

end
