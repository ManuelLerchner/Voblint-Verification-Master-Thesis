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
  and inv_less_sound[intro]:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> (n1 < n2) = res
       \<Longrightarrow> n1 \<in> gamma (fst (inv_less res a1 a2)) \<and> n2 \<in> gamma (snd (inv_less res a1 a2))"
  and inv_eq_sound[intro]:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> (n1 = n2) = res
       \<Longrightarrow> n1 \<in> gamma (fst (inv_eq res a1 a2)) \<and> n2 \<in> gamma (snd (inv_eq res a1 a2))"
  and inv_plus_sound[intro]:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> n1 + n2 \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_plus r a1 a2)) \<and> n2 \<in> gamma (snd (inv_plus r a1 a2))"
  and inv_minus_sound[intro]:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> n1 - n2 \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_minus r a1 a2)) \<and> n2 \<in> gamma (snd (inv_minus r a1 a2))"
  and inv_times_sound[intro]:
      "n1 \<in> gamma a1 \<Longrightarrow> n2 \<in> gamma a2 \<Longrightarrow> n1 * n2 \<in> gamma r
       \<Longrightarrow> n1 \<in> gamma (fst (inv_times r a1 a2)) \<and> n2 \<in> gamma (snd (inv_times r a1 a2))"
  and tobool_sound:
      "tobool p = Some b \<Longrightarrow> i \<in> gamma p \<Longrightarrow> truthy i = b"
begin

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

lemma feasible_of_concrete:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and "truthy (aval e s) = pol"
  shows "feasible e pol \<sigma>"
proof -
  have ea: "aval e s \<in> gamma (aval_abs e \<sigma>)"
    by (simp add: assms(1) aval_abs_sound)
  have nb: "\<not> is_empty (aval_abs e \<sigma>)"
    using ea is_empty_correct by auto
  have "tobool (aval_abs e \<sigma>) \<noteq> Some (\<not> pol)"
    using assms(2) ea tobool_sound by blast
  with nb show ?thesis by (simp add: feasible_def)
qed
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

lemma afilter_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "aval e s \<in> gamma a"
  shows "s \<in> \<lbrakk>afilter e a \<sigma>\<rbrakk>"
using assms proof (induction e arbitrary: a \<sigma>)
  case (N n)
  then show ?case by simp
next
  case (V x)
  have sx_a: "s x \<in> gamma a"
    using V.prems(2) by simp
  have sx_s: "s x \<in> gamma (\<sigma> x)"
    using gamma_stateD[OF V.prems(1)] by simp
  show ?case
    unfolding gamma_state_def afilter.simps
  proof (intro CollectI allI)
    fix y show "s y \<in> gamma ((\<sigma>(x := intersect a (\<sigma> x))) y)"
      using intersect_sound[OF sx_a sx_s] gamma_stateD[OF V.prems(1)]
      by (cases "y = x") auto
  qed
next
  case (Plus e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF Plus.prems(1)] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF Plus.prems(1)] by simp
  have asum: "aval e1 s + aval e2 s \<in> gamma a" using Plus.prems(2) by simp
  have inv12: "aval e1 s \<in> gamma a1 \<and> aval e2 s \<in> gamma a2"
    using inv_plus_sound[OF e1a e2a asum] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter e2 a2 \<sigma>\<rbrakk>"
    using Plus.IH(2)[OF Plus.prems(1) inv12[THEN conjunct2]] by simp
  show ?case
    unfolding afilter.simps pair[symmetric] Let_def
    using Plus.IH(1)[OF gs2 inv12[THEN conjunct1]] by simp
next
  case (Minus e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_minus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_minus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF Minus.prems(1)] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF Minus.prems(1)] by simp
  have adiff: "aval e1 s - aval e2 s \<in> gamma a" using Minus.prems(2) by simp
  have inv12: "aval e1 s \<in> gamma a1 \<and> aval e2 s \<in> gamma a2"
    using inv_minus_sound[OF e1a e2a adiff] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter e2 a2 \<sigma>\<rbrakk>"
    using Minus.IH(2)[OF Minus.prems(1) inv12[THEN conjunct2]] by simp
  show ?case
    unfolding afilter.simps pair[symmetric] Let_def
    using Minus.IH(1)[OF gs2 inv12[THEN conjunct1]] by simp
next
  case (Times e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_times a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_times a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF Times.prems(1)] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF Times.prems(1)] by simp
  have aprod: "aval e1 s * aval e2 s \<in> gamma a" using Times.prems(2) by simp
  have inv12: "aval e1 s \<in> gamma a1 \<and> aval e2 s \<in> gamma a2"
    using inv_times_sound[OF e1a e2a aprod] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter e2 a2 \<sigma>\<rbrakk>"
    using Times.IH(2)[OF Times.prems(1) inv12[THEN conjunct2]] by simp
  show ?case
    unfolding afilter.simps pair[symmetric] Let_def
    using Times.IH(1)[OF gs2 inv12[THEN conjunct1]] by simp
next
  case (Less e1 e2) then show ?case by simp
next
  case (Eq e1 e2) then show ?case by simp
next
  case (Not e) then show ?case by simp
next
  case (And e1 e2) then show ?case by simp
next
  case (Or e1 e2) then show ?case by simp
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
  have ea: "aval e s \<in> gamma (aval_abs e \<sigma>)" using aval_abs_sound[OF assms(1)] by simp
  have e0: "aval (N 0) s \<in> gamma (aval_abs (N 0) \<sigma>)" by (rule aval_abs_sound[of s \<sigma> "N 0", OF assms(1)])
  have eq0: "(aval e s = aval (N 0) s) = (\<not> res)" using assms(2) by auto
  have "aval e s \<in> gamma (fst (inv_eq (\<not> res) (aval_abs e \<sigma>) (aval_abs (N 0) \<sigma>)))"
    using inv_eq_sound[OF ea e0 eq0] by simp
  then show ?thesis using afilter_sound[OF assms(1)] by simp
qed

lemma bfilter_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (aval e s) = res"
  shows "s \<in> \<lbrakk>bfilter e res \<sigma>\<rbrakk>"
using assms proof (induction e arbitrary: res \<sigma>)
  case (N n) show ?case using bfilter_default_sound[OF N.prems(1) N.prems(2)] by simp
next
  case (V x) show ?case
    using bfilter_default_sound[OF V.prems(1) V.prems(2)]
    by (simp add: Let_def case_prod_beta fun_upd_def)
next
  case (Plus e1 e2) show ?case
    using bfilter_default_sound[OF Plus.prems(1) Plus.prems(2)] by (simp add: Let_def case_prod_beta)
next
  case (Minus e1 e2) show ?case
    using bfilter_default_sound[OF Minus.prems(1) Minus.prems(2)] by (simp add: Let_def case_prod_beta)
next
  case (Times e1 e2) show ?case
    using bfilter_default_sound[OF Times.prems(1) Times.prems(2)] by (simp add: Let_def case_prod_beta)
next
  case (Not e)
  have bv': "truthy (aval e s) = (\<not> res)" using Not.prems(2) by (auto split: if_splits)
  from Not.IH[OF Not.prems(1) bv'] show ?case by simp
next
  case (And e1 e2)
  show ?case proof (cases res)
    case True
    have v1: "truthy (aval e1 s) = True" and v2: "truthy (aval e2 s) = True"
      using And.prems(2) True by (auto split: if_splits)
    have gs2: "s \<in> \<lbrakk>bfilter e2 True \<sigma>\<rbrakk>"
      using And.IH(2)[OF And.prems(1) v2] by simp
    show ?thesis
      using And.IH(1)[OF gs2 v1] by (simp add: True)
  next
    case False
    have disj: "\<not> truthy (aval e1 s) \<or> \<not> truthy (aval e2 s)"
      using And.prems(2) False by (auto split: if_splits)
    show ?thesis proof (cases "truthy (aval e1 s)")
      case b1F: False
      have v1: "truthy (aval e1 s) = False" using b1F by simp
      have h: "s \<in> \<lbrakk>bfilter e1 False \<sigma>\<rbrakk>"
        using And.IH(1)[OF And.prems(1) v1] by simp
      have g: "feasible e1 False \<sigma>" by (rule feasible_of_concrete[OF And.prems(1) v1])
      have sup1: "s \<in> \<lbrakk>bfilter e1 False \<sigma>
                       \<squnion> (if feasible e2 False \<sigma> then bfilter e2 False \<sigma> else bot)\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub1 h] .
      have eqb: "bfilter (And e1 e2) res \<sigma>
                   = bfilter e1 False \<sigma>
                     \<squnion> (if feasible e2 False \<sigma> then bfilter e2 False \<sigma> else bot)"
        using False g by simp
      show ?thesis unfolding eqb by (rule sup1)    next
      case b1T: True
      have v2: "truthy (aval e2 s) = False" using disj b1T by simp
      have h: "s \<in> \<lbrakk>bfilter e2 False \<sigma>\<rbrakk>"
        using And.IH(2)[OF And.prems(1) v2] by simp
      have g: "feasible e2 False \<sigma>" by (rule feasible_of_concrete[OF And.prems(1) v2])
      have sup2: "s \<in> \<lbrakk>(if feasible e1 False \<sigma> then bfilter e1 False \<sigma> else bot)
                       \<squnion> bfilter e2 False \<sigma>\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub2 h] .
      have eqb: "bfilter (And e1 e2) res \<sigma>
                   = (if feasible e1 False \<sigma> then bfilter e1 False \<sigma> else bot)
                     \<squnion> bfilter e2 False \<sigma>"
        using False g by simp
      show ?thesis unfolding eqb by (rule sup2)    qed
  qed
next
  case (Or e1 e2)
  show ?case proof (cases res)
    case True
    have disj: "truthy (aval e1 s) \<or> truthy (aval e2 s)"
      using Or.prems(2) True by (auto split: if_splits)
    show ?thesis proof (cases "truthy (aval e1 s)")
      case b1T: True
      have v1: "truthy (aval e1 s) = True" using b1T by simp
      have h: "s \<in> \<lbrakk>bfilter e1 True \<sigma>\<rbrakk>"
        using Or.IH(1)[OF Or.prems(1) v1] by simp
      have g: "feasible e1 True \<sigma>" by (rule feasible_of_concrete[OF Or.prems(1) v1])
      have sup1: "s \<in> \<lbrakk>bfilter e1 True \<sigma>
                       \<squnion> (if feasible e2 True \<sigma> then bfilter e2 True \<sigma> else bot)\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub1 h] .
      have eqb: "bfilter (Or e1 e2) res \<sigma>
                   = bfilter e1 True \<sigma>
                     \<squnion> (if feasible e2 True \<sigma> then bfilter e2 True \<sigma> else bot)"
        using True g by simp
      show ?thesis unfolding eqb by (rule sup1)    next
      case b1F: False
      have v2: "truthy (aval e2 s) = True" using disj b1F by simp
      have h: "s \<in> \<lbrakk>bfilter e2 True \<sigma>\<rbrakk>"
        using Or.IH(2)[OF Or.prems(1) v2] by simp
      have g: "feasible e2 True \<sigma>" by (rule feasible_of_concrete[OF Or.prems(1) v2])
      have sup2: "s \<in> \<lbrakk>(if feasible e1 True \<sigma> then bfilter e1 True \<sigma> else bot)
                       \<squnion> bfilter e2 True \<sigma>\<rbrakk>"
        using subsetD[OF gamma_state_sup_ub2 h] .
      have eqb: "bfilter (Or e1 e2) res \<sigma>
                   = (if feasible e1 True \<sigma> then bfilter e1 True \<sigma> else bot)
                     \<squnion> bfilter e2 True \<sigma>"
        using True g by simp
      show ?thesis unfolding eqb by (rule sup2)    qed
  next
    case False
    have v1: "truthy (aval e1 s) = False" and v2: "truthy (aval e2 s) = False"
      using Or.prems(2) False by (auto split: if_splits)
    have gs2: "s \<in> \<lbrakk>bfilter e2 False \<sigma>\<rbrakk>"
      using Or.IH(2)[OF Or.prems(1) v2] by simp
    show ?thesis
      using Or.IH(1)[OF gs2 v1] by (simp add: False)
      qed
next
  case (Less e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF Less.prems(1)] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF Less.prems(1)] by simp
  have less: "(aval e1 s < aval e2 s) = res" using Less.prems(2) by (auto split: if_splits)
  have inv12: "aval e1 s \<in> gamma a1 \<and> aval e2 s \<in> gamma a2"
    using inv_less_sound[OF e1a e2a less] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter e2 a2 \<sigma>\<rbrakk>"
    using afilter_sound[OF Less.prems(1) inv12[THEN conjunct2]] by simp
  show ?case
    unfolding bfilter.simps pair[symmetric] Let_def
    using afilter_sound[OF gs2 inv12[THEN conjunct1]] by simp
next
  case (Eq e1 e2)
  obtain a1 a2 where pair: "(a1, a2) = inv_eq res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)"
    by (cases "inv_eq res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)") auto
  have e1a: "aval e1 s \<in> gamma (aval_abs e1 \<sigma>)" using aval_abs_sound[OF Eq.prems(1)] by simp
  have e2a: "aval e2 s \<in> gamma (aval_abs e2 \<sigma>)" using aval_abs_sound[OF Eq.prems(1)] by simp
  have eq: "(aval e1 s = aval e2 s) = res" using Eq.prems(2) by (auto split: if_splits)
  have inv12: "aval e1 s \<in> gamma a1 \<and> aval e2 s \<in> gamma a2"
    using inv_eq_sound[OF e1a e2a eq] pair[symmetric] by simp
  have gs2: "s \<in> \<lbrakk>afilter e2 a2 \<sigma>\<rbrakk>"
    using afilter_sound[OF Eq.prems(1) inv12[THEN conjunct2]] by simp
  show ?case
    unfolding bfilter.simps pair[symmetric] Let_def
    using afilter_sound[OF gs2 inv12[THEN conjunct1]] by simp
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

definition branch_lifted :: "exp => bool => 'a abs_state => 'a abs_state lifted" where
  "branch_lifted e pol \<sigma> = normalize_lift is_empty_state (branch e pol \<sigma>)"

lemma branch_lifted_normalized [simp]:
  "normalized_lift is_empty_state (branch_lifted e pol \<sigma>)"
  unfolding branch_lifted_def by (rule normalize_lift_normalized)

text \<open>
  \<open>branch_lifted\<close> is definitionally \<open>branch\<close>'s canonical reachability wrapper,
  not a second, independently-stated gate: the one place \<open>feasible\<close> and
  \<open>bfilter\<close> combine is \<open>branch\<close>'s own \<open>if\<close>, and \<open>branch_lifted\<close> only adds
  \<^const>\<open>normalize_lift\<close> on top. This rules out the two ever drifting apart.
  The concretizations agree exactly, not merely up to \<open>is_empty_state\<close>-collapsing:
  \<^const>\<open>normalize_lift\<close> only changes a value's representation between itself
  and \<^const>\<open>Bot\<close>, never what it concretizes to
  (\<open>is_empty_state_iff_gamma_state_empty\<close>).
\<close>

lemma gamma_branch_lifted:
  "gamma_state_lift (branch_lifted e pol \<sigma>) = \<lbrakk>branch e pol \<sigma>\<rbrakk>"
  unfolding branch_lifted_def normalize_lift_def is_empty_state_iff_gamma_state_empty
  by auto

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

  Neither equation is itself normalized: \<open>branch b1 False \<sigma> \<squnion> branch b2 False
  \<sigma>\<close> can still land on a witness-bottom, non-canonical \<open>abs_state\<close> when a
  disjunct is feasible by the forward gate but its own \<open>bfilter\<close> narrowing
  subsequently discovers a stronger contradiction (@{const is_empty_state}
  without being the literal pointwise \<open>bot\<close>). \<open>branch_lifted\<close> normalizes the
  whole condition only after this join, so it cannot repair a case where an
  infeasible-looking disjunct's non-bottom locations have already polluted a
  live disjunct's join result -- exactly the failure mode Goblint's
  \<open>inv_exp\<close> avoids by dropping a \<open>Deadcode\<close> arm before its own join. Closing
  this gap needs either canonicalizing each disjunct before the \<open>\<squnion>\<close> (matching
  what \<open>bfilter_st_lift\<close> already does at the executable \<open>resolved_st_q
  lifted\<close> level, downstream in the \<open>Voblint_Analysis\<close> session's
  \<open>Exec_Backward\<close> theory, via its \<open>probe_exp\<close> finite bottom test) or making
  \<open>bfilter\<close> itself \<open>lifted\<close>-valued and threading \<open>bind_lift\<close> through its
  recursion. Neither is done here.
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
proof -
  have f: "feasible e pol \<sigma>" by (rule feasible_of_concrete[OF assms])
  have "s \<in> \<lbrakk>bfilter e pol \<sigma>\<rbrakk>" by (rule bfilter_sound[OF assms])
  with f show ?thesis by (simp add: branch_unfold)
qed

lemma branch_lifted_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (aval e s) = pol"
  shows "s \<in> gamma_state_lift (branch_lifted e pol \<sigma>)"
proof -
  have bs: "s \<in> \<lbrakk>branch e pol \<sigma>\<rbrakk>" by (rule branch_sound[OF assms])
  then have "\<not> is_empty_state (branch e pol \<sigma>)" by (rule gamma_state_witness_not_empty)
  with bs show ?thesis unfolding branch_lifted_def by simp
qed

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
