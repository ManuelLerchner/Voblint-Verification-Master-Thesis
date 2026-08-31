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
  have ea: "aval e s \<in> gamma (aval_abs e \<sigma>)" using aval_abs_sound[OF assms(1)] by simp
  have nb: "\<not> is_empty (aval_abs e \<sigma>)" using ea is_empty_correct by auto
  have "tobool (aval_abs e \<sigma>) \<noteq> Some (\<not> pol)"
  proof
    assume "tobool (aval_abs e \<sigma>) = Some (\<not> pol)"
    then have "truthy (aval e s) = (\<not> pol)" using tobool_sound[OF _ ea] by simp
    then show False using assms(2) by simp
  qed
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
  contradiction. \<open>branch_lifted\<close> does not itself re-normalize that result
  against \<open>is_empty_state\<close>, so it is sound but not always structurally
  canonical; \<open>branch_lifted_normalized_iff\<close> below states exactly when the
  two coincide.

  \<open>branch\<close> is the plain-\<open>abs_state\<close> projection of \<open>branch_lifted\<close>, used by
  \<open>domain_transfer\<close>'s \<open>tf_branch\<close> field (and hence \<open>apply_tf\<close>): it collapses
  \<open>Bot\<close> to ordinary \<open>bot\<close>, so a caller that never needs to distinguish "no
  successor" from "successor whose store is bottom" can keep working with
  plain \<open>abs_state\<close>.
\<close>

definition branch_lifted :: "exp => bool => 'a abs_state => 'a abs_state lifted" where
  "branch_lifted e pol \<sigma> = (if feasible e pol \<sigma> then Lifted (bfilter e pol \<sigma>) else Bot)"

definition branch :: "exp => bool => 'a abs_state => 'a abs_state" where
  "branch e pol \<sigma> = (case branch_lifted e pol \<sigma> of Bot \<Rightarrow> bot | Lifted \<sigma>' \<Rightarrow> \<sigma>')"

lemma branch_lifted_normalized_iff:
  "normalized_lift is_empty_state (branch_lifted e pol \<sigma>) \<longleftrightarrow>
     \<not> feasible e pol \<sigma> \<or> \<not> is_empty_state (bfilter e pol \<sigma>)"
  by (simp add: branch_lifted_def normalized_lift_def)

text \<open>
  The plain-state case split, recovered as a lemma rather than the primitive
  definition: callers reasoning about \<open>branch\<close> at the plain \<open>abs_state\<close> level
  (\<open>domain_transfer\<close>'s \<open>tf_branch\<close> field, the executable mirror) unfold through
  this instead of \<open>branch_lifted\<close>.
\<close>

lemma branch_unfold:
  "branch e pol \<sigma> = (if feasible e pol \<sigma> then bfilter e pol \<sigma> else bot)"
  unfolding branch_def branch_lifted_def by simp

text \<open>
  \<open>bfilter\<close>'s two join cases, restated through \<open>branch\<close>: each disjunct is
  narrowed by exactly the operator the branch transfer applies to a whole
  condition, and the results are joined. This is the shape Goblint's \<open>inv_exp\<close>
  has for \<open>LOr\<close> -- refine each arm, drop an arm whose refinement raises
  \<open>Deadcode\<close> -- with \<open>bot\<close> in place of the exception, since \<open>bot\<close> is the unit
  of \<open>\<squnion>\<close>. Downstream mirrors and their correctness proofs cite these rather
  than re-deriving the gate from \<open>bfilter\<close>'s primitive equations.
\<close>

lemma bfilter_And_False_branch:
  "bfilter (And b1 b2) False \<sigma> = branch b1 False \<sigma> \<squnion> branch b2 False \<sigma>"
  by (simp add: branch_unfold)

lemma bfilter_Or_True_branch:
  "bfilter (Or b1 b2) True \<sigma> = branch b1 True \<sigma> \<squnion> branch b2 True \<sigma>"
  by (simp add: branch_unfold)
lemma branch_lifted_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (aval e s) = pol"
  shows "s \<in> gamma_state_lift (branch_lifted e pol \<sigma>)"
proof -
  have "feasible e pol \<sigma>" by (rule feasible_of_concrete[OF assms])
  then show ?thesis
    using bfilter_sound[OF assms] by (simp add: branch_lifted_def)
qed
lemma branch_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (aval e s) = pol"
  shows "s \<in> \<lbrakk>branch e pol \<sigma>\<rbrakk>"
proof -
  have "s \<in> gamma_state_lift (branch_lifted e pol \<sigma>)" by (rule branch_lifted_sound[OF assms])
  then show ?thesis
    unfolding branch_def by (cases "branch_lifted e pol \<sigma>") simp_all
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

text \<open>
  The same no-op shape for \<open>inv_eq\<close>: unlike \<open>inv_plus\<close>/\<open>inv_minus\<close>/\<open>inv_times\<close>,
  \<open>inv_eq\<close>'s first argument is \<open>bool\<close> (the assumed truth value, as for
  \<open>inv_less\<close>), not \<open>'a\<close>, so \<open>inv_conservative\<close> cannot be reused verbatim ---
  its three arguments all share one type. A domain not yet ready with a real
  equality narrowing (or one too coarse for it to help) instantiates \<open>inv_eq\<close>
  with this identity instead.
\<close>

definition inv_eq_identity :: "bool => 'a => 'a => 'a * 'a" where
  "inv_eq_identity res a1 a2 = (a1, a2)"

lemma inv_eq_identity_sound:
  fixes a1 a2 :: "'a::sound_domain"
  assumes "n1 \<in> gamma a1" and "n2 \<in> gamma a2"
  shows "n1 \<in> gamma (fst (inv_eq_identity res a1 a2)) \<and> n2 \<in> gamma (snd (inv_eq_identity res a1 a2))"
  using assms by (simp add: inv_eq_identity_def)

subsection \<open>Pairwise order for reductive/monotone inverse operators\<close>

text \<open>
  A minimal componentwise order on \<open>'a * 'a\<close>, used only to state each inverse
  operator's monotonicity and reductiveness as a single fact about its returned
  pair rather than as two separately-assumed projections. Deliberately not
  \<open>'a * 'a\<close>'s own \<open>\<le>\<close>: some already-transitively-imported theory instantiates
  \<open>('a,'b) prod :: order\<close> here with a non-componentwise (order-with-a-\<open><\<close>-disjunct)
  definition, so relying on the ambient \<open>\<le>\<close> would silently pick up the wrong
  relation. This local, self-contained \<open>\<le>_pair\<close> avoids that entirely.
\<close>

abbreviation le_pair :: "'a::order \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "le_pair p q \<equiv> fst p \<le> fst q \<and> snd p \<le> snd q"

lemma le_pair_fst: "le_pair p q \<Longrightarrow> fst p \<le> fst q"
  by simp

lemma le_pair_snd: "le_pair p q \<Longrightarrow> snd p \<le> snd q"
  by simp

subsection \<open>Refined backward-analysis locale\<close>

text \<open>
  Extends @{locale backward_domain} with two orthogonal strengthenings of the
  domain-author operators, bundled into one locale so a concrete domain proves
  both against a single interpretation rather than reproving @{locale
  backward_domain}'s base soundness once per strengthening:

    - Monotonicity: the generic @{term afilter} / @{term bfilter} are then
      monotone in the abstract state (and target value) by the same induction
      that proves their soundness.

    - Reductiveness: \<open>intersect\<close>'s result is below both input operands --
      refinement narrows, never enlarges. This is the only reductiveness this
      locale assumes: \<open>afilter_reductive\<close>/\<open>bfilter_reductive\<close> need it solely at
      @{term afilter}'s \<open>V\<close> case, where \<open>intersect\<close> is the sole narrowing step;
      the \<open>inv_*\<close> operators have no reductiveness assumption of their own,
      because none of the reductiveness proofs need one -- each recursive
      \<open>afilter\<close>/\<open>bfilter\<close> step is bounded by its own induction hypothesis, not
      by a per-operator shrink fact.

  Each \<open>inv_*\<close> operator's monotonicity contract is one @{const le_pair} fact
  about its returned pair rather than two separately-assumed \<open>fst\<close>/\<open>snd\<close>
  projections; the componentwise facts \<open>afilter_mono\<close>/\<open>bfilter_mono\<close>'s own
  induction needs are derived from these once, inside this locale.
\<close>

locale backward_domain_refined = backward_domain +
  assumes intersect_mono[intro]:
      "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> intersect a1 b1 \<le> intersect a2 b2"
  and aval_abs_mono[intro]:
      "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> aval_abs e \<sigma>1 \<le> aval_abs e \<sigma>2"
  and inv_less_mono:
      "x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_less res x1 y1) (inv_less res x2 y2)"
  and inv_eq_mono:
      "x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_eq res x1 y1) (inv_eq res x2 y2)"
  and inv_plus_mono:
      "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_plus r1 x1 y1) (inv_plus r2 x2 y2)"
  and inv_minus_mono:
      "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_minus r1 x1 y1) (inv_minus r2 x2 y2)"
  and inv_times_mono:
      "r1 \<le> r2 \<Longrightarrow> x1 \<le> x2 \<Longrightarrow> y1 \<le> y2 \<Longrightarrow> le_pair (inv_times r1 x1 y1) (inv_times r2 x2 y2)"
  and intersect_reductive1[intro]: "intersect a b \<le> a"
  and intersect_reductive2[intro]: "intersect a b \<le> b"
  and tobool_mono:
      "\<not> is_empty (p1::'a) \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> tobool p2 = Some (bv::bool) \<Longrightarrow> tobool p1 = Some bv"
begin


lemma afilter_Plus_unfold:
  "afilter (Plus e1 e2) a \<sigma> =
     afilter e1 (fst (inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)))
               (afilter e2 (snd (inv_plus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma afilter_Minus_unfold:
  "afilter (Minus e1 e2) a \<sigma> =
     afilter e1 (fst (inv_minus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)))
               (afilter e2 (snd (inv_minus a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma afilter_Times_unfold:
  "afilter (Times e1 e2) a \<sigma> =
     afilter e1 (fst (inv_times a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)))
               (afilter e2 (snd (inv_times a (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma bfilter_Less_unfold:
  "bfilter (Less e1 e2) res \<sigma> =
     afilter e1 (fst (inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)))
               (afilter e2 (snd (inv_less res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma bfilter_Eq_unfold:
  "bfilter (Eq e1 e2) res \<sigma> =
     afilter e1 (fst (inv_eq res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>)))
               (afilter e2 (snd (inv_eq res (aval_abs e1 \<sigma>) (aval_abs e2 \<sigma>))) \<sigma>)"
  by (simp add: Let_def case_prod_beta)

lemma afilter_mono:
  "a1 \<le> a2 \<Longrightarrow> \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> afilter e a1 \<sigma>1 \<le> afilter e a2 \<sigma>2"
proof (induction e arbitrary: a1 a2 \<sigma>1 \<sigma>2)
  case (N n)
  then show ?case by simp
next
  case (V x)
  show ?case
    unfolding afilter.simps
  proof (rule le_funI)
    fix y
    show "(\<sigma>1(x := intersect a1 (\<sigma>1 x))) y \<le> (\<sigma>2(x := intersect a2 (\<sigma>2 x))) y"
    proof (cases "y = x")
      case True
      thus ?thesis using intersect_mono[OF V.prems(1) le_funD[OF V.prems(2)]] by simp
    next
      case False thus ?thesis using le_funD[OF V.prems(2)] by simp
    qed
  qed
next
  case (Plus e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" by (rule aval_abs_mono[OF Plus.prems(2)])
  have v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2" by (rule aval_abs_mono[OF Plus.prems(2)])
  have iv: "fst (inv_plus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> fst (inv_plus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))
          \<and> snd (inv_plus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> snd (inv_plus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))"
    by (rule inv_plus_mono[OF Plus.prems(1) v1 v2])
  have step: "afilter e2 (snd (inv_plus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))) \<sigma>1
            \<le> afilter e2 (snd (inv_plus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))) \<sigma>2"
    by (rule Plus.IH(2)[OF conjunct2[OF iv] Plus.prems(2)])
  show ?case unfolding afilter_Plus_unfold
    by (rule Plus.IH(1)[OF conjunct1[OF iv] step])
next
  case (Minus e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" by (rule aval_abs_mono[OF Minus.prems(2)])
  have v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2" by (rule aval_abs_mono[OF Minus.prems(2)])
  have iv: "fst (inv_minus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> fst (inv_minus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))
          \<and> snd (inv_minus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> snd (inv_minus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))"
    by (rule inv_minus_mono[OF Minus.prems(1) v1 v2])
  have step: "afilter e2 (snd (inv_minus a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))) \<sigma>1
            \<le> afilter e2 (snd (inv_minus a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))) \<sigma>2"
    by (rule Minus.IH(2)[OF conjunct2[OF iv] Minus.prems(2)])
  show ?case unfolding afilter_Minus_unfold
    by (rule Minus.IH(1)[OF conjunct1[OF iv] step])
next
  case (Times e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" by (rule aval_abs_mono[OF Times.prems(2)])
  have v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2" by (rule aval_abs_mono[OF Times.prems(2)])
  have iv: "fst (inv_times a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> fst (inv_times a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))
          \<and> snd (inv_times a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> snd (inv_times a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))"
    by (rule inv_times_mono[OF Times.prems(1) v1 v2])
  have step: "afilter e2 (snd (inv_times a1 (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))) \<sigma>1
            \<le> afilter e2 (snd (inv_times a2 (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))) \<sigma>2"
    by (rule Times.IH(2)[OF conjunct2[OF iv] Times.prems(2)])
  show ?case unfolding afilter_Times_unfold
    by (rule Times.IH(1)[OF conjunct1[OF iv] step])
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
  Monotonicity companion to \<open>bfilter_default_sound\<close>: the same \<open>inv_eq\<close>-
  against-\<open>0\<close> reduction is monotone in \<open>\<sigma>\<close>, following directly from
  \<open>aval_abs_mono\<close>, \<open>inv_eq_mono\<close>, and \<open>afilter_mono\<close>.
\<close>
lemma bfilter_default_mono:
  assumes "\<sigma>1 \<le> \<sigma>2"
  shows "afilter e (fst (inv_eq (\<not> res) (aval_abs e \<sigma>1) (aval_abs (N 0) \<sigma>1))) \<sigma>1
       \<le> afilter e (fst (inv_eq (\<not> res) (aval_abs e \<sigma>2) (aval_abs (N 0) \<sigma>2))) \<sigma>2"
proof -
  have v1: "aval_abs e \<sigma>1 \<le> aval_abs e \<sigma>2" by (rule aval_abs_mono[OF assms])
  have v0: "aval_abs (N 0) \<sigma>1 \<le> aval_abs (N 0) \<sigma>2" by (rule aval_abs_mono[OF assms])
  have iv: "fst (inv_eq (\<not> res) (aval_abs e \<sigma>1) (aval_abs (N 0) \<sigma>1))
              \<le> fst (inv_eq (\<not> res) (aval_abs e \<sigma>2) (aval_abs (N 0) \<sigma>2))"
    using inv_eq_mono[OF v1 v0] by simp
  show ?thesis by (rule afilter_mono[OF iv assms])
qed

text \<open>
  The forward gate is monotone in the direction its call sites need: a state
  whose forward value already rules the selected polarity out cannot become
  feasible by shrinking. \<open>is_empty_antimono\<close> settles the bottom case and
  \<open>tobool_mono\<close> the definite-answer case. \<open>tobool_mono\<close> explicitly excludes
  bottom operands -- an author's \<open>tobool\<close> may answer arbitrarily there, since
  \<open>gamma bot = {}\<close> makes every answer vacuously sound -- which is why
  \<open>feasible\<close> tests \<open>is_empty\<close> first rather than relying on \<open>tobool\<close> to agree
  across a bottom/non-bottom pair.
\<close>

lemma feasible_mono:
  assumes "sigma1 \<le> sigma2" and "feasible e pol sigma1"
  shows "feasible e pol sigma2"
proof -
  have v: "aval_abs e sigma1 \<le> aval_abs e sigma2" by (rule aval_abs_mono[OF assms(1)])
  have nb1: "\<not> is_empty (aval_abs e sigma1)" using assms(2) by (simp add: feasible_def)
  have nb2: "\<not> is_empty (aval_abs e sigma2)" using nb1 is_empty_antimono[OF v] by blast
  have "tobool (aval_abs e sigma2) \<noteq> Some (\<not> pol)"
  proof
    assume "tobool (aval_abs e sigma2) = Some (\<not> pol)"
    then have "tobool (aval_abs e sigma1) = Some (\<not> pol)"
      using tobool_mono[OF nb1 v] by simp
    then show False using assms(2) by (simp add: feasible_def)
  qed
  with nb2 show ?thesis by (simp add: feasible_def)
qed

text \<open>
  Monotonicity of a single gated disjunct -- the shape \<open>bfilter\<close>'s two join
  cases need. An infeasible disjunct contributes \<open>bot\<close>, which is below
  everything; a feasible one stays feasible in the larger state.
\<close>

lemma gate_mono:
  assumes "sigma1 \<le> sigma2" and "bfilter e pol sigma1 \<le> bfilter e pol sigma2"
  shows "(if feasible e pol sigma1 then bfilter e pol sigma1 else bot)
           \<le> (if feasible e pol sigma2 then bfilter e pol sigma2 else bot)"
proof (cases "feasible e pol sigma1")
  case True
  have "feasible e pol sigma2" by (rule feasible_mono[OF assms(1) True])
  with True assms(2) show ?thesis by simp
next
  case False
  then show ?thesis by simp
qed
lemma bfilter_mono:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> bfilter b res \<sigma>1 \<le> bfilter b res \<sigma>2"
proof (induction b arbitrary: res \<sigma>1 \<sigma>2)
  case (N n) show ?case
    using bfilter_default_mono[where e = "N n" and res = res, OF N.prems]
    by (simp add: Let_def case_prod_beta)
next
  case (V x) show ?case
    using bfilter_default_mono[where e = "V x" and res = res, OF V.prems]
    by (simp add: Let_def case_prod_beta fun_upd_def)
next
  case (Plus e1 e2) show ?case
    using bfilter_default_mono[where e = "Plus e1 e2" and res = res, OF Plus.prems]
    by (simp add: Let_def case_prod_beta)
next
  case (Minus e1 e2) show ?case
    using bfilter_default_mono[where e = "Minus e1 e2" and res = res, OF Minus.prems]
    by (simp add: Let_def case_prod_beta)
next
  case (Times e1 e2) show ?case
    using bfilter_default_mono[where e = "Times e1 e2" and res = res, OF Times.prems]
    by (simp add: Let_def case_prod_beta)
next
  case (Not b) show ?case unfolding bfilter.simps by (rule Not.IH[OF Not.prems])
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    have c: "bfilter b2 True \<sigma>1 \<le> bfilter b2 True \<sigma>2" by (rule And.IH(2)[OF And.prems])
    have "bfilter b1 True (bfilter b2 True \<sigma>1) \<le> bfilter b1 True (bfilter b2 True \<sigma>2)"
      by (rule And.IH(1)[OF c])
    thus ?thesis using True by simp
  next
    case False
    have c1: "(if feasible b1 False \<sigma>1 then bfilter b1 False \<sigma>1 else bot)
                \<le> (if feasible b1 False \<sigma>2 then bfilter b1 False \<sigma>2 else bot)"
      by (rule gate_mono[OF And.prems And.IH(1)[OF And.prems]])
    have c2: "(if feasible b2 False \<sigma>1 then bfilter b2 False \<sigma>1 else bot)
                \<le> (if feasible b2 False \<sigma>2 then bfilter b2 False \<sigma>2 else bot)"
      by (rule gate_mono[OF And.prems And.IH(2)[OF And.prems]])
    have eq1: "bfilter (And b1 b2) res \<sigma>1
                 = (if feasible b1 False \<sigma>1 then bfilter b1 False \<sigma>1 else bot)
                   \<squnion> (if feasible b2 False \<sigma>1 then bfilter b2 False \<sigma>1 else bot)"
      using False by simp
    have eq2: "bfilter (And b1 b2) res \<sigma>2
                 = (if feasible b1 False \<sigma>2 then bfilter b1 False \<sigma>2 else bot)
                   \<squnion> (if feasible b2 False \<sigma>2 then bfilter b2 False \<sigma>2 else bot)"
      using False by simp
    show ?thesis unfolding eq1 eq2 by (rule sup_mono[OF c1 c2])  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    have c1: "(if feasible b1 True \<sigma>1 then bfilter b1 True \<sigma>1 else bot)
                \<le> (if feasible b1 True \<sigma>2 then bfilter b1 True \<sigma>2 else bot)"
      by (rule gate_mono[OF Or.prems Or.IH(1)[OF Or.prems]])
    have c2: "(if feasible b2 True \<sigma>1 then bfilter b2 True \<sigma>1 else bot)
                \<le> (if feasible b2 True \<sigma>2 then bfilter b2 True \<sigma>2 else bot)"
      by (rule gate_mono[OF Or.prems Or.IH(2)[OF Or.prems]])
    have eq1: "bfilter (Or b1 b2) res \<sigma>1
                 = (if feasible b1 True \<sigma>1 then bfilter b1 True \<sigma>1 else bot)
                   \<squnion> (if feasible b2 True \<sigma>1 then bfilter b2 True \<sigma>1 else bot)"
      using True by simp
    have eq2: "bfilter (Or b1 b2) res \<sigma>2
                 = (if feasible b1 True \<sigma>2 then bfilter b1 True \<sigma>2 else bot)
                   \<squnion> (if feasible b2 True \<sigma>2 then bfilter b2 True \<sigma>2 else bot)"
      using True by simp
    show ?thesis unfolding eq1 eq2 by (rule sup_mono[OF c1 c2])  next
    case False
    have c: "bfilter b2 False \<sigma>1 \<le> bfilter b2 False \<sigma>2" by (rule Or.IH(2)[OF Or.prems])
    have "bfilter b1 False (bfilter b2 False \<sigma>1) \<le> bfilter b1 False (bfilter b2 False \<sigma>2)"
      by (rule Or.IH(1)[OF c])
    thus ?thesis using False by simp
  qed
next
  case (Less e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" by (rule aval_abs_mono[OF Less.prems])
  have v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2" by (rule aval_abs_mono[OF Less.prems])
  have iv: "fst (inv_less res (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> fst (inv_less res (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))
          \<and> snd (inv_less res (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> snd (inv_less res (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))"
    by (rule inv_less_mono[OF v1 v2])
  have step: "afilter e2 (snd (inv_less res (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))) \<sigma>1
            \<le> afilter e2 (snd (inv_less res (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))) \<sigma>2"
    by (rule afilter_mono[OF conjunct2[OF iv] Less.prems])
  show ?case unfolding bfilter_Less_unfold
    by (rule afilter_mono[OF conjunct1[OF iv] step])
next
  case (Eq e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" by (rule aval_abs_mono[OF Eq.prems])
  have v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2" by (rule aval_abs_mono[OF Eq.prems])
  have iv: "fst (inv_eq res (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> fst (inv_eq res (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))
          \<and> snd (inv_eq res (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))
              \<le> snd (inv_eq res (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))"
    by (rule inv_eq_mono[OF v1 v2])
  have step: "afilter e2 (snd (inv_eq res (aval_abs e1 \<sigma>1) (aval_abs e2 \<sigma>1))) \<sigma>1
            \<le> afilter e2 (snd (inv_eq res (aval_abs e1 \<sigma>2) (aval_abs e2 \<sigma>2))) \<sigma>2"
    by (rule afilter_mono[OF conjunct2[OF iv] Eq.prems])
  show ?case unfolding bfilter_Eq_unfold
    by (rule afilter_mono[OF conjunct1[OF iv] step])
qed

text \<open>
  \<open>branch_lifted\<close>'s gate is the same \<open>feasible\<close> test \<open>bfilter\<close>'s join cases
  apply per disjunct, so its monotonicity is \<open>feasible_mono\<close> and
  \<open>bfilter_mono\<close> together. \<open>branch_mono\<close> follows: \<open>branch\<close>'s
  \<open>Bot => bot | Lifted s => s\<close> projection is itself monotone (\<open>Bot\<close> is least,
  so it can only project below whatever the \<open>Lifted\<close> side projects to).
\<close>
lemma branch_lifted_mono:
  assumes "sigma1 \<le> sigma2"
  shows "branch_lifted e pol sigma1 \<le> branch_lifted e pol sigma2"
proof (cases "feasible e pol sigma1")
  case False
  then show ?thesis by (simp add: branch_lifted_def)
next
  case True
  have "feasible e pol sigma2" by (rule feasible_mono[OF assms True])
  with True show ?thesis
    by (simp add: branch_lifted_def bfilter_mono[OF assms])
qed
lemma branch_mono:
  assumes "sigma1 \<le> sigma2"
  shows "branch e pol sigma1 \<le> branch e pol sigma2"
proof -
  have lm: "branch_lifted e pol sigma1 \<le> branch_lifted e pol sigma2"
    by (rule branch_lifted_mono[OF assms])
  show ?thesis
    unfolding branch_def
    using lm by (cases "branch_lifted e pol sigma1"; cases "branch_lifted e pol sigma2") auto
qed


text \<open>
  Reductiveness of the whole recursion, not just its individual \<open>intersect\<close>/\<open>inv_*\<close>
  steps: @{term \<open>afilter e a \<sigma>\<close>}/@{term \<open>bfilter b res \<sigma>\<close>} are always \<le> their
  input state. This is what lets a compound expression's re-narrowing of an
  already-settled location never revive it -- each recursive step only shrinks
  the state further, so once some location is @{const is_empty}, it stays
  @{const is_empty} through every later step (@{thm is_empty_state_antimono}).
\<close>

lemma afilter_reductive: "afilter e a \<sigma> \<le> \<sigma>"
proof (induction e arbitrary: a \<sigma>)
  case (V x) then show ?case by (auto simp: le_fun_def)
next
  case (Plus e1 e2) then show ?case
    unfolding afilter_Plus_unfold split_beta by (blast intro: order_trans)
next
  case (Minus e1 e2) then show ?case
    unfolding afilter_Minus_unfold split_beta by (blast intro: order_trans)
next
  case (Times e1 e2) then show ?case
    unfolding afilter_Times_unfold split_beta by (blast intro: order_trans)
qed simp_all

text \<open>
  Reductiveness companion to \<open>bfilter_default_sound\<close>: the \<open>inv_eq\<close>-against-\<open>0\<close>
  reduction is exactly an \<open>afilter\<close> call, so reductiveness falls straight out
  of \<open>afilter_reductive\<close> with no further argument.
\<close>
lemma bfilter_reductive: "bfilter b res \<sigma> \<le> \<sigma>"
proof (induction b arbitrary: res \<sigma>)
  case (N n) then show ?case
    unfolding bfilter.simps Let_def split_beta by (rule afilter_reductive)
next
  case (V x) then show ?case
    unfolding bfilter.simps Let_def split_beta by (rule afilter_reductive)
next
  case (Plus e1 e2) then show ?case
    unfolding bfilter.simps Let_def split_beta by (blast intro: afilter_reductive)
next
  case (Minus e1 e2) then show ?case
    unfolding bfilter.simps Let_def split_beta by (blast intro: afilter_reductive)
next
  case (Times e1 e2) then show ?case
    unfolding bfilter.simps Let_def split_beta by (blast intro: afilter_reductive)
next
  case (Not b)
  show ?case unfolding bfilter.simps by (rule Not.IH)
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    have c: "bfilter b2 True \<sigma> \<le> \<sigma>" by (rule And.IH(2))
    have "bfilter b1 True (bfilter b2 True \<sigma>) \<le> bfilter b2 True \<sigma>" by (rule And.IH(1))
    also have "... \<le> \<sigma>" by (rule c)
    finally show ?thesis using True by simp
  next
    case False
    have c1: "(if feasible b1 False \<sigma> then bfilter b1 False \<sigma> else bot) \<le> \<sigma>"
      using And.IH(1) by simp
    have c2: "(if feasible b2 False \<sigma> then bfilter b2 False \<sigma> else bot) \<le> \<sigma>"
      using And.IH(2) by simp
    have e1: "bfilter (And b1 b2) res \<sigma>
                = (if feasible b1 False \<sigma> then bfilter b1 False \<sigma> else bot)
                  \<squnion> (if feasible b2 False \<sigma> then bfilter b2 False \<sigma> else bot)"
      using False by simp
    show ?thesis unfolding e1 by (rule sup_least[OF c1 c2])
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    have c1: "(if feasible b1 True \<sigma> then bfilter b1 True \<sigma> else bot) \<le> \<sigma>"
      using Or.IH(1) by simp
    have c2: "(if feasible b2 True \<sigma> then bfilter b2 True \<sigma> else bot) \<le> \<sigma>"
      using Or.IH(2) by simp
    have e1: "bfilter (Or b1 b2) res \<sigma>
                = (if feasible b1 True \<sigma> then bfilter b1 True \<sigma> else bot)
                  \<squnion> (if feasible b2 True \<sigma> then bfilter b2 True \<sigma> else bot)"
      using True by simp
    show ?thesis unfolding e1 by (rule sup_least[OF c1 c2])
  next
    case False
    have c: "bfilter b2 False \<sigma> \<le> \<sigma>" by (rule Or.IH(2))
    have "bfilter b1 False (bfilter b2 False \<sigma>) \<le> bfilter b2 False \<sigma>" by (rule Or.IH(1))
    also have "... \<le> \<sigma>" by (rule c)
    finally show ?thesis using False by simp
  qed
next
  case (Less e1 e2)
  show ?case unfolding bfilter_Less_unfold
    by (rule order_trans[OF afilter_reductive afilter_reductive])
next
  case (Eq e1 e2)
  show ?case unfolding bfilter_Eq_unfold
    by (rule order_trans[OF afilter_reductive afilter_reductive])
qed

end

end
