theory Backward_Domain_Refined
  imports Backward_Domain
begin

section \<open>Monotone and reductive backward filtering\<close>

text \<open>
  Split out of @{theory Voblint_Domain.Backward_Domain}: the base
  \<open>backward_domain\<close> locale states filtering and its soundness alone, with no
  monotonicity or reductiveness content; this theory adds the strengthened
  \<open>backward_domain_refined\<close> locale a concrete domain interprets once it can
  supply monotone, reductive inverse operators.
\<close>

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

text \<open>
  The two strengthenings are separate locales because a domain can have one
  without the other, and the executable lifted filtering needs only the
  weaker one. Int's \<open>Refine_Fixpoint\<close> mode is exactly that case: \<open>refine\<close> is
  reductive at every mode but monotone only off \<open>Refine_Fixpoint\<close>
  (\<open>Int_Arithmetic\<close>'s \<open>refine_nonfixpoint_mono\<close>), so it interprets
  \<open>backward_domain_reductive\<close> and gets the precise, dead-arm-eliminating
  filtering, while \<open>branch_mono\<close> and the rest of the monotonicity layer stay
  out of its reach.
\<close>

locale backward_domain_reductive = backward_domain +
  assumes intersect_reductive1[intro]: "intersect a b \<le> a"
  and intersect_reductive2[intro]: "intersect a b \<le> b"
begin

text \<open>
  Reductiveness of the whole recursion, not just its individual \<open>intersect\<close>
  steps: \<^term>\<open>afilter e a \<sigma>\<close>/\<^term>\<open>bfilter b res \<sigma>\<close> are always \<open>\<le>\<close> their
  input state, so a compound expression's re-narrowing of an already-settled
  location never revives it -- once a location is \<^const>\<open>is_empty\<close> it stays
  \<^const>\<open>is_empty\<close> through every later step (@{thm is_empty_state_antimono}).
  Neither proof needs any monotonicity: \<open>afilter\<close>'s \<open>V\<close> case is bounded by
  \<open>intersect_reductive2\<close>, every compound case by its own induction hypothesis.
\<close>

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
      by (cases "feasible b1 False \<sigma>") (simp_all add: And.IH(1))
    have c2: "(if feasible b2 False \<sigma> then bfilter b2 False \<sigma> else bot) \<le> \<sigma>"
      by (cases "feasible b2 False \<sigma>") (simp_all add: And.IH(2))
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
      by (cases "feasible b1 True \<sigma>") (simp_all add: Or.IH(1))
    have c2: "(if feasible b2 True \<sigma> then bfilter b2 True \<sigma> else bot) \<le> \<sigma>"
      by (cases "feasible b2 True \<sigma>") (simp_all add: Or.IH(2))
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

text \<open>
  A witness-bottom incoming state forces \<open>bfilter_lifted\<close> to \<open>Bot\<close>
  regardless of what \<open>feasible\<close> answers: narrowing (\<open>bfilter_reductive\<close>) can
  only shrink a location, never repopulate one already empty, so whichever
  location witnessed \<open>sigma\<close>'s emptiness survives every leaf update and every
  join arm untouched. This is what lets an executable caller skip
  \<open>bfilter_st_lift\<close>'s \<open>live_resolved_st_q\<close> precondition entirely on a dead
  state: the answer is \<open>Bot\<close> either way, forward-gate false positive or not.
\<close>

lemma bfilter_lifted_witness_bottom:
  assumes "is_empty_state sigma"
  shows "bfilter_lifted e pol sigma = Bot"
using assms proof (induction e arbitrary: pol)
  case (N n)
  then show ?case by (simp add: is_empty_state_antimono[OF bfilter_reductive])
next
  case (V x)
  have "is_empty_state (bfilter (V x) pol sigma)" using is_empty_state_antimono[OF bfilter_reductive V.prems] .
  then show ?case by simp
next
  case (Plus e1 e2)
  have "is_empty_state (bfilter (Plus e1 e2) pol sigma)"
    using is_empty_state_antimono[OF bfilter_reductive Plus.prems] .
  then show ?case by simp
next
  case (Minus e1 e2)
  have "is_empty_state (bfilter (Minus e1 e2) pol sigma)"
    using is_empty_state_antimono[OF bfilter_reductive Minus.prems] .
  then show ?case by simp
next
  case (Times e1 e2)
  have "is_empty_state (bfilter (Times e1 e2) pol sigma)"
    using is_empty_state_antimono[OF bfilter_reductive Times.prems] .
  then show ?case by simp
next
  case (Less e1 e2)
  have "is_empty_state (bfilter (Less e1 e2) pol sigma)"
    using is_empty_state_antimono[OF bfilter_reductive Less.prems] .
  then show ?case by simp
next
  case (Eq e1 e2)
  have "is_empty_state (bfilter (Eq e1 e2) pol sigma)"
    using is_empty_state_antimono[OF bfilter_reductive Eq.prems] .
  then show ?case by simp
next
  case (Not b) then show ?case by simp
next
  case (And b1 b2)
  show ?case
  proof (cases pol)
    case True
    have "bfilter_lifted b2 True sigma = Bot" by (rule And.IH(2)[OF And.prems])
    then show ?thesis using True by simp
  next
    case False
    have h1: "bfilter_lifted b1 False sigma = Bot" by (rule And.IH(1)[OF And.prems])
    have h2: "bfilter_lifted b2 False sigma = Bot" by (rule And.IH(2)[OF And.prems])
    show ?thesis using False h1 h2 by simp
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases pol)
    case True
    have h1: "bfilter_lifted b1 True sigma = Bot" by (rule Or.IH(1)[OF Or.prems])
    have h2: "bfilter_lifted b2 True sigma = Bot" by (rule Or.IH(2)[OF Or.prems])
    show ?thesis using True h1 h2 by simp
  next
    case False
    have "bfilter_lifted b2 False sigma = Bot" by (rule Or.IH(2)[OF Or.prems])
    then show ?thesis using False by simp
  qed
qed

lemma branch_lifted_witness_bottom:
  assumes "is_empty_state sigma"
  shows "branch_lifted e pol sigma = Bot"
  unfolding branch_lifted_def using bfilter_lifted_witness_bottom[OF assms] by simp

lemma branch_witness_bottom:
  assumes "is_empty_state sigma"
  shows "branch e pol sigma = bot"
  unfolding branch_def using branch_lifted_witness_bottom[OF assms] by simp

end

locale backward_domain_refined = backward_domain_reductive +
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
  and tobool_mono:
      "\<not> is_empty (p1::'a) \<Longrightarrow> p1 \<le> p2 \<Longrightarrow> tobool p2 = Some (bv::bool) \<Longrightarrow> tobool p1 = Some bv"
begin

lemmas inv_less_mono_fst [intro] = inv_less_mono[THEN le_pair_fst]
lemmas inv_less_mono_snd [intro] = inv_less_mono[THEN le_pair_snd]

lemmas inv_eq_mono_fst [intro] = inv_eq_mono[THEN le_pair_fst]
lemmas inv_eq_mono_snd [intro] = inv_eq_mono[THEN le_pair_snd]

lemmas inv_plus_mono_fst [intro] = inv_plus_mono[THEN le_pair_fst]
lemmas inv_plus_mono_snd [intro] = inv_plus_mono[THEN le_pair_snd]

lemmas inv_minus_mono_fst [intro] = inv_minus_mono[THEN le_pair_fst]
lemmas inv_minus_mono_snd [intro] = inv_minus_mono[THEN le_pair_snd]

lemmas inv_times_mono_fst [intro] = inv_times_mono[THEN le_pair_fst]
lemmas inv_times_mono_snd [intro] = inv_times_mono[THEN le_pair_snd]


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
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" and v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2"
    using aval_abs_mono[OF Plus.prems(2)] by simp_all
  show ?case unfolding afilter_Plus_unfold
    using v1 v2 Plus.prems
    by (blast intro: Plus.IH)
next
  case (Minus e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" and v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2"
    using aval_abs_mono[OF Minus.prems(2)] by simp_all
  show ?case unfolding afilter_Minus_unfold
    using v1 v2 Minus.prems
    by (blast intro: Minus.IH)
next
  case (Times e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" and v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2"
    using aval_abs_mono[OF Times.prems(2)] by simp_all
  show ?case unfolding afilter_Times_unfold
    using v1 v2 Times.prems
    by (blast intro: Times.IH)
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
  Monotonicity companion to \<open>afilter_pair_sound\<close>: the same two-operand
  filtering step, once \<open>inv_less\<close>/\<open>inv_eq\<close>/\<open>inv_plus\<close>/... has narrowed the
  operand pair monotonically, is itself monotone in both the narrowed pair
  and the incoming state. Stated generically here from the completed
  \<open>afilter_mono\<close>, so it cannot help \<open>afilter_mono\<close>'s own Plus/Minus/Times
  cases -- \<open>afilter_mono\<close> is still mid-induction when they run -- but lets
  later clients such as \<open>bfilter_mono\<close>'s Less/Eq cases apply it directly
  instead of repeating this chaining.
\<close>

lemma afilter_pair_mono [intro]:
  assumes fst: "fst p1 \<le> fst p2" and snd: "snd p1 \<le> snd p2" and st: "\<sigma>1 \<le> \<sigma>2"
  shows "afilter e1 (fst p1) (afilter e2 (snd p1) \<sigma>1)
       \<le> afilter e1 (fst p2) (afilter e2 (snd p2) \<sigma>2)"
proof -
  have inner: "afilter e2 (snd p1) \<sigma>1 \<le> afilter e2 (snd p2) \<sigma>2"
    by (rule afilter_mono[OF snd st])
  show ?thesis by (rule afilter_mono[OF fst inner])
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
  \<open>bfilter\<close>'s two join cases test \<open>feasible\<close> and fall back to \<open>bot\<close> on
  failure; \<open>bfilter_lifted\<close>'s corresponding cases do the same against
  \<open>Bot\<close>. Both reduce to this one order fact, generic in the carrier: a
  monotone guard together with a monotone payload keeps the whole
  if-then-else monotone.
\<close>

lemma if_bot_mono:
  fixes x y :: "'b::order_bot"
  assumes pq: "p \<Longrightarrow> q"
      and xy: "x \<le> y"
  shows "(if p then x else bot) \<le> (if q then y else bot)"
  using assms by auto

text \<open>
  Monotonicity of a single gated disjunct -- the shape \<open>bfilter\<close>'s two join
  cases actually compute. An infeasible disjunct contributes \<open>bot\<close>, which is
  below everything; a feasible one stays feasible in the larger state, and
  the recursive monotonicity fact carries through unchanged.
\<close>

lemma gate_mono:
  assumes "sigma1 \<le> sigma2" and "bfilter e pol sigma1 \<le> bfilter e pol sigma2"
  shows "(if feasible e pol sigma1 then bfilter e pol sigma1 else bot)
           \<le> (if feasible e pol sigma2 then bfilter e pol sigma2 else bot)"
  by (rule if_bot_mono[OF feasible_mono[OF assms(1)] assms(2)])

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
    show ?thesis unfolding eq1 eq2 by (rule sup_mono[OF c1 c2])
  qed
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
    show ?thesis unfolding eq1 eq2 by (rule sup_mono[OF c1 c2])
  next
    case False
    have c: "bfilter b2 False \<sigma>1 \<le> bfilter b2 False \<sigma>2" by (rule Or.IH(2)[OF Or.prems])
    have "bfilter b1 False (bfilter b2 False \<sigma>1) \<le> bfilter b1 False (bfilter b2 False \<sigma>2)"
      by (rule Or.IH(1)[OF c])
    thus ?thesis using False by simp
  qed
next
  case (Less e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" and v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2"
    using aval_abs_mono[OF Less.prems] by simp_all
  show ?case unfolding bfilter_Less_unfold
    by (rule afilter_pair_mono[OF inv_less_mono_fst[OF v1 v2] inv_less_mono_snd[OF v1 v2]
                                  Less.prems])
next
  case (Eq e1 e2)
  have v1: "aval_abs e1 \<sigma>1 \<le> aval_abs e1 \<sigma>2" and v2: "aval_abs e2 \<sigma>1 \<le> aval_abs e2 \<sigma>2"
    using aval_abs_mono[OF Eq.prems] by simp_all
  show ?case unfolding bfilter_Eq_unfold
    by (rule afilter_pair_mono[OF inv_eq_mono_fst[OF v1 v2] inv_eq_mono_snd[OF v1 v2] Eq.prems])
qed


text \<open>
  \<open>bfilter_lifted\<close>'s two non-join shapes reduce to \<open>bfilter_mono\<close> lifted
  through \<^const>\<open>normalize_lift\<close>, exactly as \<open>branch_lifted_mono\<close> lifts
  \<open>branch_mono\<close>; the sequential \<open>And\<close>/\<open>Or\<close> cases lift @{const bind_lift}'s own
  premise (case \<open>Bot\<close> is trivial, case \<open>Lifted\<close> is the head recursion's own
  monotonicity fact). \<open>gate_lifted_mono\<close> is \<open>gate_mono\<close> restated for a single
  \<open>bfilter_lifted\<close> disjunct against \<^const>\<open>Bot\<close>, feeding the join cases the
  same shape \<open>gate_mono\<close> feeds \<open>bfilter_mono\<close>'s.
\<close>

lemma gate_lifted_mono:
  assumes "sigma1 \<le> sigma2" and "bfilter_lifted e pol sigma1 \<le> bfilter_lifted e pol sigma2"
  shows "(if feasible e pol sigma1 then bfilter_lifted e pol sigma1 else Bot)
           \<le> (if feasible e pol sigma2 then bfilter_lifted e pol sigma2 else Bot)"
  unfolding bot_lifted_eq[symmetric]
proof (rule if_bot_mono)
  show "feasible e pol sigma1 \<Longrightarrow> feasible e pol sigma2" by (rule feasible_mono[OF assms(1)])
next
  show "bfilter_lifted e pol sigma1 \<le> bfilter_lifted e pol sigma2" by (rule assms(2))
qed

lemma bfilter_lifted_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> bfilter_lifted e pol sigma1 \<le> bfilter_lifted e pol sigma2"
proof (induction e arbitrary: pol sigma1 sigma2)
  case (N n)
  show ?case
    using normalize_state_lift_mono[OF bfilter_mono[where b = "N n" and res = pol, OF N.prems]]
    by simp
next
  case (V x)
  show ?case
    using normalize_state_lift_mono[OF bfilter_mono[where b = "V x" and res = pol, OF V.prems]]
    by simp
next
  case (Plus e1 e2)
  show ?case
    using normalize_state_lift_mono[
            OF bfilter_mono[where b = "Plus e1 e2" and res = pol, OF Plus.prems]]
    by simp
next
  case (Minus e1 e2)
  show ?case
    using normalize_state_lift_mono[
            OF bfilter_mono[where b = "Minus e1 e2" and res = pol, OF Minus.prems]]
    by simp
next
  case (Times e1 e2)
  show ?case
    using normalize_state_lift_mono[
            OF bfilter_mono[where b = "Times e1 e2" and res = pol, OF Times.prems]]
    by simp
next
  case (Less e1 e2)
  show ?case
    using normalize_state_lift_mono[
            OF bfilter_mono[where b = "Less e1 e2" and res = pol, OF Less.prems]]
    by simp
next
  case (Eq e1 e2)
  show ?case
    using normalize_state_lift_mono[OF bfilter_mono[where b = "Eq e1 e2" and res = pol, OF Eq.prems]]
    by simp
next
  case (Not b) then show ?case by simp
next
  case (And b1 b2)
  show ?case
  proof (cases pol)
    case True
    have step: "bfilter_lifted b2 True sigma1 \<le> bfilter_lifted b2 True sigma2"
      by (rule And.IH(2)[OF And.prems])
    have ih1: "\<And>a b. a \<le> b \<Longrightarrow> bfilter_lifted b1 True a \<le> bfilter_lifted b1 True b"
      using And.IH(1) by simp
    show ?thesis using True by (simp add: bind_lift_mono2[OF step ih1])
  next
    case False
    have c1: "(if feasible b1 False sigma1 then bfilter_lifted b1 False sigma1 else Bot)
                \<le> (if feasible b1 False sigma2 then bfilter_lifted b1 False sigma2 else Bot)"
      by (rule gate_lifted_mono[OF And.prems And.IH(1)[OF And.prems]])
    have c2: "(if feasible b2 False sigma1 then bfilter_lifted b2 False sigma1 else Bot)
                \<le> (if feasible b2 False sigma2 then bfilter_lifted b2 False sigma2 else Bot)"
      by (rule gate_lifted_mono[OF And.prems And.IH(2)[OF And.prems]])
    have eq1: "bfilter_lifted (And b1 b2) pol sigma1
                 = (if feasible b1 False sigma1 then bfilter_lifted b1 False sigma1 else Bot)
                   \<squnion> (if feasible b2 False sigma1 then bfilter_lifted b2 False sigma1 else Bot)"
      using False by simp
    have eq2: "bfilter_lifted (And b1 b2) pol sigma2
                 = (if feasible b1 False sigma2 then bfilter_lifted b1 False sigma2 else Bot)
                   \<squnion> (if feasible b2 False sigma2 then bfilter_lifted b2 False sigma2 else Bot)"
      using False by simp
    show ?thesis unfolding eq1 eq2 by (rule sup_mono[OF c1 c2])
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases pol)
    case True
    have c1: "(if feasible b1 True sigma1 then bfilter_lifted b1 True sigma1 else Bot)
                \<le> (if feasible b1 True sigma2 then bfilter_lifted b1 True sigma2 else Bot)"
      by (rule gate_lifted_mono[OF Or.prems Or.IH(1)[OF Or.prems]])
    have c2: "(if feasible b2 True sigma1 then bfilter_lifted b2 True sigma1 else Bot)
                \<le> (if feasible b2 True sigma2 then bfilter_lifted b2 True sigma2 else Bot)"
      by (rule gate_lifted_mono[OF Or.prems Or.IH(2)[OF Or.prems]])
    have eq1: "bfilter_lifted (Or b1 b2) pol sigma1
                 = (if feasible b1 True sigma1 then bfilter_lifted b1 True sigma1 else Bot)
                   \<squnion> (if feasible b2 True sigma1 then bfilter_lifted b2 True sigma1 else Bot)"
      using True by simp
    have eq2: "bfilter_lifted (Or b1 b2) pol sigma2
                 = (if feasible b1 True sigma2 then bfilter_lifted b1 True sigma2 else Bot)
                   \<squnion> (if feasible b2 True sigma2 then bfilter_lifted b2 True sigma2 else Bot)"
      using True by simp
    show ?thesis unfolding eq1 eq2 by (rule sup_mono[OF c1 c2])
  next
    case False
    have step: "bfilter_lifted b2 False sigma1 \<le> bfilter_lifted b2 False sigma2"
      by (rule Or.IH(2)[OF Or.prems])
    have ih1: "\<And>a b. a \<le> b \<Longrightarrow> bfilter_lifted b1 False a \<le> bfilter_lifted b1 False b"
      using Or.IH(1) by simp
    show ?thesis using False by (simp add: bind_lift_mono2[OF step ih1])
  qed
qed

lemma branch_lifted_mono:
  assumes "sigma1 \<le> sigma2"
  shows "branch_lifted e pol sigma1 \<le> branch_lifted e pol sigma2"
proof (cases "feasible e pol sigma1")
  case True
  have "feasible e pol sigma2" by (rule feasible_mono[OF assms True])
  with True assms show ?thesis
    unfolding branch_lifted_def by (simp add: bfilter_lifted_mono)
next
  case False
  then show ?thesis unfolding branch_lifted_def by simp
qed

lemma branch_mono:
  assumes "sigma1 \<le> sigma2"
  shows "branch e pol sigma1 \<le> branch e pol sigma2"
  unfolding branch_def
  by (rule collapse_lift_mono[OF branch_lifted_mono[OF assms]])

text \<open>
  \<open>bfilter_lifted\<close> only ever narrows further than raw \<open>bfilter\<close>: each leaf
  either falls through to \<open>bfilter\<close> unchanged or short-circuits to \<open>Bot\<close>,
  and every \<open>And\<close>/\<open>Or\<close> recursion step preserves that ordering by
  \<open>bfilter_lifted_mono\<close>. \<open>branch_le_bfilter\<close> transports this to the
  collapsed carrier: callers that only need an upper bound on \<open>branch\<close>'s
  result -- e.g. post-fixpoint checks -- can reuse their existing
  \<open>bfilter\<close>-level reasoning through it instead of re-deriving one against
  \<open>branch\<close>'s definition.
\<close>

lemma bfilter_lifted_le_raw: "bfilter_lifted e pol sigma \<le> Lifted (bfilter e pol sigma)"
proof (induction e arbitrary: pol sigma)
  case (N n) then show ?case by (cases "is_empty_state (bfilter (N n) pol sigma)") simp_all
next
  case (V x) then show ?case by (cases "is_empty_state (bfilter (V x) pol sigma)") simp_all
next
  case (Plus e1 e2)
  then show ?case by (cases "is_empty_state (bfilter (Plus e1 e2) pol sigma)") simp_all
next
  case (Minus e1 e2)
  then show ?case by (cases "is_empty_state (bfilter (Minus e1 e2) pol sigma)") simp_all
next
  case (Times e1 e2)
  then show ?case by (cases "is_empty_state (bfilter (Times e1 e2) pol sigma)") simp_all
next
  case (Less e1 e2)
  then show ?case by (cases "is_empty_state (bfilter (Less e1 e2) pol sigma)") simp_all
next
  case (Eq e1 e2)
  then show ?case by (cases "is_empty_state (bfilter (Eq e1 e2) pol sigma)") simp_all
next
  case (Not b) then show ?case by simp
next
  case (And b1 b2)
  show ?case
  proof (cases pol)
    case True
    show ?thesis
    proof (cases "bfilter_lifted b2 True sigma")
      case Bot
      then show ?thesis using True by simp
    next
      case (Lifted t)
      have le_t: "t \<le> bfilter b2 True sigma"
        using And.IH(2)[of True sigma] Lifted by simp
      have "bfilter_lifted b1 True t \<le> bfilter_lifted b1 True (bfilter b2 True sigma)"
        by (rule bfilter_lifted_mono[OF le_t])
      also have "\<dots> \<le> Lifted (bfilter b1 True (bfilter b2 True sigma))"
        using And.IH(1)[of True "bfilter b2 True sigma"] by simp
      finally show ?thesis using True Lifted by simp
    qed
  next
    case False
    have c1: "(if feasible b1 False sigma then bfilter_lifted b1 False sigma else Bot)
                \<le> Lifted (if feasible b1 False sigma then bfilter b1 False sigma else bot)"
      using And.IH(1)[of False sigma] by simp
    have c2: "(if feasible b2 False sigma then bfilter_lifted b2 False sigma else Bot)
                \<le> Lifted (if feasible b2 False sigma then bfilter b2 False sigma else bot)"
      using And.IH(2)[of False sigma] by simp
    have "(if feasible b1 False sigma then bfilter_lifted b1 False sigma else Bot)
            \<squnion> (if feasible b2 False sigma then bfilter_lifted b2 False sigma else Bot)
          \<le> Lifted (if feasible b1 False sigma then bfilter b1 False sigma else bot)
              \<squnion> Lifted (if feasible b2 False sigma then bfilter b2 False sigma else bot)"
      by (rule sup_mono[OF c1 c2])
    also have "\<dots> = Lifted (bfilter (And b1 b2) False sigma)" by simp
    finally have result: "bfilter_lifted (And b1 b2) False sigma \<le> Lifted (bfilter (And b1 b2) False sigma)"
      by simp
    have pol_eq: "pol = False" using False by simp
    show ?thesis unfolding pol_eq by (rule result)
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases pol)
    case True
    have c1: "(if feasible b1 True sigma then bfilter_lifted b1 True sigma else Bot)
                \<le> Lifted (if feasible b1 True sigma then bfilter b1 True sigma else bot)"
      using Or.IH(1)[of True sigma] by simp
    have c2: "(if feasible b2 True sigma then bfilter_lifted b2 True sigma else Bot)
                \<le> Lifted (if feasible b2 True sigma then bfilter b2 True sigma else bot)"
      using Or.IH(2)[of True sigma] by simp
    have "(if feasible b1 True sigma then bfilter_lifted b1 True sigma else Bot)
            \<squnion> (if feasible b2 True sigma then bfilter_lifted b2 True sigma else Bot)
          \<le> Lifted (if feasible b1 True sigma then bfilter b1 True sigma else bot)
              \<squnion> Lifted (if feasible b2 True sigma then bfilter b2 True sigma else bot)"
      by (rule sup_mono[OF c1 c2])
    also have "\<dots> = Lifted (bfilter (Or b1 b2) True sigma)" by simp
    finally have result: "bfilter_lifted (Or b1 b2) True sigma \<le> Lifted (bfilter (Or b1 b2) True sigma)"
      by simp
    have pol_eq: "pol = True" using True by simp
    show ?thesis unfolding pol_eq by (rule result)
  next
    case False
    show ?thesis
    proof (cases "bfilter_lifted b2 False sigma")
      case Bot
      then show ?thesis using False by simp
    next
      case (Lifted t)
      have le_t: "t \<le> bfilter b2 False sigma"
        using Or.IH(2)[of False sigma] Lifted by simp
      have "bfilter_lifted b1 False t \<le> bfilter_lifted b1 False (bfilter b2 False sigma)"
        by (rule bfilter_lifted_mono[OF le_t])
      also have "\<dots> \<le> Lifted (bfilter b1 False (bfilter b2 False sigma))"
        using Or.IH(1)[of False "bfilter b2 False sigma"] by simp
      finally show ?thesis using False Lifted by simp
    qed
  qed
qed

lemma branch_lifted_le_raw: "branch_lifted e pol sigma \<le> Lifted (bfilter e pol sigma)"
  unfolding branch_lifted_def
  by (cases "feasible e pol sigma") (simp_all add: bfilter_lifted_le_raw)

lemma branch_le_bfilter: "branch e pol sigma \<le> bfilter e pol sigma"
  unfolding branch_def
  using collapse_lift_mono[OF branch_lifted_le_raw] by simp

end

end
