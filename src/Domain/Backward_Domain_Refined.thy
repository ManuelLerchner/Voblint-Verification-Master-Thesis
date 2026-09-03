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
  \<open>branch\<close>'s gate is the same \<open>feasible\<close> test \<open>bfilter\<close>'s join cases apply
  per disjunct, so its monotonicity is \<open>feasible_mono\<close> and \<open>bfilter_mono\<close>
  together. \<open>branch_lifted_mono\<close> follows for free, since \<open>branch_lifted\<close> is
  definitionally \<open>branch\<close> composed with \<^const>\<open>normalize_lift\<close>
  (\<open>normalize_lift_mono\<close>, \<open>is_empty_state_antimono\<close>).
\<close>
lemma branch_mono:
  assumes "sigma1 \<le> sigma2"
  shows "branch e pol sigma1 \<le> branch e pol sigma2"
proof (cases "feasible e pol sigma1")
  case True
  have "feasible e pol sigma2" by (rule feasible_mono[OF assms True])
  with True assms show ?thesis by (simp add: branch_unfold bfilter_mono)
next
  case False
  then show ?thesis by (simp add: branch_unfold)
qed

lemma branch_lifted_mono:
  assumes "sigma1 \<le> sigma2"
  shows "branch_lifted e pol sigma1 \<le> branch_lifted e pol sigma2"
proof -
  have bm: "branch e pol sigma1 \<le> branch e pol sigma2" by (rule branch_mono[OF assms])
  have anti: "is_empty_state (branch e pol sigma2) \<Longrightarrow> is_empty_state (branch e pol sigma1)"
    by (rule is_empty_state_antimono[OF bm])
  show ?thesis unfolding branch_lifted_def by (simp add: anti bm normalize_lift_mono)
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
