theory Sign_Backward
  imports Sign_Arithmetic Exec_Backward "Voblint_Domain.Abstract_Numeric_Queries"
begin

section \<open>Sign backward filtering\<close>

subsection \<open>Meet (greatest lower bound)\<close>

text \<open>
  The seven-element sign lattice has a well-defined glb.  Adding @{class semilattice_inf}
  here gives @{text \<open>inf_mono\<close>} for free, which is needed for the monotonicity proof
  of @{text bfilter}.
\<close>

fun meet_sign :: "sign => sign => sign" where
    "meet_sign SBot    _       = SBot"
  | "meet_sign _       SBot    = SBot"
  | "meet_sign STop    b       = b"
  | "meet_sign a       STop    = a"
  | "meet_sign SNeg    SNeg    = SNeg"
  | "meet_sign SNeg    SNonPos = SNeg"
  | "meet_sign SNonPos SNeg    = SNeg"
  | "meet_sign SNonPos SNonPos = SNonPos"
  | "meet_sign SNonPos SZero   = SZero"
  | "meet_sign SZero   SNonPos = SZero"
  | "meet_sign SNonPos SNonNeg = SZero"
  | "meet_sign SNonNeg SNonPos = SZero"
  | "meet_sign SZero   SZero   = SZero"
  | "meet_sign SZero   SNonNeg = SZero"
  | "meet_sign SNonNeg SZero   = SZero"
  | "meet_sign SNonNeg SNonNeg = SNonNeg"
  | "meet_sign SNonNeg SPos    = SPos"
  | "meet_sign SPos    SNonNeg = SPos"
  | "meet_sign SPos    SPos    = SPos"
  | "meet_sign _       _       = SBot"

lemma meet_sign_sound:
  "n \<in> gamma_sign a \<Longrightarrow> n \<in> gamma_sign b \<Longrightarrow> n \<in> gamma_sign (meet_sign a b)"
  by (cases a; cases b; auto)

instantiation sign :: inf begin
definition inf_sign :: "sign => sign => sign" where
  "inf_sign = meet_sign"
instance ..
end

declare inf_sign_def [simp]

instance sign :: semilattice_inf
proof intro_classes
  fix x y z :: sign
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y; auto simp: less_eq_sign_def)
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y; auto simp: less_eq_sign_def)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z; auto simp: less_eq_sign_def)
qed

instance sign :: lattice ..
instance sign :: bounded_lattice_bot ..

subsection \<open>Backward-analysis: inverse operators\<close>

text \<open>
  Per the backward-domain plan, @{text inv_less_sign} provides sign-specific
  refinement when a guard @{text "e1 < e2"} is known true or false. Plus/minus/times
  are too coarse for useful arithmetic inversion in sign, so they instantiate the
  shared @{const inv_conservative} (identity) instead of a per-domain no-op; the
  structural bfilter propagation (And/Or/Not/Eq) is where sign gains.
\<close>

fun inv_less_sign :: "bool => sign => sign => sign * sign" where
    "inv_less_sign True  a1 a2 =
       (let a1' = if sign_le a2 SNonPos then meet_sign a1 SNeg else a1 ;
                a2' = if sign_le a1 SNonNeg then meet_sign a2 SPos else a2
        in (a1', a2'))"
  | "inv_less_sign False a1 a2 =
       (let a1' = if sign_le a2 SPos then meet_sign a1 SPos
                  else if sign_le a2 SNonNeg then meet_sign a1 SNonNeg
                  else a1 ;
                a2' = if sign_le a1 SNeg then meet_sign a2 SNeg
                  else if sign_le a1 SNonPos then meet_sign a2 SNonPos
                  else a2
        in (a1', a2'))"

lemma inv_less_sign_sound:
  "n1 \<in> gamma_sign a1 \<Longrightarrow> n2 \<in> gamma_sign a2 \<Longrightarrow> (n1 < n2) = res
   \<Longrightarrow> n1 \<in> gamma_sign (fst (inv_less_sign res a1 a2))
     \<and> n2 \<in> gamma_sign (snd (inv_less_sign res a1 a2))"
  by (cases res; cases a1; cases a2;
      auto simp: less_eq_sign_def; linarith)

text \<open>
  @{text inv_eq_sign} narrows on a guard @{text \<open>e1 = e2\<close>} known true or
  false. The true branch narrows both operands to their intersection, exactly
  matching what \<open>bfilter\<close> already computes for @{text \<open>Eq _ _ True\<close>}
  via @{const meet_sign} directly. The false branch only narrows a boundary
  singleton away from a wider operand that has @{const SZero} as one of its
  bounds: excluding @{text 0} from @{const SNonNeg} leaves @{const SPos},
  from @{const SNonPos} leaves @{const SNeg}; both directions, symmetric in
  which operand is at most @{const SZero}. Two jointly-at-most-@{const SZero}
  operands are jointly unreachable. Every other pair --- including any pair
  where the excluded value would not sit at a representable lattice boundary
  --- passes through unchanged: the seven-element lattice cannot express
  \"nonzero\" or an interior exclusion as a single value.

  The guard tests @{term \<open>sign_le a SZero\<close>} (the set @{term \<open>{SBot, SZero}\<close>}),
  not literal equality @{term \<open>a = SZero\<close>}: @{const SBot} is strictly below
  @{const SZero}, so an equality guard would let a wider input at @{const
  SZero} trigger narrowing that a strictly more precise input at @{const
  SBot} would not --- a genuine monotonicity failure, not merely a missed
  precision opportunity. The order-based guard closes that gap the same way
  @{const inv_less_sign}'s own @{term \<open>sign_le a2 SNonPos\<close>}-style guards do;
  it also makes the @{const SBot} case sound for free (vacuously, since
  @{term \<open>gamma_sign SBot = {}\<close>}), without @{const inv_less_sign}'s separate
  reliance on @{text \<open>meet_sign SBot _ = SBot\<close>}.
\<close>

fun inv_eq_sign :: "bool => sign => sign => sign * sign" where
    "inv_eq_sign True  a1 a2 = (meet_sign a1 a2, meet_sign a1 a2)"
  | "inv_eq_sign False a1 a2 =
       (let a1' = if sign_le a1 SZero \<and> sign_le a2 SZero then SBot
                  else if sign_le a2 SZero \<and> sign_le a1 SNonNeg then meet_sign a1 SPos
                  else if sign_le a2 SZero \<and> sign_le a1 SNonPos then meet_sign a1 SNeg
                  else a1 ;
                a2' = if sign_le a1 SZero \<and> sign_le a2 SZero then SBot
                  else if sign_le a1 SZero \<and> sign_le a2 SNonNeg then meet_sign a2 SPos
                  else if sign_le a1 SZero \<and> sign_le a2 SNonPos then meet_sign a2 SNeg
                  else a2
        in (a1', a2'))"

lemma inv_eq_sign_sound:
  "n1 \<in> gamma_sign a1 \<Longrightarrow> n2 \<in> gamma_sign a2 \<Longrightarrow> (n1 = n2) = res
   \<Longrightarrow> n1 \<in> gamma_sign (fst (inv_eq_sign res a1 a2))
     \<and> n2 \<in> gamma_sign (snd (inv_eq_sign res a1 a2))"
proof (cases res)
  case True
  assume h1: "n1 \<in> gamma_sign a1" and h2: "n2 \<in> gamma_sign a2"
    and heq: "(n1 = n2) = res"
  have "n1 = n2" using heq True by simp
  then have "n1 \<in> gamma_sign a2" using h2 by simp
  then have "n1 \<in> gamma_sign (meet_sign a1 a2)"
    using meet_sign_sound[OF h1] by simp
  then show ?thesis using True \<open>n1 = n2\<close> by simp
next
  case False
  assume h1: "n1 \<in> gamma_sign a1" and h2: "n2 \<in> gamma_sign a2"
    and heq: "(n1 = n2) = res"
  have hne: "n1 \<noteq> n2" using heq False by simp
  show ?thesis
    using h1 h2 hne False
    by (cases a1; cases a2;
        auto simp: less_eq_sign_def Let_def)
qed

lemma meet_sign_mono:
  assumes "x \<le> x'" and "y \<le> y'"
  shows "meet_sign x y \<le> meet_sign x' y'"
  using assms
  by (metis inf_mono inf_sign_def)

text \<open>
  Reductiveness: @{const meet_sign} is exactly @{term "(\<sqinter>)"} for @{typ sign}
  (@{thm inf_sign_def}), so it never enlarges either operand.
\<close>

lemma meet_sign_le1: "meet_sign a b \<le> a"
  by (cases a; cases b; auto simp: less_eq_sign_def)

lemma meet_sign_le2: "meet_sign a b \<le> b"
  by (cases a; cases b; auto simp: less_eq_sign_def)

lemma sbot_le: "SBot \<le> (a :: sign)"
  by (cases a; auto simp: less_eq_sign_def)

text \<open>
  @{const inv_less_sign} only ever narrows an operand via @{const meet_sign} or
  passes it through unchanged, so it is reductive in both components. Each branch
  applies @{const meet_sign} with the bounded operand in either argument position
  (e.g. \<open>meet_sign a1 SNeg\<close> for the first component, \<open>meet_sign a2 SPos\<close> for the
  second), so both @{thm meet_sign_le1} and @{thm meet_sign_le2} are needed.
\<close>

lemma inv_less_sign_reductive1: "fst (inv_less_sign res a1 a2) \<le> a1"
  by (cases res; auto simp: Let_def meet_sign_le1 meet_sign_le2 split: if_splits)

lemma inv_less_sign_reductive2: "snd (inv_less_sign res a1 a2) \<le> a2"
  by (cases res; auto simp: Let_def meet_sign_le1 meet_sign_le2 split: if_splits)

text \<open>
  @{const inv_eq_sign} narrows via @{const meet_sign}, collapses to @{const SBot}
  (below every operand, @{thm sbot_le}), or passes an operand through unchanged.
\<close>

lemma inv_eq_sign_reductive1: "fst (inv_eq_sign res a1 a2) \<le> a1"
  by (cases res; auto simp: Let_def meet_sign_le1 meet_sign_le2 sbot_le split: if_splits)

lemma inv_eq_sign_reductive2: "snd (inv_eq_sign res a1 a2) \<le> a2"
  by (cases res; auto simp: Let_def meet_sign_le1 meet_sign_le2 sbot_le split: if_splits)

lemma inv_eq_sign_false_fst_mono:
  assumes "a1 \<le> (a1' :: sign)" and "a2 \<le> a2'"
  shows
    "fst (inv_eq_sign False a1 a2)
      \<le> fst (inv_eq_sign False a1' a2')"
  using assms
  by (auto simp only: inv_eq_sign.simps Let_def fst_conv snd_conv meet_sign_mono)
     (smt (verit, ccfv_SIG)
        gamma_sign.cases inf_sign_def inf_sup_ord(2)
        join_sign.simps(4) join_sign_ub2 le_infI1 less_eq_sign_def
        meet_sign.simps(19,21,31,33) order_eq_refl
        sign_le.simps(18,24,36,40,42) sign_le_trans)

lemma inv_eq_sign_false_snd_mono:
  assumes "a1 \<le> (a1' :: sign)" and "a2 \<le> a2'"
  shows
    "snd (inv_eq_sign False a1 a2)
      \<le> snd (inv_eq_sign False a1' a2')"
  using assms
  by (auto simp only: inv_eq_sign.simps Let_def fst_conv snd_conv meet_sign_mono)
     (smt (verit, best)
        bot.extremum bot_sign_def less_eq_sign_def
        meet_sign.simps(19,21,31,33) order_eq_refl sign.exhaust
        sign_le.simps(9,16,19,36,40,42) sign_le_trans)

lemma inv_eq_sign_mono:
  assumes "a1 \<le> (a1' :: sign)"
      and "a2 \<le> a2'"
  shows
    "fst (inv_eq_sign r a1 a2) \<le> fst (inv_eq_sign r a1' a2') \<and>
     snd (inv_eq_sign r a1 a2) \<le> snd (inv_eq_sign r a1' a2')"
  apply (cases r)
  using assms inv_eq_sign_false_fst_mono inv_eq_sign_false_snd_mono 
  by (auto simp add: meet_sign_mono)

text \<open>
  Monotonicity of @{const inv_less_sign} needs a case split on both the guard's
  truth value and which side of the shared narrowing threshold each operand sits;
  \<open>narrow1_mono\<close>/\<open>narrow2_mono\<close> factor the \<open>if\<close>-cascade shape common to both
  branches so the case split is done once, generically in a
  @{class semilattice_inf} operand, rather than twice inline.
\<close>

lemma sign_le_iff:
  "sign_le a b \<longleftrightarrow> a \<le> b"
  by (cases a; cases b; auto simp: less_eq_sign_def)

lemma narrow1_mono:
  fixes x x' y y' c d :: "'a::semilattice_inf"
  assumes xx': "x \<le> x'"
      and yy': "y \<le> y'"
  shows
    "(if y \<le> c then x \<sqinter> d else x)
      \<le> (if y' \<le> c then x' \<sqinter> d else x')"
  using xx' yy' inf_mono
  by auto

lemma narrow2_mono:
  fixes x x' y y' c1 c2 :: "'a::semilattice_inf"
  assumes xx': "x \<le> x'"
      and yy': "y \<le> y'"
      and cc': "c1 \<le> c2"
  shows
    "(if y \<le> c1 then x \<sqinter> c1
      else if y \<le> c2 then x \<sqinter> c2
      else x)
      \<le>
     (if y' \<le> c1 then x' \<sqinter> c1
      else if y' \<le> c2 then x' \<sqinter> c2
      else x')"
  using xx' yy' cc' inf_mono
  by (auto simp add: inf.coboundedI1 inf.coboundedI2)

lemma inv_less_sign_mono:
  assumes A1: "a1 \<le> (a1' :: sign)"
      and A2: "a2 \<le> a2'"
  shows
    "fst (inv_less_sign r a1 a2)
       \<le> fst (inv_less_sign r a1' a2') \<and>
     snd (inv_less_sign r a1 a2)
       \<le> snd (inv_less_sign r a1' a2')"
proof (cases r)
  case True

  have fst_mono:
    "(if a2 \<le> SNonPos then a1 \<sqinter> SNeg else a1)
      \<le>
     (if a2' \<le> SNonPos then a1' \<sqinter> SNeg else a1')"
    using narrow1_mono[OF A1 A2, of SNonPos SNeg] .

  have snd_mono:
    "(if a1 \<le> SNonNeg then a2 \<sqinter> SPos else a2)
      \<le>
     (if a1' \<le> SNonNeg then a2' \<sqinter> SPos else a2')"
    using narrow1_mono[OF A2 A1, of SNonNeg SPos] .

  show ?thesis
    using fst_mono snd_mono True sign_le_iff
    by auto
next
  case False

  have pos_order: "(SPos :: sign) \<le> SNonNeg"
    by (simp add: less_eq_sign_def)

  have neg_order: "(SNeg :: sign) \<le> SNonPos"
    by (simp add: less_eq_sign_def)

  have fst_mono:
    "(if a2 \<le> SPos then a1 \<sqinter> SPos
      else if a2 \<le> SNonNeg then a1 \<sqinter> SNonNeg
      else a1)
      \<le>
     (if a2' \<le> SPos then a1' \<sqinter> SPos
      else if a2' \<le> SNonNeg then a1' \<sqinter> SNonNeg
      else a1')"
    using narrow2_mono[OF A1 A2, of SPos SNonNeg] pos_order by simp

  have snd_mono:
    "(if a1 \<le> SNeg then a2 \<sqinter> SNeg
      else if a1 \<le> SNonPos then a2 \<sqinter> SNonPos
      else a2)
      \<le>
     (if a1' \<le> SNeg then a2' \<sqinter> SNeg
      else if a1' \<le> SNonPos then a2' \<sqinter> SNonPos
      else a2')"
    using narrow2_mono[OF A2 A1, of SNeg SNonPos] neg_order by simp

  show ?thesis
    using fst_mono snd_mono False sign_le_iff
    by fastforce
qed

subsection \<open>Backward-domain interpretation\<close>

text \<open>
  One interpretation discharges soundness, monotonicity, and reductiveness
  together against @{locale backward_domain_refined} -- each \<open>inv_*\<close>'s
  mono/reductive obligation is one @{const le_pair} fact, transparent notation for
  the componentwise \<open>\<and>\<close> the per-operator lemmas above already prove, so no
  bridging step is needed at any of these call sites.
\<close>

global_interpretation sign_backward_domain:
    backward_domain_refined meet_sign aval_sign sign_tobool
                    inv_less_sign inv_eq_sign inv_conservative inv_conservative inv_conservative
  defines
    afilter_sign = sign_backward_domain.afilter
    and feasible_sign = sign_backward_domain.feasible
    and bfilter_sign = sign_backward_domain.bfilter
    and branch_sign = sign_backward_domain.branch
    and branch_lifted_sign = sign_backward_domain.branch_lifted
    and afilter_sign_st = sign_backward_domain.afilter_st
    and bfilter_sign_st = sign_backward_domain.bfilter_st
    and branch_sign_st = sign_backward_domain.branch_st
    and sign_less_true_of_inv = sign_backward_domain.less_true
    and sign_less_false_of_inv = sign_backward_domain.less_false
    and sign_eq_true_of_less = sign_backward_domain.eq_true
    and sign_eq_false_of_intersection = sign_backward_domain.eq_false
proof unfold_locales
  fix n :: int and a b :: sign
  assume H1: "n \<in> gamma a" and H2: "n \<in> gamma b"
  show "n \<in> gamma (meet_sign a b)"
    using meet_sign_sound[of n a b] H1 H2 by simp
next
  fix s :: store and e :: exp and \<sigma> :: "vname \<Rightarrow> sign"
  assume H: "\<forall>x. s x \<in> gamma (\<sigma> x)"
  show "aval e s \<in> gamma (aval_sign e \<sigma>)"
    using aval_sign_sound[of s \<sigma> e] H by simp
next
  fix n1 n2 :: int and a1 a2 :: sign and res :: bool
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "(n1 < n2) = res"
  show "n1 \<in> gamma (fst (inv_less_sign res a1 a2)) \<and> n2 \<in> gamma (snd (inv_less_sign res a1 a2))"
    using inv_less_sign_sound[of n1 a1 n2 a2 res] H1 H2 H3 by simp
next
  fix n1 n2 :: int and a1 a2 :: sign and res :: bool
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "(n1 = n2) = res"
  show "n1 \<in> gamma (fst (inv_eq_sign res a1 a2)) \<and> n2 \<in> gamma (snd (inv_eq_sign res a1 a2))"
    using inv_eq_sign_sound[of n1 a1 n2 a2 res] H1 H2 H3 by simp
next
  fix n1 n2 :: int and a1 a2 r :: sign
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 + n2 \<in> gamma r"
  show "n1 \<in> gamma (fst (inv_conservative r a1 a2)) \<and> n2 \<in> gamma (snd (inv_conservative r a1 a2))"
    using inv_conservative_sound[OF H1 H2] .
next
  fix n1 n2 :: int and a1 a2 r :: sign
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 - n2 \<in> gamma r"
  show "n1 \<in> gamma (fst (inv_conservative r a1 a2)) \<and> n2 \<in> gamma (snd (inv_conservative r a1 a2))"
    using inv_conservative_sound[OF H1 H2] .
next
  fix n1 n2 :: int and a1 a2 r :: sign
  assume H1: "n1 \<in> gamma a1" and H2: "n2 \<in> gamma a2" and H3: "n1 * n2 \<in> gamma r"
  show "n1 \<in> gamma (fst (inv_conservative r a1 a2)) \<and> n2 \<in> gamma (snd (inv_conservative r a1 a2))"
    using inv_conservative_sound[OF H1 H2] .
next
  fix p :: sign and b :: bool and i :: int
  assume "sign_tobool p = Some b" and "i \<in> gamma p"
  then show "truthy i = b" using sign_tobool_sound by simp
next
  fix a1 a2 b1 b2 :: sign
  assume "a1 \<le> a2" and "b1 \<le> b2"
  thus "meet_sign a1 b1 \<le> meet_sign a2 b2" using inf_mono[of a1 a2 b1 b2] by simp
next
  fix e :: exp and \<sigma>1 \<sigma>2 :: "vname \<Rightarrow> sign"
  assume "\<sigma>1 \<le> \<sigma>2"
  thus "aval_sign e \<sigma>1 \<le> aval_sign e \<sigma>2" by (rule aval_sign_mono)
next
  fix x1 x2 y1 y2 :: sign and res :: bool
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  show "le_pair (inv_less_sign res x1 y1) (inv_less_sign res x2 y2)"
    using inv_less_sign_mono[OF A B] by (simp add: le_pair_def)
next
  fix x1 x2 y1 y2 :: sign and res :: bool
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  show "le_pair (inv_eq_sign res x1 y1) (inv_eq_sign res x2 y2)"
    using inv_eq_sign_mono[OF A B] by (simp add: le_pair_def)
next
  fix r1 r2 x1 x2 y1 y2 :: sign
  assume A: "x1 \<le> x2" and B: "y1 \<le> y2"
  show "le_pair (inv_conservative r1 x1 y1) (inv_conservative r2 x2 y2)"
    using A B by (simp add: inv_conservative_def le_pair_def)
next
  fix a b :: sign
  show "meet_sign a b \<le> a" by (rule meet_sign_le1)
next
  fix a b :: sign
  show "meet_sign a b \<le> b" by (rule meet_sign_le2)
next
  fix res :: bool and a1 a2 :: sign
  show "le_pair (inv_less_sign res a1 a2) (a1, a2)"
    using inv_less_sign_reductive1 inv_less_sign_reductive2 by (simp add: le_pair_def)
next
  fix res :: bool and a1 a2 :: sign
  show "le_pair (inv_eq_sign res a1 a2) (a1, a2)"
    using inv_eq_sign_reductive1 inv_eq_sign_reductive2 by (simp add: le_pair_def)
next
  fix r a1 a2 :: sign
  show "le_pair (inv_conservative r a1 a2) (a1, a2)"
    by (simp add: inv_conservative_def le_pair_def)
next
  fix p1 p2 :: sign and bv :: bool
  assume "\<not> is_bot p1" and "p1 \<le> p2" and "sign_tobool p2 = Some bv"
  then show "sign_tobool p1 = Some bv" using sign_tobool_mono by simp
qed

text \<open>
  Executable @{typ "sign resolved_st_q"} mirror of \<open>afilter_sign\<close> /
  \<open>bfilter_sign\<close>, and \<open>bfilter_sign\<close>'s commutation with the abstract filter
  through @{const fun_of_resolved_st_q_for}. Both come from the generic
  @{locale backward_domain} executable mirror (\<open>Exec_Backward\<close>); no Sign-level
  caller needs the \<open>afilter_st\<close> commutation on its own (only \<open>bfilter_st\<close>'s
  is used, by \<open>branch_sign_st_for\<close>), so it stays reachable
  as \<open>sign_backward_domain.afilter_st_commute\<close> without a short alias here.
\<close>

lemmas bfilter_sign_st_commute = sign_backward_domain.bfilter_st_commute
lemmas branch_sign_st_commute = sign_backward_domain.branch_st_commute

text \<open>
  \<open>sign_eq_true_of_less\<close> sits two \<open>sublocale\<close> layers below \<open>backward_domain\<close>
  (\<open>backward_domain \<subseteq> derived_less_queries \<subseteq> derived_eq_true_from_less\<close>), one
  layer deeper than \<open>sign_less_true_of_inv\<close>/\<open>sign_less_false_of_inv\<close> or
  \<open>sign_eq_false_of_intersection\<close>. The automatic code-equation chain the \<open>defines\<close>
  clause above sets up does not reach that deep, so this restates the
  definition explicitly in terms of the already-executable
  \<open>sign_less_false_of_inv\<close>, tagged \<open>[code]\<close> directly.
\<close>

lemma sign_eq_true_of_less_code [code]:
  "sign_eq_true_of_less a b = (sign_less_false_of_inv a b \<and> sign_less_false_of_inv b a)"
  using sign_backward_domain.eq_true_def sign_eq_true_of_less_def sign_less_false_of_inv_def
  by auto

subsection \<open>Abstract branch\<close>

text \<open>
  Guard refinement via backward evaluation. @{const bfilter_sign} narrows the
  abstract state on the branch selected by its boolean polarity argument
  (@{text True} for the then-branch, @{text False} for the else-branch),
  delegating to the generic @{text bfilter} proved sound in @{locale backward_domain}.
  This is the domain's @{text tf_branch} instance directly (@{text Sign_Transfer.thy}),
  matching Goblint's single polarity-parametrized @{text Spec.branch}.
\<close>

lemma bfilter_sign_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>bfilter_sign b res \<sigma>\<rbrakk>"
  using sign_backward_domain.bfilter_sound by simp

text \<open>
  @{const branch_sign} is Sign's \<open>tf_branch\<close> instance: a forward
  @{const sign_tobool} feasibility check ahead of @{const bfilter_sign},
  matching Goblint's \<open>Base.branch\<close> structure. Proved once, generically, as
  @{thm [source] backward_domain.branch_sound}.
\<close>

lemma branch_sign_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>branch_sign b res \<sigma>\<rbrakk>"
  using sign_backward_domain.branch_sound by simp


lemma afilter_sign_mono:
  "a1 \<le> (a2::sign) \<Longrightarrow> sigma1 \<le> sigma2 \<Longrightarrow>
   afilter_sign e a1 sigma1 \<le> afilter_sign e a2 sigma2"
  using sign_backward_domain.afilter_mono by (simp add: afilter_sign_def)

lemma bfilter_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> bfilter_sign b res sigma1 \<le> bfilter_sign b res sigma2"
  using sign_backward_domain.bfilter_mono by (simp add: bfilter_sign_def)

lemma branch_sign_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> branch_sign b res sigma1 \<le> branch_sign b res sigma2"
  using sign_backward_domain.branch_mono by (simp add: branch_sign_def)

subsection \<open>Executable equality-narrowing tests\<close>

text \<open>
  Representative @{const inv_eq_sign} cases, directly matching the behavioral
  examples from the design: the true branch always meets, and the false
  branch narrows exactly when one operand is exactly @{term SZero} and the
  other's sign bounds it away from zero on one side.
\<close>

lemma inv_eq_sign_true_meets: "inv_eq_sign True SNonNeg SNonPos = (SZero, SZero)"
  by eval

lemma inv_eq_sign_false_zero_zero_unreachable:
  "inv_eq_sign False SZero SZero = (SBot, SBot)"
  by eval

lemma inv_eq_sign_false_nonneg_zero_narrows_pos:
  "inv_eq_sign False SNonNeg SZero = (SPos, SZero)"
  by eval

lemma inv_eq_sign_false_zero_nonneg_narrows_pos:
  "inv_eq_sign False SZero SNonNeg = (SZero, SPos)"
  by eval

lemma inv_eq_sign_false_nonpos_zero_narrows_neg:
  "inv_eq_sign False SNonPos SZero = (SNeg, SZero)"
  by eval

lemma inv_eq_sign_false_zero_nonpos_narrows_neg:
  "inv_eq_sign False SZero SNonPos = (SZero, SNeg)"
  by eval

text \<open>Neither operand is exactly @{term SZero}: the conservative identity fallback.\<close>
lemma inv_eq_sign_false_unrepresentable_identity:
  "inv_eq_sign False SPos SPos = (SPos, SPos)"
  by eval

text \<open>@{term SBot} on either side stays bottom-consistent.\<close>
lemma inv_eq_sign_false_bot_consistent:
  "inv_eq_sign False SBot SZero = (SBot, SBot)"
  by eval

subsection \<open>Executable end-to-end @{const bfilter_sign} tests\<close>

definition test_env_nonneg_eq :: "sign abs_state" where
  "test_env_nonneg_eq = (\<lambda>_. STop)((STR ''x'') := SNonNeg)"

text \<open>@{text \<open>x = 0\<close>} known true meets \<open>x\<close>'s bound with @{term SZero}.\<close>
lemma bfilter_sign_eq_true_narrows:
  "bfilter_sign (Eq (V (STR ''x'')) (N 0)) True test_env_nonneg_eq (STR ''x'') = SZero"
  unfolding test_env_nonneg_eq_def by eval

text \<open>@{text \<open>x != 0\<close>} known true (i.e. the guard @{text \<open>x = 0\<close>} is false) on
  @{term SNonNeg} narrows to @{term SPos}: the disequality-narrowing gain
  \<open>bfilter\<close>'s old identity-only \<open>Eq\<close> \<open>False\<close> case could never produce.\<close>
lemma bfilter_sign_eq_false_narrows_to_pos:
  "bfilter_sign (Eq (V (STR ''x'')) (N 0)) False test_env_nonneg_eq (STR ''x'') = SPos"
  unfolding test_env_nonneg_eq_def by eval

end
