theory Sign_Backward
  imports
    Sign_Arithmetic
    "Voblint_Nonrelational.Exec_Backward"
    "Voblint_Domain.Backward_Numeric_Queries"
begin

section \<open>Sign backward filtering\<close>

text \<open>The sign meet lives with the lattice in \<^theory>\<open>Voblint_Domain.Sign_Lattice\<close>.\<close>

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
       (let a1' = if sign_le a2 SNonPos then a1 \<sqinter> SNeg else a1 ;
                a2' = if sign_le a1 SNonNeg then a2 \<sqinter> SPos else a2
        in (a1', a2'))"
  | "inv_less_sign False a1 a2 =
       (let a1' = if sign_le a2 SPos then a1 \<sqinter> SPos
                  else if sign_le a2 SNonNeg then a1 \<sqinter> SNonNeg
                  else a1 ;
                a2' = if sign_le a1 SNeg then a2 \<sqinter> SNeg
                  else if sign_le a1 SNonPos then a2 \<sqinter> SNonPos
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
  via @{const inf} directly. The false branch only narrows a boundary
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
  reliance on @{text \<open>SBot \<sqinter> _ = SBot\<close>}.
\<close>

fun inv_eq_sign :: "bool => sign => sign => sign * sign" where
    "inv_eq_sign True  a1 a2 = (a1 \<sqinter> a2, a1 \<sqinter> a2)"
  | "inv_eq_sign False a1 a2 =
       (let a1' = if sign_le a1 SZero \<and> sign_le a2 SZero then SBot
                  else if sign_le a2 SZero \<and> sign_le a1 SNonNeg then a1 \<sqinter> SPos
                  else if sign_le a2 SZero \<and> sign_le a1 SNonPos then a1 \<sqinter> SNeg
                  else a1 ;
                a2' = if sign_le a1 SZero \<and> sign_le a2 SZero then SBot
                  else if sign_le a1 SZero \<and> sign_le a2 SNonNeg then a2 \<sqinter> SPos
                  else if sign_le a1 SZero \<and> sign_le a2 SNonPos then a2 \<sqinter> SNeg
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
  then have "n1 \<in> gamma_sign (a1 \<sqinter> a2)"
    using inf_sign_sound[OF h1] by simp
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

lemma inv_eq_sign_mono:
  assumes "a1 \<le> (a1' :: sign)"
      and "a2 \<le> a2'"
  shows
    "le_pair (inv_eq_sign r a1 a2) (inv_eq_sign r a1' a2')"
proof (cases r)
  case True
  then show ?thesis using assms by (simp add: le_infI1 le_infI2)
next
  case False
  then show ?thesis
    using assms unfolding less_eq_sign_def
    by (cases a1; cases a1'; simp; cases a2; cases a2'; simp add: Let_def)
qed

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
    "le_pair (inv_less_sign r a1 a2) (inv_less_sign r a1' a2')"
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
    using True fst_mono snd_mono
    by (simp only: inv_less_sign.simps Let_def sign_le_iff prod.sel)
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
    using False fst_mono snd_mono
    by (simp only: inv_less_sign.simps Let_def sign_le_iff prod.sel)
qed

subsection \<open>The refinement operations and their certificate\<close>

text \<open>
  Sign's refinement choices: the lattice meet, the sign-specific comparison
  inverses, and the conservative identity for arithmetic. The guard filters and
  the branch are not stated here; \<open>Sign_Transfer\<close> derives them from this record
  and the evaluator.
\<close>

definition sign_refine_ops :: "sign refine_ops" where
  "sign_refine_ops =
     \<lparr>r_tobool = sign_tobool, r_inv_less = inv_less_sign, r_inv_eq = inv_eq_sign,
      r_inv_plus = inv_conservative, r_inv_minus = inv_conservative,
      r_inv_times = inv_conservative, r_intersect = inf\<rparr>"

lemma sign_refine_ops_simps [simp]:
  "r_tobool sign_refine_ops = sign_tobool"
  "r_inv_less sign_refine_ops = inv_less_sign"
  "r_inv_eq sign_refine_ops = inv_eq_sign"
  "r_inv_plus sign_refine_ops = inv_conservative"
  "r_inv_minus sign_refine_ops = inv_conservative"
  "r_inv_times sign_refine_ops = inv_conservative"
  "r_intersect sign_refine_ops = inf"
  by (simp_all add: sign_refine_ops_def)

text \<open>
  The certificate discharges soundness, monotonicity, and reductiveness together
  against @{locale mono_refinement}. Each \<open>inv_*\<close>'s mono/reductive obligation
  is one @{const le_pair} fact, transparent notation for the componentwise \<open>\<and>\<close> the
  per-operator lemmas above already prove.
\<close>

lemma sign_backward_domain:
  "mono_refinement inf aval_sign sign_tobool
     inv_less_sign inv_eq_sign inv_conservative inv_conservative inv_conservative"
proof unfold_locales
qed (use sign_tobool_mono in \<open>simp_all add: inf_sign_sound inv_less_sign_sound
       inv_eq_sign_sound inv_conservative_def sign_tobool_sound inf_mono sign_arith.aval_dom_mono
       inv_less_sign_mono inv_eq_sign_mono le_infI1 le_infI2\<close>)

end
