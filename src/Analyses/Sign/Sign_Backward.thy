theory Sign_Backward
  imports
    Sign_Arithmetic
    "Voblint_Domain.Backward_Numeric_Queries"
begin

section \<open>Sign backward filtering\<close>

text \<open>The sign meet lives with the lattice in \<^theory>\<open>Voblint_Domain.Sign_Lattice\<close>.\<close>

subsection \<open>Backward-analysis: inverse operators\<close>

text \<open>
  @{text inv_less_sign} provides sign-specific refinement when a guard
  @{text "e1 < e2"} is known true or false. Plus/minus/times are too coarse for
  useful arithmetic inversion in sign, so this theory gives no inverse for them.
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
  false. The true branch narrows both operands to their intersection,
  @{const inf}. The false branch only narrows a boundary
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

end
