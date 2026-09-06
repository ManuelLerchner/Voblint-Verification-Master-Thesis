theory Sign_Special
  imports Sign_Arithmetic "Voblint_Analysis_Base.Special_Ops"
begin

section \<open>Sign: special-call semantics\<close>

text \<open>
  \<open>sign_min\<close>/\<open>sign_max\<close> exist solely as the abstract implementation of the
  \<open>Min\<close>/\<open>Max\<close> special calls (\<open>VIMP_Special.special_call\<close>); they are not part
  of Sign's core arithmetic interface the way \<open>plus_sign\<close>/\<open>times_sign\<close> are
  (VIMP's expression language has no \<open>Min\<close>/\<open>Max\<close> arithmetic operator, only the
  special-call form). If a future consumer needs them independently of
  special-call dispatch, that is the point to reconsider their home, not before.
\<close>

text \<open>
  \<open>sign_min\<close>/\<open>sign_max\<close> abstract the two-argument \<open>Min\<close>/\<open>Max\<close> special calls: the
  same brute-force per-constructor table as \<open>plus_sign\<close>/\<open>minus_sign\<close>/\<open>times_sign\<close>,
  sound and, where the two argument signs pin down which side realizes the
  extremum, exact (e.g. \<open>sign_min SNeg _ = SNeg\<close>: a negative left argument is
  always \<le> any right argument, so the minimum is negative regardless of the
  right side).
\<close>
fun sign_min :: "sign => sign => sign" where
    "sign_min SBot    _       = SBot"
  | "sign_min _       SBot    = SBot"
  | "sign_min SNeg    SNeg    = SNeg"
  | "sign_min SNonPos SNonPos = SNonPos"
  | "sign_min SZero   SZero   = SZero"
  | "sign_min SNonNeg SNonNeg = SNonNeg"
  | "sign_min SPos    SPos    = SPos"
  | "sign_min STop    STop    = STop"
  | "sign_min SNeg    SNonPos = SNeg"    | "sign_min SNonPos SNeg    = SNeg"
  | "sign_min SNeg    SZero   = SNeg"    | "sign_min SZero   SNeg    = SNeg"
  | "sign_min SNeg    SNonNeg = SNeg"    | "sign_min SNonNeg SNeg    = SNeg"
  | "sign_min SNeg    SPos    = SNeg"    | "sign_min SPos    SNeg    = SNeg"
  | "sign_min SNeg    STop    = SNeg"    | "sign_min STop    SNeg    = SNeg"
  | "sign_min SNonPos SZero   = SNonPos" | "sign_min SZero   SNonPos = SNonPos"
  | "sign_min SNonPos SNonNeg = SNonPos" | "sign_min SNonNeg SNonPos = SNonPos"
  | "sign_min SNonPos SPos    = SNonPos" | "sign_min SPos    SNonPos = SNonPos"
  | "sign_min SNonPos STop    = SNonPos" | "sign_min STop    SNonPos = SNonPos"
  | "sign_min SZero   SNonNeg = SZero"   | "sign_min SNonNeg SZero   = SZero"
  | "sign_min SZero   SPos    = SZero"   | "sign_min SPos    SZero   = SZero"
  | "sign_min SZero   STop    = SNonPos" | "sign_min STop    SZero   = SNonPos"
  | "sign_min SNonNeg SPos    = SNonNeg" | "sign_min SPos    SNonNeg = SNonNeg"
  | "sign_min SNonNeg STop    = STop"    | "sign_min STop    SNonNeg = STop"
  | "sign_min SPos    STop    = STop"    | "sign_min STop    SPos    = STop"

fun sign_max :: "sign => sign => sign" where
    "sign_max SBot    _       = SBot"
  | "sign_max _       SBot    = SBot"
  | "sign_max SNeg    SNeg    = SNeg"
  | "sign_max SNonPos SNonPos = SNonPos"
  | "sign_max SZero   SZero   = SZero"
  | "sign_max SNonNeg SNonNeg = SNonNeg"
  | "sign_max SPos    SPos    = SPos"
  | "sign_max STop    STop    = STop"
  | "sign_max SNeg    SNonPos = SNonPos" | "sign_max SNonPos SNeg    = SNonPos"
  | "sign_max SNeg    SZero   = SZero"   | "sign_max SZero   SNeg    = SZero"
  | "sign_max SNeg    SNonNeg = SNonNeg" | "sign_max SNonNeg SNeg    = SNonNeg"
  | "sign_max SNeg    SPos    = SPos"    | "sign_max SPos    SNeg    = SPos"
  | "sign_max SNeg    STop    = STop"    | "sign_max STop    SNeg    = STop"
  | "sign_max SNonPos SZero   = SZero"   | "sign_max SZero   SNonPos = SZero"
  | "sign_max SNonPos SNonNeg = SNonNeg" | "sign_max SNonNeg SNonPos = SNonNeg"
  | "sign_max SNonPos SPos    = SPos"    | "sign_max SPos    SNonPos = SPos"
  | "sign_max SNonPos STop    = STop"    | "sign_max STop    SNonPos = STop"
  | "sign_max SZero   SNonNeg = SNonNeg" | "sign_max SNonNeg SZero   = SNonNeg"
  | "sign_max SZero   SPos    = SPos"    | "sign_max SPos    SZero   = SPos"
  | "sign_max SZero   STop    = SNonNeg" | "sign_max STop    SZero   = SNonNeg"
  | "sign_max SNonNeg SPos    = SPos"    | "sign_max SPos    SNonNeg = SPos"
  | "sign_max SNonNeg STop    = SNonNeg" | "sign_max STop    SNonNeg = SNonNeg"
  | "sign_max SPos    STop    = SPos"    | "sign_max STop    SPos    = SPos"

lemma sign_min_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "min i j \<in> gamma_sign (sign_min a b)"
  using assms by (cases a; cases b; auto)

lemma sign_max_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "max i j \<in> gamma_sign (sign_max a b)"
  using assms by (cases a; cases b; auto)

lemma sign_min_mono1:
  "a1 \<le> a2 \<Longrightarrow> sign_min a1 b \<le> sign_min a2 (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_min_mono2:
  "b1 \<le> b2 \<Longrightarrow> sign_min a b1 \<le> sign_min a (b2::sign)"
  unfolding less_eq_sign_def
  by (cases a; cases b1; cases b2; simp)

lemma sign_min_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> sign_min a1 b1 \<le> sign_min a2 (b2::sign)"
  by (meson order.trans sign_min_mono1 sign_min_mono2)

lemma sign_max_mono1:
  "a1 \<le> a2 \<Longrightarrow> sign_max a1 b \<le> sign_max a2 (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_max_mono2:
  "b1 \<le> b2 \<Longrightarrow> sign_max a b1 \<le> sign_max a (b2::sign)"
  unfolding less_eq_sign_def
  by (cases a; cases b1; cases b2; simp)

lemma sign_max_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> sign_max a1 b1 \<le> sign_max a2 (b2::sign)"
  by (meson order.trans sign_max_mono1 sign_max_mono2)

subsection \<open>Special-call dispatch\<close>

fun special_sign ::
    "special_call => vname => (vname => sign) => (vname => sign)"
where
  "special_sign Nondet_Int x \<sigma> = \<sigma>(x := STop)"
| "special_sign (Min a b) x \<sigma> = \<sigma>(x := sign_min (aval_sign a \<sigma>) (aval_sign b \<sigma>))"
| "special_sign (Max a b) x \<sigma> = \<sigma>(x := sign_max (aval_sign a \<sigma>) (aval_sign b \<sigma>))"

definition sign_special_ops :: "sign special_ops" where
  "sign_special_ops = (| special_min = sign_min, special_max = sign_max |)"

interpretation sign_special: sound_special_ops sign_special_ops aval_sign
  by unfold_locales
     (auto simp: sign_special_ops_def gamma_sign_top
           intro: sign_min_sound sign_max_sound sign_min_combine_mono sign_max_combine_mono
                  aval_sign_sound aval_sign_mono)

lemma sign_special_ops_min [simp]: "special_min sign_special_ops = sign_min"
  by (simp add: sign_special_ops_def)

lemma sign_special_ops_max [simp]: "special_max sign_special_ops = sign_max"
  by (simp add: sign_special_ops_def)

lemma special_sign_eq_transfer: "special_sign sc x \<sigma> = sign_special.special_transfer sc x \<sigma>"
  by (cases sc) (simp_all add: top_sign_def)

lemmas special_sign_sound = sign_special.special_transfer_sound[folded special_sign_eq_transfer]
lemmas special_sign_mono  = sign_special.special_transfer_mono[folded special_sign_eq_transfer]

end
