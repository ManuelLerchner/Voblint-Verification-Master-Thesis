theory Machine_Kind
  imports Main "HOL-Library.Countable" "Deriving.Compare_Order_Instances"
begin

section \<open>Machine-integer kinds\<close>

text \<open>
  A kind fixes a bit width and a signedness, in the role of Goblint's \<open>ikind\<close>. It
  determines a representable range, and \<open>ik_norm\<close> maps a mathematical integer onto
  that range by two's-complement wraparound. Kinds are fixed-width, so nothing plays
  the part of C's platform-dependent type sizes.

  Wraparound is the defined behaviour for signed kinds too. C leaves signed overflow
  undefined; this semantics instead gives it the meaning \<open>-fwrapv\<close> gives it, which
  keeps evaluation total. A claim proved against it is a claim about wrapping
  arithmetic, not about C programs whose signed arithmetic overflows.

  The carrier stays \<^typ>\<open>int\<close>: a store holds one integer per variable whatever its
  kind, and the kind is read off the syntax.
\<close>

datatype ikind = I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64

instance ikind :: countable
  by countable_datatype

derive linorder ikind

fun ik_bits :: "ikind \<Rightarrow> nat" where
  "ik_bits I8 = 8" | "ik_bits U8 = 8"
| "ik_bits I16 = 16" | "ik_bits U16 = 16"
| "ik_bits I32 = 32" | "ik_bits U32 = 32"
| "ik_bits I64 = 64" | "ik_bits U64 = 64"

fun ik_signed :: "ikind \<Rightarrow> bool" where
  "ik_signed I8 = True" | "ik_signed U8 = False"
| "ik_signed I16 = True" | "ik_signed U16 = False"
| "ik_signed I32 = True" | "ik_signed U32 = False"
| "ik_signed I64 = True" | "ik_signed U64 = False"

lemma ik_bits_pos [simp]: "0 < ik_bits ik"
  by (cases ik) simp_all

subsection \<open>Range and wraparound\<close>

text \<open>A kind's range is the interval its values occupy, and \<open>ik_norm\<close> retracts every
  integer onto it.\<close>

definition ik_mod :: "ikind \<Rightarrow> int" where
  "ik_mod ik = 2 ^ ik_bits ik"

definition ik_half :: "ikind \<Rightarrow> int" where
  "ik_half ik = 2 ^ (ik_bits ik - 1)"

definition ik_min :: "ikind \<Rightarrow> int" where
  "ik_min ik = (if ik_signed ik then - ik_half ik else 0)"

definition ik_max :: "ikind \<Rightarrow> int" where
  "ik_max ik = (if ik_signed ik then ik_half ik - 1 else ik_mod ik - 1)"

definition ik_range :: "ikind \<Rightarrow> int set" where
  "ik_range ik = {ik_min ik..ik_max ik}"

text \<open>\<open>ik_norm\<close> is the truncation primitive a bit-vector type would use, applied to an
  integer: \<^const>\<open>take_bit\<close> for an unsigned kind, \<^const>\<open>signed_take_bit\<close> for a
  signed one. Their library lemmas carry the arithmetic congruences below.\<close>

definition ik_norm :: "ikind \<Rightarrow> int \<Rightarrow> int" where
  "ik_norm ik n =
     (if ik_signed ik then signed_take_bit (ik_bits ik - 1) n else take_bit (ik_bits ik) n)"

lemma ik_range_iff [simp, code_unfold]:
  "n \<in> ik_range ik \<longleftrightarrow> ik_min ik \<le> n \<and> n \<le> ik_max ik"
  unfolding ik_range_def by simp

lemma zero_in_ik_range [simp, intro]: "0 \<in> ik_range ik"
  by (cases ik) (simp_all add: ik_min_def ik_max_def ik_half_def ik_mod_def)

lemma one_in_ik_range [simp, intro]: "1 \<in> ik_range ik"
  by (cases ik) (simp_all add: ik_min_def ik_max_def ik_half_def ik_mod_def)

lemma ik_norm_in_range [simp, intro]: "ik_norm ik n \<in> ik_range ik"
proof (cases "ik_signed ik")
  case True
  have "- (2 ^ (ik_bits ik - 1)) \<le> signed_take_bit (ik_bits ik - 1) n"
    by (rule signed_take_bit_int_greater_eq_minus_exp)
  moreover have "signed_take_bit (ik_bits ik - 1) n < 2 ^ (ik_bits ik - 1)"
    by (rule signed_take_bit_int_less_exp)
  ultimately show ?thesis
    using True by (simp add: ik_norm_def ik_min_def ik_max_def ik_half_def)
next
  case False
  have "0 \<le> take_bit (ik_bits ik) n"
    by (rule take_bit_nonnegative)
  moreover have "take_bit (ik_bits ik) n < 2 ^ ik_bits ik"
    by (rule take_bit_int_less_exp)
  ultimately show ?thesis
    using False by (simp add: ik_norm_def ik_min_def ik_max_def ik_mod_def)
qed

lemma ik_norm_ge_min [simp]: "ik_min ik \<le> ik_norm ik n"
  and ik_norm_le_max [simp]: "ik_norm ik n \<le> ik_max ik"
  using ik_norm_in_range [of ik n] by simp_all

lemma ik_min_le_zero [simp]: "ik_min ik \<le> 0" and zero_le_ik_max [simp]: "0 \<le> ik_max ik"
  and ik_min_le_one [simp]: "ik_min ik \<le> 1" and one_le_ik_max [simp]: "1 \<le> ik_max ik"
  by (cases ik; simp add: ik_min_def ik_max_def ik_half_def ik_mod_def)+

lemma ik_norm_id [simp]:
  assumes "n \<in> ik_range ik"
  shows "ik_norm ik n = n"
proof (cases "ik_signed ik")
  case True
  with assms have "- (2 ^ (ik_bits ik - 1)) \<le> n" and "n < 2 ^ (ik_bits ik - 1)"
    by (simp_all add: ik_min_def ik_max_def ik_half_def)
  from signed_take_bit_int_eq_self [OF this] True show ?thesis
    by (simp add: ik_norm_def)
next
  case False
  with assms have "0 \<le> n" and "n < 2 ^ ik_bits ik"
    by (simp_all add: ik_min_def ik_max_def ik_mod_def)
  from take_bit_int_eq_self [OF this] False show ?thesis
    by (simp add: ik_norm_def)
qed

lemma ik_norm_idem [simp]: "ik_norm ik (ik_norm ik n) = ik_norm ik n"
  by (rule ik_norm_id [OF ik_norm_in_range])

lemma ik_norm_nonneg_unsigned: "\<not> ik_signed ik \<Longrightarrow> 0 \<le> ik_norm ik n"
  by (simp add: ik_norm_def)

text \<open>Wraparound subtracts a multiple of an even modulus, so it preserves parity.\<close>

lemma even_ik_norm_iff [simp]: "even (ik_norm ik n) \<longleftrightarrow> even n"
  by (cases ik) (simp_all add: ik_norm_def even_take_bit_eq even_signed_take_bit_iff)

lemma ik_norm_zero [simp]: "ik_norm ik 0 = 0"
  by (rule ik_norm_id [OF zero_in_ik_range])

lemma ik_norm_one [simp]: "ik_norm ik 1 = 1"
  by (rule ik_norm_id [OF one_in_ik_range])

text \<open>\<open>ik_norm\<close> as modular arithmetic, the form the interval argument below needs.\<close>

lemma ik_mod_pos [simp]: "0 < ik_mod ik"
  unfolding ik_mod_def by simp

lemma ik_norm_mod: "ik_norm ik n = (n - ik_min ik) mod ik_mod ik + ik_min ik"
proof (cases "ik_signed ik")
  case True
  have suc: "Suc (ik_bits ik - 1) = ik_bits ik" using ik_bits_pos [of ik] by simp
  show ?thesis
    using signed_take_bit_eq_take_bit_shift [of "ik_bits ik - 1" n]
    by (simp add: ik_norm_def ik_min_def ik_max_def ik_half_def ik_mod_def
                  take_bit_eq_mod suc True algebra_simps)
next
  case False
  then show ?thesis
    by (simp add: ik_norm_def ik_min_def ik_max_def ik_mod_def take_bit_eq_mod)
qed

text \<open>Wrapping the endpoints of an interval no wider than the kind's range and finding
  them still ordered certifies that wraparound shifts the whole interval by one amount,
  so every value in between keeps its distance to the endpoints. Goblint's
  \<open>IntervalDomain.norm ~cast:true\<close> relies on the same fact.\<close>

lemma ik_norm_interval_shift:
  assumes width: "h - l \<le> ik_max ik - ik_min ik"
    and ordered: "ik_norm ik l \<le> ik_norm ik h"
    and lv: "l \<le> v" and vh: "v \<le> h"
  shows "ik_norm ik v = ik_norm ik l + (v - l)"
proof -
  define M where "M = ik_mod ik"
  define m where "m = ik_min ik"
  have Mpos: "0 < M" unfolding M_def by simp
  have bits2: "2 * (2::int) ^ (ik_bits ik - 1) = 2 ^ ik_bits ik"
    using ik_bits_pos [of ik]
    by (metis One_nat_def Suc_pred power_Suc)
  have max_min_mod: "ik_max ik - ik_min ik + 1 = M"
    unfolding M_def ik_mod_def ik_max_def ik_min_def ik_half_def
    using bits2 by (simp split: if_splits)
  have width': "h - l < M" using width max_min_mod by linarith
  have wrap: "ik_norm ik x = (x - m) mod M + m" for x
    unfolding M_def m_def by (rule ik_norm_mod)
  have dist: "(x - m) mod M = ((l - m) mod M + (x - l)) mod M" if "l \<le> x" for x
  proof -
    have "x - m = (l - m) + (x - l)" by simp
    then show ?thesis by (metis mod_add_left_eq)
  qed
  have hv: "(h - m) mod M = ((l - m) mod M + (h - l)) mod M" using dist[OF order_refl[of l]] lv vh
    by (metis dist order_trans)
  have vv: "(v - m) mod M = ((l - m) mod M + (v - l)) mod M" using dist[OF lv] .
  have lmM: "0 \<le> (l - m) mod M" using Mpos by simp
  have not_caseB: "\<not> (l - m) mod M + (h - l) \<ge> M"
  proof
    assume ge0: "(l - m) mod M + (h - l) \<ge> M"
    have ge: "(l - m) mod M + (h - l) - M \<ge> 0" using ge0 by linarith
    have lt: "(l - m) mod M + (h - l) - M < M"
      using pos_mod_bound[OF Mpos, of "l - m"] width' by linarith
    have "((l - m) mod M + (h - l)) mod M = ((l - m) mod M + (h - l) - M + M) mod M"
      by simp
    also have "... = ((l - m) mod M + (h - l) - M) mod M" by (rule mod_add_self2)
    also have "... = (l - m) mod M + (h - l) - M" using ge lt by (rule mod_pos_pos_trivial)
    finally have "((l - m) mod M + (h - l)) mod M = (l - m) mod M + (h - l) - M" .
    with hv have "ik_norm ik h = ik_norm ik l + ((h - l) - M)" by (simp add: wrap)
    then show False using ordered width' by linarith
  qed
  have caseA_h: "(h - m) mod M = (l - m) mod M + (h - l)"
    using not_caseB hv Mpos lmM lv vh
    by (simp add: mod_pos_pos_trivial)
  have range_v: "0 \<le> v - l" "v - l \<le> h - l" using lv vh by simp_all
  have not_caseB_v: "\<not> (l - m) mod M + (v - l) \<ge> M" using not_caseB range_v by linarith
  have caseA_v: "(v - m) mod M = (l - m) mod M + (v - l)"
    using vv not_caseB_v Mpos lmM range_v
    by (simp add: mod_pos_pos_trivial)
  show ?thesis using caseA_v by (simp add: wrap)
qed

subsection \<open>Integer promotion and the usual arithmetic conversions\<close>

text \<open>\<open>ik_promote\<close> is C's integer promotion (ISO/IEC 9899 6.3.1.1p2): a kind narrower
  than \<^const>\<open>I32\<close> becomes \<^const>\<open>I32\<close>, which represents every narrower value, so
  the "promote to unsigned int" branch of the C rule never applies.\<close>

definition ik_promote :: "ikind \<Rightarrow> ikind" where
  "ik_promote ik = (if ik_bits ik < ik_bits I32 then I32 else ik)"

lemma ik_promote_pins [simp]:
  "ik_promote I8 = I32" "ik_promote U8 = I32" "ik_promote I16 = I32" "ik_promote U16 = I32"
  "ik_promote I32 = I32" "ik_promote U32 = U32" "ik_promote I64 = I64" "ik_promote U64 = U64"
  by (simp_all add: ik_promote_def)

text \<open>\<open>ik_unsigned_of\<close> is C's corresponding unsigned type: same width, unsigned.\<close>

fun ik_unsigned_of :: "ikind \<Rightarrow> ikind" where
  "ik_unsigned_of I8 = U8" | "ik_unsigned_of U8 = U8"
| "ik_unsigned_of I16 = U16" | "ik_unsigned_of U16 = U16"
| "ik_unsigned_of I32 = U32" | "ik_unsigned_of U32 = U32"
| "ik_unsigned_of I64 = U64" | "ik_unsigned_of U64 = U64"

text \<open>\<open>usual_kind\<close> is the usual arithmetic conversions (ISO/IEC 9899 6.3.1.8): promote
  both operands, then pick the common kind by signedness and width. Width stands in
  for conversion rank, which is faithful because every rank class here has one width.
  The final branch of the standard's rule is kept although no promoted pair reaches
  it, so the definition reads like the standard.\<close>

definition usual_kind :: "ikind \<Rightarrow> ikind \<Rightarrow> ikind" where
  "usual_kind a0 b0 =
     (let a = ik_promote a0; b = ik_promote b0 in
      if a = b then a
      else if ik_signed a = ik_signed b then (if ik_bits a < ik_bits b then b else a)
      else
        (let s = (if ik_signed a then a else b); u = (if ik_signed a then b else a)
         in if ik_bits s \<le> ik_bits u then u
            else if ik_max u \<le> ik_max s then s
            else ik_unsigned_of s))"


end
