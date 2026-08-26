theory VIMP_Ikind
  imports Main "HOL-Library.Countable" "Deriving.Compare_Order_Instances"
begin

section \<open>Machine-integer kinds\<close>

text \<open>
  A machine-integer kind fixes a bit width and a signedness, in the role of
  Goblint's \<open>ikind\<close>: a kind determines the representable range
  (Goblint's \<open>Size.range\<close>), and \<open>ik_norm\<close> maps a mathematical
  integer onto that range by two's-complement wraparound (Goblint's
  \<open>norm\<close>). Kinds are fixed-width, stdint-style; VIMP has no platform,
  so nothing plays the part of CIL's machine-dependent C kind sizes.

  Wraparound is the defined behaviour for signed kinds as well: keeping the
  semantics total avoids an undefined-behaviour layer, and an abstract
  transfer that answers top on possible signed overflow is sound over wrap.

  \<open>ik_norm\<close> is built directly on \<^const>\<open>take_bit\<close> and
  \<^const>\<open>signed_take_bit\<close> (\<^theory>\<open>HOL.Bit_Operations\<close>, part of
  \<open>Main\<close>) rather than a hand-rolled \<open>mod\<close>: \<^verbatim>\<open>'a word\<close>
  (\<^verbatim>\<open>HOL-Library.Word\<close>, not imported here) is itself the
  quotient of \<open>int\<close> by \<open>take_bit\<close>-equivalence, so this is the same
  truncation primitive a bit-vector carrier would use, without moving
  the width into the HOL type. The carrier stays plain \<open>int\<close> deliberately
  -- VIMP's \<open>store\<close>
  is one \<open>vname => int\<close> function shared by every variable regardless of
  kind, with \<open>ikind\<close> consulted as a runtime value from the typing
  environment; a per-width type would force either monomorphising every
  program to one kind or an existential wrapper across widths, reopening
  the \<open>IntDomLifter\<close>-style value/kind pairing the migration's D6
  decision avoids. The payoff of building on \<open>take_bit\<close>/\<open>signed_take_bit\<close>
  survives that choice: their existing arithmetic-interaction lemmas
  replace hand-proved congruences below, and the same underlying bit-
  operations class carries bitwise AND/OR/XOR/shifts on \<open>int\<close> for a
  future bitfield domain (register row "Value domains").
\<close>

datatype ikind = I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64

derive linorder ikind

instance ikind :: countable
  by countable_datatype

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

subsection \<open>Integer promotion\<close>

text \<open>
  \<open>ik_promote\<close> is C's integer-promotion rule (ISO 6.3.1.8): a kind narrower
  than \<open>I32\<close> is promoted to \<open>I32\<close> before it participates in an arithmetic,
  comparison, or logical operator -- exactly what CIL's \<open>integralPromotion\<close>
  does as the first step of \<open>arithmeticConversion\<close>, before any operator is
  evaluated. A kind already at or above \<open>I32\<close>'s width is unaffected: \<open>I32\<close>
  can represent every value of a narrower kind, signed or unsigned, so
  promotion never needs the "promote to unsigned int" branch of the C rule.
\<close>

definition ik_promote :: "ikind \<Rightarrow> ikind" where
  "ik_promote ik = (if ik_bits ik < ik_bits I32 then I32 else ik)"

lemma ik_bits_ik_promote_ge [simp]: "ik_bits I32 \<le> ik_bits (ik_promote ik)"
  by (simp add: ik_promote_def)

lemma ik_promote_pins:
  "ik_promote I8 = I32" "ik_promote U8 = I32"
  "ik_promote I16 = I32" "ik_promote U16 = I32"
  "ik_promote I32 = I32" "ik_promote U32 = U32"
  "ik_promote I64 = I64" "ik_promote U64 = U64"
  by eval+


subsection \<open>Range and wraparound\<close>

text \<open>
  \<open>ik_mod\<close> is the size of the kind's value space and \<open>ik_half\<close>
  the magnitude of a signed kind's minimum; every bound below is expressed
  through the two, so that only \<open>ik_mod_2half\<close> ever reasons about
  the exponent.
\<close>

definition ik_mod :: "ikind \<Rightarrow> int" where
  "ik_mod ik = 2 ^ ik_bits ik"

definition ik_half :: "ikind \<Rightarrow> int" where
  "ik_half ik = 2 ^ (ik_bits ik - 1)"

lemma ik_mod_pos [simp]: "0 < ik_mod ik"
  unfolding ik_mod_def by simp

lemma ik_half_pos [simp]: "0 < ik_half ik"
  unfolding ik_half_def by simp

lemma ik_mod_2half: "ik_mod ik = 2 * ik_half ik"
  by (cases ik) (simp_all add: ik_mod_def ik_half_def)

definition ik_min :: "ikind \<Rightarrow> int" where
  "ik_min ik = (if ik_signed ik then - ik_half ik else 0)"

definition ik_max :: "ikind \<Rightarrow> int" where
  "ik_max ik = (if ik_signed ik then ik_half ik - 1 else ik_mod ik - 1)"

definition ik_range :: "ikind \<Rightarrow> int set" where
  "ik_range ik = {ik_min ik..ik_max ik}"

definition ik_norm :: "ikind \<Rightarrow> int \<Rightarrow> int" where
  "ik_norm ik n =
     (if ik_signed ik
      then signed_take_bit (ik_bits ik - 1) n
      else take_bit (ik_bits ik) n)"

text \<open>
  The \<open>code_unfold\<close> turns range membership into two comparisons;
  the interval-set representation would otherwise enumerate the range as
  a list when evaluated.
\<close>

lemma ik_range_iff [simp, code_unfold]:
  "n \<in> ik_range ik \<longleftrightarrow> ik_min ik \<le> n \<and> n \<le> ik_max ik"
  unfolding ik_range_def by simp

lemma finite_ik_range [simp, intro]: "finite (ik_range ik)"
  unfolding ik_range_def by simp

lemma zero_in_ik_range [simp, intro]: "0 \<in> ik_range ik"
  by (cases ik) (simp_all add: ik_min_def ik_max_def ik_half_def ik_mod_def)

text \<open>Every kind this project defines is at least eight bits wide, so \<open>1\<close> is
  representable at all of them -- the fact a comparison's \<open>0\<close>/\<open>1\<close> result needs
  in order to lie in its own kind's range.\<close>
lemma one_in_ik_range [simp, intro]: "1 \<in> ik_range ik"
  by (cases ik) (simp_all add: ik_min_def ik_max_def ik_half_def ik_mod_def)

lemma ik_min_le_zero [simp]: "ik_min ik \<le> 0"
  using zero_in_ik_range [of ik] by simp

lemma zero_le_ik_max [simp]: "0 \<le> ik_max ik"
  using zero_in_ik_range [of ik] by simp

lemma one_le_ik_max [simp]: "1 \<le> ik_max ik"
  by (cases ik) (simp_all add: ik_max_def ik_half_def ik_mod_def)

lemma ik_min_le_one [simp]: "ik_min ik \<le> 1"
  by (rule order_trans [OF ik_min_le_zero]) simp

lemma ik_min_le_max: "ik_min ik \<le> ik_max ik"
  by (rule order_trans [OF ik_min_le_zero zero_le_ik_max])

subsection \<open>\<open>ik_norm\<close> as a retraction onto the range\<close>

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
  using ik_norm_in_range [of ik n] by simp

lemma ik_norm_le_max [simp]: "ik_norm ik n \<le> ik_max ik"
  using ik_norm_in_range [of ik n] by simp

lemma ik_norm_id [simp]:
  assumes "n \<in> ik_range ik"
  shows "ik_norm ik n = n"
proof (cases "ik_signed ik")
  case True
  with assms have lb: "- (2 ^ (ik_bits ik - 1)) \<le> n"
    and ub: "n < 2 ^ (ik_bits ik - 1)"
    by (simp_all add: ik_min_def ik_max_def ik_half_def)
  from signed_take_bit_int_eq_self [OF lb ub] True
  show ?thesis by (simp add: ik_norm_def)
next
  case False
  with assms have lb: "0 \<le> n" and ub: "n < 2 ^ ik_bits ik"
    by (simp_all add: ik_min_def ik_max_def ik_mod_def)
  from take_bit_int_eq_self [OF lb ub] False
  show ?thesis by (simp add: ik_norm_def)
qed

lemma ik_norm_idem [simp]: "ik_norm ik (ik_norm ik n) = ik_norm ik n"
  by (rule ik_norm_id [OF ik_norm_in_range])

text \<open>
  \<open>ik_unsigned_of\<close> is C's "corresponding unsigned type" (6.3.1.8's final
  case): same width, signedness flipped. It is the identity on a kind that is
  already unsigned.
\<close>

fun ik_unsigned_of :: "ikind \<Rightarrow> ikind" where
  "ik_unsigned_of I8 = U8" | "ik_unsigned_of U8 = U8"
| "ik_unsigned_of I16 = U16" | "ik_unsigned_of U16 = U16"
| "ik_unsigned_of I32 = U32" | "ik_unsigned_of U32 = U32"
| "ik_unsigned_of I64 = U64" | "ik_unsigned_of U64 = U64"

lemma ik_bits_ik_unsigned_of [simp]: "ik_bits (ik_unsigned_of ik) = ik_bits ik"
  by (cases ik) simp_all

lemma ik_signed_ik_unsigned_of [simp]: "\<not> ik_signed (ik_unsigned_of ik)"
  by (cases ik) simp_all

text \<open>Promotion lands in one of four kinds, whatever it is given. Every
  statement below about "a promoted kind" is a statement about these four.\<close>

lemma ik_promote_cases:
  "ik_promote ik = I32 \<or> ik_promote ik = U32 \<or> ik_promote ik = I64 \<or> ik_promote ik = U64"
  by (cases ik) (simp_all add: ik_promote_def)

lemma ik_promote_idem [simp]: "ik_promote (ik_promote ik) = ik_promote ik"
  by (cases ik) (simp_all add: ik_promote_def)

text \<open>
  \<open>usual_kind\<close> is C's usual arithmetic conversions (ISO/IEC 9899 6.3.1.8) on
  this project's fixed-width kinds: promote both operands, then pick the common
  kind by signedness and width.

  Width stands in for C's conversion rank. That is faithful for this kind set
  because, after promotion, each rank class is represented by exactly one
  width, with the signed and unsigned counterparts of a class sharing that
  width. Comparing widths therefore compares ranks. It would not be faithful
  for C's own types, where \<open>int\<close> and \<open>long\<close> may share a width while holding
  different ranks; introducing platform kinds is exactly the change that would
  invalidate this paragraph.

  All six branches of the standard's rule are written out, including the final
  one -- neither width dominates and the signed kind cannot represent the
  unsigned one, so the result is the signed kind's own unsigned counterpart.
  That branch is unreachable here, and \<open>promoted_signed_covers_narrower_unsigned\<close>
  proves it so for arbitrary kinds rather than tabulating instances: whenever a
  promoted signed kind is strictly wider than a promoted unsigned one, it
  represents that unsigned kind's whole range, which is the standard's
  preceding case. The definition is kept in the standard's shape rather than
  collapsed to what today's kinds happen to allow.

  This replaces a left-biased join, which made evaluation depend on operand
  order: \<open>u32 == i64\<close> and \<open>i64 == u32\<close> could disagree, which C forbids and
  which no source language should permit.
\<close>

definition usual_kind :: "ikind \<Rightarrow> ikind \<Rightarrow> ikind" where
  "usual_kind a0 b0 =
     (let a = ik_promote a0; b = ik_promote b0 in
      if a = b then a
      else if ik_signed a = ik_signed b
      then (if ik_bits a < ik_bits b then b else a)
      else
        (let s = (if ik_signed a then a else b);
             u = (if ik_signed a then b else a)
         in if ik_bits s \<le> ik_bits u then u
            else if ik_max u \<le> ik_max s then s
            else ik_unsigned_of s))"

text \<open>The standard's final case cannot arise at a promoted kind pair: a wider
  promoted signed kind always covers a narrower promoted unsigned one.\<close>
lemma promoted_signed_covers_narrower_unsigned:
  assumes "ik_promote s = s" and "ik_promote u = u"
      and "ik_signed s" and "\<not> ik_signed u"
      and "ik_bits u < ik_bits s"
    shows "ik_max u \<le> ik_max s"
  using assms
  by (cases s; cases u)
     (simp_all add: ik_promote_def ik_max_def ik_half_def ik_mod_def)

lemma usual_kind_commute: "usual_kind a b = usual_kind b a"
  by (cases a; cases b)
     (simp_all add: usual_kind_def ik_promote_def ik_max_def ik_half_def ik_mod_def Let_def)

text \<open>The result dominates both promoted operands in width -- the fact
  elaboration needs to know that converting each operand to the common kind is
  a widening, not a truncation.\<close>

lemma ik_bits_usual_kind_ge_left [simp]: "ik_bits (ik_promote a) \<le> ik_bits (usual_kind a b)"
  by (cases a; cases b)
     (simp_all add: usual_kind_def ik_promote_def ik_max_def ik_half_def ik_mod_def Let_def)

lemma ik_bits_usual_kind_ge_right [simp]: "ik_bits (ik_promote b) \<le> ik_bits (usual_kind a b)"
  using ik_bits_usual_kind_ge_left[of b a] by (simp add: usual_kind_commute)

lemma ik_bits_usual_kind_ge_I32: "ik_bits I32 \<le> ik_bits (usual_kind a b)"
  by (rule order_trans[OF ik_bits_ik_promote_ge ik_bits_usual_kind_ge_left])

text \<open>\<open>usual_kind\<close> promotes, so it is idempotent only up to promotion: a narrow
  kind combined with itself yields \<open>I32\<close>, not that kind.\<close>

lemma usual_kind_idem [simp]: "usual_kind a a = ik_promote a"
  by (cases a) (simp_all add: usual_kind_def ik_promote_def Let_def)

lemma usual_kind_promoted [simp]: "usual_kind (ik_promote a) (ik_promote b) = usual_kind a b"
  by (cases a; cases b) (simp_all add: usual_kind_def ik_promote_def Let_def)

text \<open>The complete conversion table over the four kinds promotion can produce.
  Regression evidence for the table above, not the proof of unreachability --
  that is \<open>promoted_signed_covers_narrower_unsigned\<close>.\<close>
lemma usual_kind_reachable_pins:
  "usual_kind I32 I32 = I32" "usual_kind I32 U32 = U32"
  "usual_kind I32 I64 = I64" "usual_kind I32 U64 = U64"
  "usual_kind U32 I32 = U32" "usual_kind U32 U32 = U32"
  "usual_kind U32 I64 = I64" "usual_kind U32 U64 = U64"
  "usual_kind I64 I32 = I64" "usual_kind I64 U32 = I64"
  "usual_kind I64 I64 = I64" "usual_kind I64 U64 = U64"
  "usual_kind U64 I32 = U64" "usual_kind U64 U32 = U64"
  "usual_kind U64 I64 = U64" "usual_kind U64 U64 = U64"
  by (simp_all add: usual_kind_def ik_promote_def ik_max_def ik_half_def ik_mod_def Let_def)

subsection \<open>Congruence: moving \<open>ik_norm\<close> through arithmetic\<close>

text \<open>
  \<open>take_bit\<close>/\<open>signed_take_bit\<close> already carry the arithmetic-interaction
  lemmas this needs (\<open>take_bit_add\<close>, \<open>signed_take_bit_add\<close>, ...): each
  one has exactly the shape \<open>f n (f n a `op` f n b) = f n (a `op` b)\<close>
  that a transfer proof reduces to when it moves \<open>ik_norm\<close> across an
  arithmetic operator.
\<close>

lemma ik_norm_add:
  "ik_norm ik (ik_norm ik a + ik_norm ik b) = ik_norm ik (a + b)"
  by (cases "ik_signed ik") (simp_all add: ik_norm_def signed_take_bit_add take_bit_add)

lemma ik_norm_diff:
  "ik_norm ik (ik_norm ik a - ik_norm ik b) = ik_norm ik (a - b)"
  by (cases "ik_signed ik") (simp_all add: ik_norm_def signed_take_bit_diff take_bit_diff)

lemma ik_norm_mult:
  "ik_norm ik (ik_norm ik a * ik_norm ik b) = ik_norm ik (a * b)"
  by (cases "ik_signed ik") (simp_all add: ik_norm_def signed_take_bit_mult take_bit_mult)

lemma ik_norm_uminus:
  "ik_norm ik (- ik_norm ik a) = ik_norm ik (- a)"
  by (cases "ik_signed ik") (simp_all add: ik_norm_def signed_take_bit_minus take_bit_minus)

text \<open>Norming at a narrower kind after a wider one is the same as norming at the narrower
  kind directly: a narrower truncation only ever looks at the low bits a wider one already
  preserved exactly, so the wider step is redundant. This is what makes a value normed once
  at an externally-imposed kind (an assignment target, a formal, a return type) equal a value
  computed at its own wider natural kind and truncated only at that one boundary.\<close>
lemma ik_norm_ik_norm:
  assumes le: "ik_bits m \<le> ik_bits n"
  shows "ik_norm m (ik_norm n v) = ik_norm m v"
proof -
  have not_le: "\<not> ik_bits n \<le> ik_bits m - Suc 0"
    using le ik_bits_pos [of m] by linarith
  show ?thesis
    using le
    by (cases "ik_signed m"; cases "ik_signed n")
       (simp_all add: ik_norm_def take_bit_take_bit signed_take_bit_take_bit
         take_bit_signed_take_bit signed_take_bit_signed_take_bit min.absorb1 not_le)
qed

text \<open>
  \<open>ik_norm\<close> as reduce-then-recenter modular arithmetic: the form Goblint's
  own \<open>cast_to\<close> (\<open>Size.cast\<close>) and this migration's Interval/Congruence
  \<open>cast\<close> operators reason about directly, since \<open>mod\<close> lemmas are far better
  automated than \<open>take_bit\<close>/\<open>signed_take_bit\<close> ones for the interval-wrap
  argument those operators need.
\<close>

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

lemma ik_mod_dvd_ik_norm_diff: "ik_mod ik dvd (ik_norm ik n - n)"
proof -
  let ?a = "n - ik_min ik" and ?M = "ik_mod ik"
  have "ik_norm ik n - n = ?a mod ?M - ?a"
    by (simp add: ik_norm_mod)
  also have "... = - (?a div ?M * ?M)"
    using minus_div_mult_eq_mod [of ?a ?M] by simp
  finally show ?thesis by simp
qed

text \<open>
  The interval-wrap step Interval's \<open>cast\<close> needs: wrapping the two
  endpoints of a not-too-wide range and finding them still ordered is enough
  to certify that every point in between wraps into that same order --
  exactly the fact Goblint's own \<open>IntervalDomain.norm ~cast:true\<close> relies on
  (\<open>resdiff \<le> diff\<close> then re-check \<open>l \<le> u\<close> after wrapping each bound).
\<close>

lemma ik_norm_interval_wrap:
  assumes width: "h - l \<le> ik_max ik - ik_min ik"
    and ordered: "ik_norm ik l \<le> ik_norm ik h"
    and lv: "l \<le> v" and vh: "v \<le> h"
  shows "ik_norm ik l \<le> ik_norm ik v \<and> ik_norm ik v \<le> ik_norm ik h"
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
    have ge: "(l - m) mod M + (h - l) - M \<ge> 0" using ge0 by linarith    have lt: "(l - m) mod M + (h - l) - M < M"
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
  show ?thesis using caseA_v caseA_h range_v by (simp add: wrap)
qed

subsection \<open>Executable pins\<close>

text \<open>
  Closed-form bounds and wraparound cases, pinned by evaluation so a
  definition change that silently shifts a range or a wrap boundary fails
  here first.
\<close>

lemma ik_bounds_pins:
  "ik_min I8 = - (2 ^ 7)" "ik_max I8 = 2 ^ 7 - 1"
  "ik_min U8 = 0" "ik_max U8 = 2 ^ 8 - 1"
  "ik_min I16 = - (2 ^ 15)" "ik_max I16 = 2 ^ 15 - 1"
  "ik_min U16 = 0" "ik_max U16 = 2 ^ 16 - 1"
  "ik_min I32 = - (2 ^ 31)" "ik_max I32 = 2 ^ 31 - 1"
  "ik_min U32 = 0" "ik_max U32 = 2 ^ 32 - 1"
  "ik_min I64 = - (2 ^ 63)" "ik_max I64 = 2 ^ 63 - 1"
  "ik_min U64 = 0" "ik_max U64 = 2 ^ 64 - 1"
  by eval+

text \<open>
  Promotion never narrows the representable range: a value already fitting
  \<open>ik\<close> also fits \<open>ik_promote ik\<close>. Every kind narrower than \<open>I32\<close> promotes
  to \<open>I32\<close>, whose range contains all eight- and sixteen-bit values, signed
  or unsigned alike; every kind at or above \<open>I32\<close>'s width is its own
  promotion. This is what lets a variable's own leaf value, known within its
  declared kind, be soundly reused at the promoted kind a comparison or
  logical operator evaluates it at.
\<close>
lemma ik_range_promote_mono: "ik_range ik \<subseteq> ik_range (ik_promote ik)"
  by (cases ik) (auto simp: ik_promote_pins ik_bounds_pins)

lemma ik_norm_pins:
  "ik_norm U8 (2 ^ 8) = 0"
  "ik_norm U8 (- 1) = 2 ^ 8 - 1"
  "ik_norm I8 (2 ^ 7) = - (2 ^ 7)"
  "ik_norm I8 (- (2 ^ 7) - 1) = 2 ^ 7 - 1"
  "ik_norm I32 (2 ^ 31) = - (2 ^ 31)"
  "ik_norm U32 (- 1) = 2 ^ 32 - 1"
  "ik_norm U32 (2 ^ 32) = 0"
  "ik_norm I64 42 = 42"
  by eval+

end
