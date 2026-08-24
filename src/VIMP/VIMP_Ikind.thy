theory VIMP_Ikind
  imports Main
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
\<close>

datatype ikind = I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64

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
      then (n + ik_half ik) mod ik_mod ik - ik_half ik
      else n mod ik_mod ik)"

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
  have r1: "0 \<le> (n + ik_half ik) mod ik_mod ik"
    and r2: "(n + ik_half ik) mod ik_mod ik < ik_mod ik"
    by simp_all
  have "- ik_half ik \<le> (n + ik_half ik) mod ik_mod ik - ik_half ik"
    using r1 by linarith
  moreover have "(n + ik_half ik) mod ik_mod ik - ik_half ik \<le> ik_half ik - 1"
    using r2 ik_mod_2half [of ik] by linarith
  ultimately show ?thesis
    using True by (simp add: ik_norm_def ik_min_def ik_max_def)
next
  case False
  have "0 \<le> n mod ik_mod ik" and "n mod ik_mod ik < ik_mod ik"
    by simp_all
  then show ?thesis
    using False by (simp add: ik_norm_def ik_min_def ik_max_def)
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
  with assms have lb: "- ik_half ik \<le> n" and ub: "n \<le> ik_half ik - 1"
    by (simp_all add: ik_min_def ik_max_def)
  have "0 \<le> n + ik_half ik" using lb by linarith
  moreover have "n + ik_half ik < ik_mod ik"
    using ub ik_mod_2half [of ik] by linarith
  ultimately have "(n + ik_half ik) mod ik_mod ik = n + ik_half ik"
    by (rule mod_pos_pos_trivial)
  with True show ?thesis by (simp add: ik_norm_def)
next
  case False
  with assms have "0 \<le> n" and "n \<le> ik_mod ik - 1"
    by (simp_all add: ik_min_def ik_max_def)
  then have "n mod ik_mod ik = n"
    by (intro mod_pos_pos_trivial) linarith+
  with False show ?thesis by (simp add: ik_norm_def)
qed

lemma ik_norm_idem [simp]: "ik_norm ik (ik_norm ik n) = ik_norm ik n"
  by (rule ik_norm_id [OF ik_norm_in_range])

subsection \<open>Congruence: moving \<open>ik_norm\<close> through arithmetic\<close>

text \<open>
  \<open>ik_norm\<close> agrees with reduction modulo \<open>ik_mod\<close> up to the
  signed re-centering, so any two integers in the same residue class norm
  to the same value. The operator laws below are what lets a transfer
  proof replace normed operands by mathematical ones under an outer
  \<open>ik_norm\<close> \<comment> \<open>the shape every wraparound-aware transfer
  soundness argument reduces to.\<close>
\<close>

lemma ik_norm_mod [simp]:
  "ik_norm ik n mod ik_mod ik = n mod ik_mod ik"
proof (cases "ik_signed ik")
  case True
  have "((n + ik_half ik) mod ik_mod ik - ik_half ik) mod ik_mod ik
          = n mod ik_mod ik"
    by (simp add: mod_diff_left_eq)
  with True show ?thesis by (simp add: ik_norm_def)
next
  case False
  then show ?thesis by (simp add: ik_norm_def)
qed

lemma ik_norm_cong:
  assumes "a mod ik_mod ik = b mod ik_mod ik"
  shows "ik_norm ik a = ik_norm ik b"
proof -
  have "(a + ik_half ik) mod ik_mod ik = (b + ik_half ik) mod ik_mod ik"
    using assms by (metis mod_add_left_eq)
  with assms show ?thesis by (simp add: ik_norm_def)
qed

lemma ik_norm_add:
  "ik_norm ik (ik_norm ik a + ik_norm ik b) = ik_norm ik (a + b)"
  by (rule ik_norm_cong) (metis ik_norm_mod mod_add_eq)

lemma ik_norm_diff:
  "ik_norm ik (ik_norm ik a - ik_norm ik b) = ik_norm ik (a - b)"
  by (rule ik_norm_cong) (metis ik_norm_mod mod_diff_eq)

lemma ik_norm_mult:
  "ik_norm ik (ik_norm ik a * ik_norm ik b) = ik_norm ik (a * b)"
  by (rule ik_norm_cong) (metis ik_norm_mod mod_mult_eq)

lemma ik_norm_uminus:
  "ik_norm ik (- ik_norm ik a) = ik_norm ik (- a)"
  by (rule ik_norm_cong) (metis ik_norm_mod mod_minus_eq)

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
