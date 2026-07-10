theory Interval_Bounds
  imports Main
begin

section \<open>Interval bounds\<close>

subsection \<open>Extended integers as interval bounds\<close>

datatype eint = MinInf | Fin int | PlusInf

fun eint_le :: "eint => eint => bool" where
    "eint_le MinInf  _       = True"
  | "eint_le _       PlusInf = True"
  | "eint_le (Fin n) (Fin m) = (n <= m)"
  | "eint_le _       MinInf  = False"
  | "eint_le PlusInf _       = False"

lemma eint_le_refl: "eint_le x x"
  by (cases x) simp_all

lemma eint_le_antisym: "eint_le x y \<Longrightarrow> eint_le y x \<Longrightarrow> x = y"
  by (cases x; cases y) simp_all

lemma eint_le_trans: "eint_le x y \<Longrightarrow> eint_le y z \<Longrightarrow> eint_le x z"
  by (cases x; cases y; cases z) simp_all

lemma eint_le_PlusInf [simp]: "eint_le x PlusInf"
  by (cases x) simp_all

lemma eint_le_MinInf_left [simp]: "eint_le MinInf x"
  by simp

lemma eint_le_linear: "eint_le x y \<or> eint_le y x"
  by (cases x; cases y) auto

instantiation eint :: ord begin
definition less_eq_eint :: "eint => eint => bool" where "less_eq_eint = eint_le"
definition less_eint    :: "eint => eint => bool" where "(a :: eint) < b = (eint_le a b \<and> \<not> eint_le b a)"
instance ..
end

declare less_eq_eint_def [simp]

instance eint :: linorder
proof
  fix x y z :: eint
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_eint_def less_eq_eint_def by simp
  show "x \<le> x"                           unfolding less_eq_eint_def by (rule eint_le_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"    unfolding less_eq_eint_def by (rule eint_le_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"    unfolding less_eq_eint_def by (rule eint_le_antisym)
  show "x \<le> y \<or> y \<le> x"                  unfolding less_eq_eint_def by (rule eint_le_linear)
qed

subsection \<open>Extended-integer arithmetic\<close>

instantiation eint :: plus begin
fun plus_eint :: "eint => eint => eint" where
    "plus_eint (Fin n)   (Fin m)   = Fin (n + m)"
  | "plus_eint (Fin _)   MinInf    = MinInf"
  | "plus_eint (Fin _)   PlusInf   = PlusInf"
  | "plus_eint MinInf    MinInf    = MinInf"
  | "plus_eint MinInf    (Fin _)   = MinInf"
  | "plus_eint MinInf    PlusInf   = MinInf"
  | "plus_eint PlusInf   MinInf    = PlusInf"
  | "plus_eint PlusInf   (Fin _)   = PlusInf"
  | "plus_eint PlusInf   PlusInf   = PlusInf"
instance ..
end

instantiation eint :: minus begin
fun minus_eint :: "eint => eint => eint" where
    "minus_eint (Fin n)   (Fin m)   = Fin (n - m)"
  | "minus_eint (Fin _)   MinInf    = PlusInf"
  | "minus_eint (Fin _)   PlusInf   = MinInf"
  | "minus_eint MinInf    MinInf    = MinInf"
  | "minus_eint MinInf    (Fin _)   = MinInf"
  | "minus_eint MinInf    PlusInf   = MinInf"
  | "minus_eint PlusInf   MinInf    = PlusInf"
  | "minus_eint PlusInf   (Fin _)   = PlusInf"
  | "minus_eint PlusInf   PlusInf   = PlusInf"
instance ..
end

lemma eint_le_PlusInf_iff: "eint_le PlusInf z \<longleftrightarrow> z = PlusInf"
  by (cases z) auto
lemma eint_le_MinInf_iff: "eint_le z MinInf \<longleftrightarrow> z = MinInf"
  by (cases z) auto

lemma eint_plus_mono:
  "eint_le a1 a2 \<Longrightarrow> eint_le b1 b2 \<Longrightarrow> eint_le (a1 + b1) (a2 + b2)"
  by (cases a1; cases a2; cases b1; cases b2; auto)

lemma eint_minus_mono:
  "eint_le a1 a2 \<Longrightarrow> eint_le b2 b1 \<Longrightarrow> eint_le (a1 - b1) (a2 - b2)"
  by (cases a1; cases a2; cases b1; cases b2; auto)

end
