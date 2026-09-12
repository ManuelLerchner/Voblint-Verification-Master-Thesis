theory VIMP_Expr
  imports VIMP_Syntax
begin

section \<open>Expression evaluation\<close>

text \<open>
  \<open>aval\<close> evaluates an expression in a store.  Every VIMP expression is integer-valued, so
  there is no separate Boolean type. Conditions use C-style truthiness (non-zero),
  while comparisons and logical operators yield \<open>1\<close> or \<open>0\<close>.  Evaluation is total and has no
  effects, which is why a guard can be re-evaluated freely by the transfer functions.
\<close>

text \<open>Division and remainder truncate toward zero for non-zero divisors.
  VIMP keeps expressions total by defining division by zero as zero and
  remainder by zero as the dividend. These zero-divisor cases are VIMP
  conventions; they do not model C's undefined behavior.\<close>

definition c_div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "c_div a b =
    (if b = 0 then 0 else sgn a * sgn b * (abs a div abs b))"

definition c_mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "c_mod a b = (if b = 0 then a else a - c_div a b * b)"

lemma c_div_zero [simp]: "c_div a 0 = 0" "c_div 0 b = 0"
  by (simp_all add: c_div_def)

lemma c_mod_zero [simp]: "c_mod a 0 = a" "c_mod 0 b = 0"
  by (simp_all add: c_mod_def)

lemma c_div_one [simp]: "c_div a 1 = a" "c_div a (-1) = -a"
  by (simp_all add: c_div_def sgn_mult_abs)

lemma c_mod_one [simp]: "c_mod a 1 = 0" "c_mod a (-1) = 0"
  by (simp_all add: c_mod_def)

lemma c_div_mod_reconstruct:
  "c_div a b * b + c_mod a b = a"
  by (simp add: c_mod_def)

lemma c_mod_abs:
  "c_mod a b = sgn a * (abs a mod abs b)"
proof (cases "b = 0")
  case True
  then show ?thesis by (simp add: sgn_mult_abs)
next
  case False
  have product: "c_div a b * b = sgn a * (abs a div abs b * abs b)"
    using False unfolding c_div_def
    by (simp add: abs_sgn mult_ac)
  have "sgn a * (abs a div abs b * abs b) + sgn a * (abs a mod abs b) = a"
    by (simp only: distrib_left[symmetric] div_mult_mod_eq sgn_mult_abs)
  with False product show ?thesis unfolding c_mod_def by (simp only: False if_False; linarith)
qed

lemma c_div_nonneg:
  "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> c_div a b"
  "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> 0 \<le> c_div a b"
  by (auto simp: c_div_def sgn_if pos_imp_zdiv_nonneg_iff neg_imp_zdiv_nonneg_iff)

lemma c_div_nonpos:
  "a \<le> 0 \<Longrightarrow> 0 \<le> b \<Longrightarrow> c_div a b \<le> 0"
  "0 \<le> a \<Longrightarrow> b \<le> 0 \<Longrightarrow> c_div a b \<le> 0"
  by (auto simp: c_div_def sgn_if pos_imp_zdiv_nonneg_iff neg_imp_zdiv_nonneg_iff)

lemma c_mod_nonneg:
  "0 \<le> a \<Longrightarrow> 0 \<le> c_mod a b"
  by (cases "b = 0") (auto simp: c_mod_abs sgn_if intro: pos_mod_sign)

lemma c_mod_nonpos:
  "a \<le> 0 \<Longrightarrow> c_mod a b \<le> 0"
  by (cases "b = 0") (auto simp: c_mod_abs sgn_if intro: pos_mod_sign)

lemma c_div_neg_divisor:
  "c_div a (-b) = - c_div a b"
  by (simp add: c_div_def)

lemma c_div_neg_dividend:
  "c_div (-a) b = - c_div a b"
  by (simp add: c_div_def)

lemma c_div_signed_examples:
  "map (\<lambda>(a, b). c_div a b) [(7, 3), (-7, 3), (7, -3), (-7, -3)] =
    [2, -2, -2, 2]"
  by (simp add: c_div_def)

lemma c_mod_signed_examples:
  "map (\<lambda>(a, b). c_mod a b) [(7, 3), (-7, 3), (7, -3), (-7, -3)] =
    [1, -1, 1, -1]"
  by (simp add: c_mod_def c_div_def)

definition truthy :: "int \<Rightarrow> bool" where
  [simp]: "truthy n \<longleftrightarrow> n \<noteq> 0"

fun aval :: "exp \<Rightarrow> store \<Rightarrow> int" where
    "aval (N n)     s  = n"
  | "aval (V x)     s  = s x"
  | "aval (Plus  a b) s  = aval a s + aval b s"
  | "aval (Minus a b) s  = aval a s - aval b s"
  | "aval (Times a b) s  = aval a s * aval b s"
  | "aval (Div a b) s = c_div (aval a s) (aval b s)"
  | "aval (Mod a b) s = c_mod (aval a s) (aval b s)"
  | "aval (Less a b)  s  = (if aval a s < aval b s then 1 else 0)"
  | "aval (LessEq a b) s = (if aval a s \<le> aval b s then 1 else 0)"
  | "aval (Greater a b) s = (if aval a s > aval b s then 1 else 0)"
  | "aval (GreaterEq a b) s = (if aval a s \<ge> aval b s then 1 else 0)"
  | "aval (NotEq a b) s = (if aval a s \<noteq> aval b s then 1 else 0)"
  | "aval (Eq   a b)  s  = (if aval a s = aval b s then 1 else 0)"
  | "aval (Not b)     s  = (if truthy (aval b s) then 0 else 1)"
  | "aval (And b1 b2) s  = (if truthy (aval b1 s) \<and> truthy (aval b2 s) then 1 else 0)"
  | "aval (Or  b1 b2) s  = (if truthy (aval b1 s) \<or> truthy (aval b2 s) then 1 else 0)"

text \<open>
  \<open>truthy\<close> of a compiled comparison or Boolean expression restated in plain
  Boolean form, so a caller never has to re-derive it from \<open>aval.simps\<close> and
  \<open>truthy\<close>'s own \<open>\<noteq> 0\<close> encoding through an explicit \<open>if\<close>-split.
\<close>

lemma truthy_aval_Less [simp]:
  "truthy (aval (Less a b) s) \<longleftrightarrow> aval a s < aval b s"
  by simp

lemma truthy_aval_LessEq [simp]:
  "truthy (aval (LessEq a b) s) \<longleftrightarrow> aval a s \<le> aval b s"
  by simp

lemma truthy_aval_Greater [simp]:
  "truthy (aval (Greater a b) s) \<longleftrightarrow> aval a s > aval b s"
  by simp

lemma truthy_aval_GreaterEq [simp]:
  "truthy (aval (GreaterEq a b) s) \<longleftrightarrow> aval a s \<ge> aval b s"
  by simp

lemma truthy_aval_NotEq [simp]:
  "truthy (aval (NotEq a b) s) \<longleftrightarrow> aval a s \<noteq> aval b s"
  by simp

lemma truthy_aval_Eq [simp]:
  "truthy (aval (Eq a b) s) \<longleftrightarrow> aval a s = aval b s"
  by simp

lemma truthy_aval_Not [simp]:
  "truthy (aval (Not b) s) \<longleftrightarrow> \<not> truthy (aval b s)"
  by simp

lemma truthy_aval_And [simp]:
  "truthy (aval (And b1 b2) s) \<longleftrightarrow> truthy (aval b1 s) \<and> truthy (aval b2 s)"
  by simp

lemma truthy_aval_Or [simp]:
  "truthy (aval (Or b1 b2) s) \<longleftrightarrow> truthy (aval b1 s) \<or> truthy (aval b2 s)"
  by simp

end

