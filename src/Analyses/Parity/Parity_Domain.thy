theory Parity_Domain
  imports Parity_Warrowing "Voblint_Nonrelational.Abstract_Arithmetic"
begin

section \<open>Parity arithmetic and expression evaluation\<close>

subsection \<open>Abstract arithmetic\<close>

instantiation parity :: plus begin
fun plus_parity :: "parity => parity => parity" where
    "plus_parity PBot  _     = PBot"
  | "plus_parity _     PBot  = PBot"
  | "plus_parity PEven PEven = PEven"
  | "plus_parity POdd  POdd  = PEven"
  | "plus_parity PEven POdd  = POdd"
  | "plus_parity POdd  PEven = POdd"
  | "plus_parity _     _     = PTop"
instance ..
end

instantiation parity :: minus begin
fun minus_parity :: "parity => parity => parity" where
    "minus_parity PBot  _     = PBot"
  | "minus_parity _     PBot  = PBot"
  | "minus_parity PEven PEven = PEven"
  | "minus_parity POdd  POdd  = PEven"
  | "minus_parity PEven POdd  = POdd"
  | "minus_parity POdd  PEven = POdd"
  | "minus_parity _     _     = PTop"
instance ..
end

instantiation parity :: times begin
fun times_parity :: "parity => parity => parity" where
    "times_parity PBot  _     = PBot"
  | "times_parity _     PBot  = PBot"
  | "times_parity PEven _     = PEven"
  | "times_parity _     PEven = PEven"
  | "times_parity POdd  POdd  = POdd"
  | "times_parity _     _     = PTop"
instance ..
end

lemma parity_plus_sound:
  "i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow> i + j \<in> gamma_parity (a + b)"
  by (cases a; cases b; auto)

lemma parity_minus_sound:
  "i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow> i - j \<in> gamma_parity (a - b)"
  by (cases a; cases b; auto)

lemma parity_times_sound:
  "i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow> i * j \<in> gamma_parity (a * b)"
  by (cases a; cases b; auto)

subsection \<open>Monotonicity of arithmetic\<close>

lemma parity_plus_mono1: "a1 \<le> a2 \<Longrightarrow> a1 + b \<le> a2 + (b::parity)"
  unfolding less_eq_parity_def by (cases a1; cases a2; cases b; simp)
lemma parity_plus_mono2: "b1 \<le> b2 \<Longrightarrow> a + b1 \<le> a + (b2::parity)"
  unfolding less_eq_parity_def by (cases a; cases b1; cases b2; simp)
lemma parity_minus_mono1: "a1 \<le> a2 \<Longrightarrow> a1 - b \<le> a2 - (b::parity)"
  unfolding less_eq_parity_def by (cases a1; cases a2; cases b; simp)
lemma parity_minus_mono2: "b1 \<le> b2 \<Longrightarrow> a - b1 \<le> a - (b2::parity)"
  unfolding less_eq_parity_def by (cases a; cases b1; cases b2; simp)
lemma parity_times_mono1: "a1 \<le> a2 \<Longrightarrow> a1 * b \<le> a2 * (b::parity)"
  unfolding less_eq_parity_def by (cases a1; cases a2; cases b; simp)
lemma parity_times_mono2: "b1 \<le> b2 \<Longrightarrow> a * b1 \<le> a * (b2::parity)"
  unfolding less_eq_parity_def by (cases a; cases b1; cases b2; simp)

lemma parity_plus_combine_mono: "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 + b1 \<le> a2 + (b2::parity)"
  by (meson order.trans parity_plus_mono1 parity_plus_mono2)

lemma parity_minus_combine_mono: "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 - b1 \<le> a2 - (b2::parity)"
  by (meson order.trans parity_minus_mono1 parity_minus_mono2)

lemma parity_times_combine_mono: "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 * b1 \<le> a2 * (b2::parity)"
  by (meson order.trans parity_times_mono1 parity_times_mono2)

subsection \<open>Comparison and truthiness queries\<close>

text \<open>
  Parity carries no ordering information, so \<open>parity_lt\<close> is always \<open>None\<close>.
  Equality is decidable exactly when the two operands have opposite parity --
  an even value can never equal an odd one -- and truthiness is decidable
  exactly for \<open>POdd\<close>, since every odd integer is nonzero.
\<close>

fun parity_lt :: "parity \<Rightarrow> parity \<Rightarrow> bool option" where
  "parity_lt _ _ = None"

fun parity_eqb :: "parity \<Rightarrow> parity \<Rightarrow> bool option" where
    "parity_eqb PEven POdd = Some False"
  | "parity_eqb POdd PEven = Some False"
  | "parity_eqb _ _ = None"

fun parity_tobool :: "parity \<Rightarrow> bool option" where
    "parity_tobool POdd = Some True"
  | "parity_tobool _ = None"

lemma parity_lt_sound:
  "parity_lt a b = Some c \<Longrightarrow> i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow> (i < j) = c"
  by simp

lemma parity_eqb_sound:
  "parity_eqb a b = Some c \<Longrightarrow> i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow> (i = j) = c"
  by (cases a; cases b; auto)

lemma parity_tobool_sound:
  "parity_tobool a = Some c \<Longrightarrow> i \<in> gamma_parity a \<Longrightarrow> (i \<noteq> 0) = c"
  by (cases a; auto)

lemma parity_lt_mono:
  "\<not> is_empty (a1::parity) \<Longrightarrow> \<not> is_empty b1 \<Longrightarrow> a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow>
   parity_lt a2 b2 = Some c \<Longrightarrow> parity_lt a1 b1 = Some c"
  by simp

lemma parity_eqb_mono:
  "\<not> is_empty (a1::parity) \<Longrightarrow> \<not> is_empty b1 \<Longrightarrow> a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow>
   parity_eqb a2 b2 = Some c \<Longrightarrow> parity_eqb a1 b1 = Some c"
  unfolding is_empty_parity is_bottom_parity_def less_eq_parity_def
  by (cases a1; cases a2; cases b1; cases b2; simp)

lemma parity_tobool_mono:
  "\<not> is_empty (a1::parity) \<Longrightarrow> a1 \<le> a2 \<Longrightarrow> parity_tobool a2 = Some c \<Longrightarrow> parity_tobool a1 = Some c"
  unfolding is_empty_parity is_bottom_parity_def less_eq_parity_def
  by (cases a1; cases a2; simp)


definition parity_div :: "parity \<Rightarrow> parity \<Rightarrow> parity" where
  "parity_div a b = (if a = PBot \<or> b = PBot then PBot else PTop)"

definition parity_mod :: "parity \<Rightarrow> parity \<Rightarrow> parity" where
  "parity_mod a b =
    (if a = PBot \<or> b = PBot then PBot else if b = PEven then a else PTop)"

lemma parity_div_sound:
  "i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow>
    c_div i j \<in> gamma_parity (parity_div a b)"
  by (cases a; cases b; simp add: parity_div_def)

lemma parity_mod_sound:
  "i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow>
    c_mod i j \<in> gamma_parity (parity_mod a b)"
  by (cases a; cases b; auto simp: parity_mod_def c_mod_def)

lemma parity_div_mono:
  "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> parity_div a1 b1 \<le> parity_div a2 b2"
  by (cases a1; cases a2; cases b1; cases b2;
      simp add: parity_div_def less_eq_parity_def)

lemma parity_mod_mono:
  "a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> parity_mod a1 b1 \<le> parity_mod a2 b2"
  by (cases a1; cases a2; cases b1; cases b2;
      simp add: parity_mod_def less_eq_parity_def)


subsection \<open>Abstract expression evaluation\<close>

fun aval_parity :: "exp => (vname => parity) => parity" where
    "aval_parity (N n)       \<sigma> = parity_of_int n"
  | "aval_parity (V v)       \<sigma> = \<sigma> v"
  | "aval_parity (Plus  a b) \<sigma> = aval_parity a \<sigma> + aval_parity b \<sigma>"
  | "aval_parity (Minus a b) \<sigma> = aval_parity a \<sigma> - aval_parity b \<sigma>"
  | "aval_parity (Times a b) \<sigma> = aval_parity a \<sigma> * aval_parity b \<sigma>"
  | "aval_parity (Div a b) \<sigma> = parity_div (aval_parity a \<sigma>) (aval_parity b \<sigma>)"
  | "aval_parity (Mod a b) \<sigma> = parity_mod (aval_parity a \<sigma>) (aval_parity b \<sigma>)"
  | "aval_parity (Less a b)  \<sigma> =
       (if is_empty (aval_parity a \<sigma>) \<or> is_empty (aval_parity b \<sigma>) then bot
        else of_bool_option parity_of_int (parity_lt (aval_parity a \<sigma>) (aval_parity b \<sigma>)))"
  | "aval_parity (LessEq a b)  \<sigma> =
       (if is_empty (aval_parity a \<sigma>) \<or> is_empty (aval_parity b \<sigma>) then bot
        else of_bool_option parity_of_int
               (map_option HOL.Not (parity_lt (aval_parity b \<sigma>) (aval_parity a \<sigma>))))"
  | "aval_parity (Greater a b)  \<sigma> =
       (if is_empty (aval_parity a \<sigma>) \<or> is_empty (aval_parity b \<sigma>) then bot
        else of_bool_option parity_of_int (parity_lt (aval_parity b \<sigma>) (aval_parity a \<sigma>)))"
  | "aval_parity (GreaterEq a b)  \<sigma> =
       (if is_empty (aval_parity a \<sigma>) \<or> is_empty (aval_parity b \<sigma>) then bot
        else of_bool_option parity_of_int
               (map_option HOL.Not (parity_lt (aval_parity a \<sigma>) (aval_parity b \<sigma>))))"
  | "aval_parity (NotEq a b) \<sigma> =
       (if is_empty (aval_parity a \<sigma>) \<or> is_empty (aval_parity b \<sigma>) then bot
        else of_bool_option parity_of_int
               (map_option HOL.Not (parity_eqb (aval_parity a \<sigma>) (aval_parity b \<sigma>))))"
  | "aval_parity (exp.Eq a b) \<sigma> =
       (if is_empty (aval_parity a \<sigma>) \<or> is_empty (aval_parity b \<sigma>) then bot
        else of_bool_option parity_of_int (parity_eqb (aval_parity a \<sigma>) (aval_parity b \<sigma>)))"
  | "aval_parity (exp.Not a)  \<sigma> =
       (if is_empty (aval_parity a \<sigma>) then bot
        else of_bool_option parity_of_int (map_option HOL.Not (parity_tobool (aval_parity a \<sigma>))))"
  | "aval_parity (And a b)    \<sigma> =
       (if is_empty (aval_parity a \<sigma>) \<or> is_empty (aval_parity b \<sigma>) then bot
        else of_bool_option parity_of_int
               (and_opt (parity_tobool (aval_parity a \<sigma>)) (parity_tobool (aval_parity b \<sigma>))))"
  | "aval_parity (Or a b)     \<sigma> =
       (if is_empty (aval_parity a \<sigma>) \<or> is_empty (aval_parity b \<sigma>) then bot
        else of_bool_option parity_of_int
               (or_opt (parity_tobool (aval_parity a \<sigma>)) (parity_tobool (aval_parity b \<sigma>))))"

interpretation parity_arith: mono_arith_ops
    aval_parity parity_of_int "(+)" "(-)" "(*)" parity_div parity_mod
    parity_lt parity_eqb parity_tobool
  apply unfold_locales
  apply (simp_all add: parity_of_int_gamma parity_plus_sound parity_minus_sound parity_times_sound
    parity_div_sound parity_mod_sound
                        parity_plus_combine_mono parity_minus_combine_mono parity_times_combine_mono
                          parity_div_mono parity_mod_mono
                        parity_lt_sound parity_eqb_sound parity_tobool_sound[unfolded truthy_def]
                        sup_parity_def
                    del: parity_lt.simps parity_eqb.simps parity_tobool.simps)
  apply (blast intro: parity_lt_mono[unfolded is_empty_parity]
                      parity_eqb_mono[unfolded is_empty_parity]
                      parity_tobool_mono[unfolded is_empty_parity])+
  done

lemmas aval_parity_sound = parity_arith.aval_abs_sound[unfolded gamma_abs_parity]

end
