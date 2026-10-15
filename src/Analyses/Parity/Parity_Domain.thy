theory Parity_Domain
  imports Parity_Warrowing
    "Voblint_Domain.Forward_Domain"
    "Voblint_Domain.Numeric_Queries" "Voblint_Domain.Nonrelational_State"
begin

section \<open>Parity arithmetic\<close>

text \<open>
  Parity arithmetic and comparison queries, with their soundness and monotonicity facts.
\<close>

subsection \<open>Abstract arithmetic\<close>

text \<open>
  Addition and subtraction follow the parity rules of \<open>int\<close>; a product is even
  as soon as one factor is. Any bottom operand yields \<open>PBot\<close>.
\<close>

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

text \<open>A conversion to a machine kind preserves parity (@{thm even_ik_norm_iff}), so the
  parity cast is the identity.\<close>

lemma parity_cast_sound: "i \<in> gamma_parity a \<Longrightarrow> ik_norm ik i \<in> gamma_parity a"
  by (cases a) simp_all

end
