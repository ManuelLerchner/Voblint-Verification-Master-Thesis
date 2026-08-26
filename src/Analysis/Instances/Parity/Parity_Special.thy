theory Parity_Special
  imports Parity_Domain Voblint_Core.Special_Ops
begin

section \<open>Parity: special-call semantics\<close>

text \<open>
  \<open>parity_min\<close>/\<open>parity_max\<close> exist solely as the abstract implementation of the
  \<open>Min\<close>/\<open>Max\<close> special calls; see the analogous note on Sign's \<open>sign_min\<close>/
  \<open>sign_max\<close>. Unlike Sign and Interval, parity's result is not simply "top
  unless we're being lazy": \<open>min x y\<close> and \<open>max x y\<close> both evaluate to exactly
  one of their two arguments, never a newly synthesized value, so when both
  arguments share a known parity the result provably shares it too --
  \<open>parity_min PEven PEven = PEven\<close>, not \<open>PTop\<close>. Only a parity mismatch (or an
  unknown operand) loses the information, because then either argument could
  be the one selected.
\<close>

fun parity_min :: "parity => parity => parity" where
    "parity_min PBot _        = PBot"
  | "parity_min _    PBot     = PBot"
  | "parity_min PEven PEven   = PEven"
  | "parity_min POdd  POdd    = POdd"
  | "parity_min _    _        = PTop"

fun parity_max :: "parity => parity => parity" where
    "parity_max PBot _        = PBot"
  | "parity_max _    PBot     = PBot"
  | "parity_max PEven PEven   = PEven"
  | "parity_max POdd  POdd    = POdd"
  | "parity_max _    _        = PTop"

lemma parity_min_sound:
  assumes "i \<in> gamma_parity a" "j \<in> gamma_parity b"
  shows "min i j \<in> gamma_parity (parity_min a b)"
  using assms by (cases a; cases b; auto simp: min_def)

lemma parity_max_sound:
  assumes "i \<in> gamma_parity a" "j \<in> gamma_parity b"
  shows "max i j \<in> gamma_parity (parity_max a b)"
  using assms by (cases a; cases b; auto simp: max_def)

lemma parity_min_mono1:
  "a1 \<le> a2 \<Longrightarrow> parity_min a1 b \<le> parity_min a2 (b::parity)"
  unfolding less_eq_parity_def
  by (cases a1; cases a2; cases b; simp)

lemma parity_min_mono2:
  "b1 \<le> b2 \<Longrightarrow> parity_min a b1 \<le> parity_min a (b2::parity)"
  unfolding less_eq_parity_def
  by (cases a; cases b1; cases b2; simp)

lemma parity_min_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> parity_min a1 b1 \<le> parity_min a2 (b2::parity)"
  by (meson order.trans parity_min_mono1 parity_min_mono2)

lemma parity_max_mono1:
  "a1 \<le> a2 \<Longrightarrow> parity_max a1 b \<le> parity_max a2 (b::parity)"
  unfolding less_eq_parity_def
  by (cases a1; cases a2; cases b; simp)

lemma parity_max_mono2:
  "b1 \<le> b2 \<Longrightarrow> parity_max a b1 \<le> parity_max a (b2::parity)"
  unfolding less_eq_parity_def
  by (cases a; cases b1; cases b2; simp)

lemma parity_max_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> parity_max a1 b1 \<le> parity_max a2 (b2::parity)"
  by (meson order.trans parity_max_mono1 parity_max_mono2)

subsection \<open>Special-call dispatch\<close>

definition parity_special_ops :: "parity special_ops" where
  "parity_special_ops = (| special_min = parity_min, special_max = parity_max |)"

interpretation parity_special: sound_special_ops parity_special_ops aval_parity_t parity_cast
  by unfold_locales
     (auto simp: parity_special_ops_def gamma_parity_top
           intro: parity_min_sound parity_max_sound parity_min_combine_mono parity_max_combine_mono
                  aval_parity_t_sound aval_parity_t_mono parity_cast_sound_parity parity_cast_mono)

lemma parity_special_ops_min [simp]: "special_min parity_special_ops = parity_min"
  by (simp add: parity_special_ops_def)

lemma parity_special_ops_max [simp]: "special_max parity_special_ops = parity_max"
  by (simp add: parity_special_ops_def)

text \<open>
  \<open>special_parity\<close> is a thin alias for \<^const>\<open>sound_special_ops.special_transfer\<close>
  at its own \<open>parity_special_ops\<close>/\<open>aval_parity_t\<close> instance --
  \<open>special_transfer\<close> already evaluates \<open>Min\<close>/\<open>Max\<close>'s two elaborated operands
  and casts the result at the call's own destination kind, so there is
  nothing for a per-domain reimplementation to add.
\<close>

definition special_parity ::
    "special_call => vname => (vname => parity) => (vname => parity)"
where
  "special_parity = parity_special.special_transfer"

text \<open>The executable equation the code generator needs: the locale constant
  carries the locale's parameters, so \<open>export_code\<close> cannot see through the alias
  on its own.\<close>

lemma special_parity_code [code]:
  "special_parity sc x \<sigma> =
     \<sigma>(x := (case sc of
                Nondet_Int k \<Rightarrow> parity_cast k top
              | Min k a b \<Rightarrow> parity_cast k (parity_min (aval_parity_t a \<sigma>) (aval_parity_t b \<sigma>))
              | Max k a b \<Rightarrow> parity_cast k (parity_max (aval_parity_t a \<sigma>) (aval_parity_t b \<sigma>))))"
  unfolding special_parity_def
  by (simp add: parity_special.special_transfer_def split: special_call.splits)

lemmas special_parity_sound = parity_special.special_transfer_sound[folded special_parity_def]
lemmas special_parity_mono  = parity_special.special_transfer_mono[folded special_parity_def]

end
