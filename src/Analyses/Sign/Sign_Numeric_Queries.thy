theory Sign_Numeric_Queries
  imports Sign_Arithmetic Sign_Backward "Voblint_Domain.Numeric_Queries"
begin

section \<open>Sign interpretation of the generic numeric-query interface\<close>

text \<open>
  \<open>sound_numeric_queries\<close> (\<^theory>\<open>Voblint_Domain.Numeric_Queries\<close>) is
  the reusable interface; this theory supplies its Sign instance. None of the
  four query functions is a hand-built table: all four are Sign's instance of
  the generic derivations in \<^locale>\<open>sound_inverse_ops\<close>'s own context ---
  \<open>sign_less_true\<close>/\<open>sign_less_false\<close> read off \<open>inv_less_sign\<close>, \<open>sign_eq_true\<close>
  reads off \<open>sign_less_false\<close> in both directions, and \<open>sign_eq_false\<close> reads off
  \<open>(\<sqinter>)\<close> collapsing to \<open>SBot\<close> --- so their soundness is \<^locale>\<open>sound_inverse_ops\<close>'s,
  instantiated by @{thm [source] sign_backward_domain}.
\<close>

text \<open>
  \<open>sign_less_true_eq\<close>/\<open>sign_less_false_eq\<close>/\<open>sign_eq_true_eq\<close>/\<open>sign_eq_false_eq\<close>
  below restate each derived predicate as an explicit truth table over
  \<open>inv_less_sign\<close>/\<open>(\<sqinter>)\<close>. They are the code equations of the four predicates, and
  they guard precision: a future change to
  \<open>inv_less_sign\<close>/\<open>inv_eq_sign\<close>/\<open>(\<sqinter>)\<close> that silently narrows or widens
  what these four predicates classify breaks one of these four proofs, at the
  seven-element lattice, rather than surfacing only as a precision regression
  in a downstream analysis.
\<close>

subsection \<open>Comparison judgments\<close>

text \<open>
  \<open>sign_less_true a b\<close> holds when every concrete pair \<open>i \<in> gamma_sign a\<close>,
  \<open>j \<in> gamma_sign b\<close> satisfies \<open>i < j\<close>; \<open>sign_less_false a b\<close> when every such
  pair satisfies \<open>\<not> i < j\<close>. The two are not complements of each other:
  overlapping abstractions (e.g. \<open>SNonPos\<close> against \<open>SNonNeg\<close>) make both false,
  meaning unknown. \<open>SBot\<close> on either side makes both vacuously true.
\<close>

definition sign_less_true :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_less_true = sound_inverse_ops.less_true inv_less_sign"

lemma sign_less_true_sound:
  assumes "sign_less_true a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "i < j"
  using assms sound_inverse_ops.less_true_sound[OF
      sign_backward_domain[THEN mono_refinement.axioms(1), THEN sound_refinement.axioms(4)],
      of a b i j]
  by (simp add: sign_less_true_def)

definition sign_less_false :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_less_false = sound_inverse_ops.less_false inv_less_sign"

lemma sign_less_false_sound:
  assumes "sign_less_false a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "\<not> i < j"
  using assms sound_inverse_ops.less_false_sound[OF
      sign_backward_domain[THEN mono_refinement.axioms(1), THEN sound_refinement.axioms(4)],
      of a b i j]
  by (simp add: sign_less_false_def)

lemma sign_less_true_eq [code]: "sign_less_true a b \<longleftrightarrow>
  (fst (inv_less_sign False a b) = SBot \<or> snd (inv_less_sign False a b) = SBot)"
  by (cases a; cases b;
      simp add: sign_less_true_def sound_inverse_ops.less_true_def[OF
        sign_backward_domain[THEN mono_refinement.axioms(1), THEN sound_refinement.axioms(4)]]
                bot_sign_def is_bottom_sign_def)

lemma sign_less_false_eq [code]: "sign_less_false a b \<longleftrightarrow>
  (fst (inv_less_sign True a b) = SBot \<or> snd (inv_less_sign True a b) = SBot)"
  by (cases a; cases b;
      simp add: sign_less_false_def sound_inverse_ops.less_false_def[OF
        sign_backward_domain[THEN mono_refinement.axioms(1), THEN sound_refinement.axioms(4)]]
                bot_sign_def is_bottom_sign_def)

subsection \<open>Equality judgments\<close>

text \<open>Only \<open>SZero\<close> concretizes to a singleton, so equality is provable exactly
  there; two abstractions are provably unequal exactly when their
  concretizations are disjoint. Neither table is hand-built: \<open>sign_eq_true\<close>
  is Sign's instance of the \<open>eq_true\<close> derivation off \<open>less_false\<close> in both
  directions (integer trichotomy), and \<open>sign_eq_false\<close> is Sign's instance of
  the \<open>eq_false\<close> derivation off \<open>(\<sqinter>)\<close> collapsing to \<open>SBot\<close> (disjoint
  concretizations).\<close>

definition sign_eq_true :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_eq_true = sound_inverse_ops.eq_true inv_less_sign"

text \<open>The derived definition unfolds through \<open>less_false\<close>'s global constant, so
  the code equation is stated over the Sign-level name directly.\<close>

lemma sign_eq_true_eq [code]:
  "sign_eq_true a b \<longleftrightarrow> (sign_less_false a b \<and> sign_less_false b a)"
  by (simp add: sign_eq_true_def sign_less_false_def
    sound_inverse_ops.eq_true_def[OF
        sign_backward_domain[THEN mono_refinement.axioms(1), THEN sound_refinement.axioms(4)]])

lemma sign_eq_true_sound:
  assumes "sign_eq_true a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "i = j"
  using assms sound_inverse_ops.eq_true_sound[OF
      sign_backward_domain[THEN mono_refinement.axioms(1), THEN sound_refinement.axioms(4)],
      of a b i j]
  by (simp add: sign_eq_true_def)

definition sign_eq_false :: "sign \<Rightarrow> sign \<Rightarrow> bool" where
  "sign_eq_false = sound_inverse_ops.eq_false inf"

lemma sign_eq_false_eq [code]: "sign_eq_false a b \<longleftrightarrow> a \<sqinter> b = SBot"
  by (cases a; cases b;
      simp add: sign_eq_false_def bot_sign_def sound_inverse_ops.eq_false_def[OF
        sign_backward_domain[THEN mono_refinement.axioms(1), THEN sound_refinement.axioms(4)]]
        is_bottom_sign_def)

lemma sign_eq_false_sound:
  assumes "sign_eq_false a b" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "i \<noteq> j"
  using assms sound_inverse_ops.eq_false_sound[OF
      sign_backward_domain[THEN mono_refinement.axioms(1), THEN sound_refinement.axioms(4)],
      of a b i j]
  by (simp add: sign_eq_false_def)


subsection \<open>Goblint-style optional-Boolean queries\<close>

text \<open>
  \<open>sign_less\<close>/\<open>sign_eq\<close> are the generic packaging of the four judgments
  above, so one interpretation both introduces them and discharges the query
  interface. The \<^theory_text>\<open>defines\<close> clause is what keeps them ordinary
  top-level constants, with the code equation the check layer needs.
\<close>

global_interpretation sign_numeric_queries:
  numeric_query_judgments sign_less_true sign_less_false sign_eq_true sign_eq_false
  defines sign_less = sign_numeric_queries.query_less
    and sign_eq = sign_numeric_queries.query_eq
  by unfold_locales
     (auto intro: sign_less_true_sound sign_eq_true_sound
            dest: sign_less_false_sound sign_eq_false_sound)


end
