theory Int_Regression
  imports
    "Voblint_Analysis_Int.Int_Exec"
begin

section \<open>Regression assertions for the reduced product\<close>

text \<open>
  Build-checked regression assertions for the reduced product \<open>int_dom\<close>, moved
  out of the core theories. Nothing cites them; each one evaluates a fixed value
  and fails the build if the generated code changes its answer.
\<close>

subsection \<open>Check classifier\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained (\<open>top\<close>)
  environment, classified at the most precise mode, \<open>Refine_Fixpoint\<close>.\<close>

definition test_env_int_bounded :: "int_dom abs_state" where
  "test_env_int_bounded =
     (\<lambda>_. top)((STR ''x'') := int_dom_sipc SPos (Ivl (Fin 4) (Fin 7)) PTop top)"

lemma int_classify_less_proved:
  "int_classify_check Refine_Fixpoint (Less (V (STR ''x'')) (N 11)) test_env_int_bounded
     = Check_Proved"
  unfolding test_env_int_bounded_def by eval

lemma int_classify_less_refuted:
  "int_classify_check Refine_Fixpoint (Less (V (STR ''x'')) (N 0)) test_env_int_bounded
     = Check_Refuted"
  unfolding test_env_int_bounded_def by eval

lemma int_classify_eq_unknown:
  "int_classify_check Refine_Fixpoint (Eq (V (STR ''x'')) (N 5)) test_env_int_bounded
     = Check_Unknown"
  unfolding test_env_int_bounded_def by eval

subsection \<open>Refinement control\<close>

text \<open>
  Sign teaches Interval that a range's non-positive half is unreachable, and
  Congruence teaches Parity: \<open>x \<equiv> 0 (mod 4)\<close> forces \<open>x\<close> even. Neither component
  derives either fact alone.
\<close>

lemma sign_interval_positive_narrows:
  "int_ivl (refine_interval (int_dom_sip SPos (Ivl (Fin (-10)) (Fin 5)) PTop))
     = Ivl (Fin 1) (Fin 5)"
  by eval

lemma congruence_parity_mod4_narrows:
  "int_parity (refine_congruence (int_dom_sipc STop (top :: ivl) PTop (mk_congruence 0 4)))
     = PEven"
  by eval

subsection \<open>Rendering\<close>

text \<open>
  \<open>to_string\<close> on \<open>int_dom\<close>: bottom and top print their symbols, a singleton
  prints as its number, and other values list all four components.
\<close>

lemma to_string_int_dom_regression:
  "to_string (bot :: int_dom) = sym_bottom"
  "to_string (top :: int_dom) = sym_top"
  "to_string (int_dom_sipc STop (Ivl (Fin 5) (Fin 5)) PTop top) = STR ''5''"
  "to_string (int_dom_sipc SPos (Ivl (Fin 1) (Fin 9)) POdd (mk_congruence 1 2)) =
     STR ''signs:+; intervals:[1,9]; parities:1+2<int>; congruences:1+2<int>''"
  "to_string (int_dom_sipc SNonNeg (Ivl (Fin 0) PlusInf) PTop top) =
     STR ''signs:<ge>0; intervals:[0,+<infinity>]; parities:<int>; congruences:<int>''"
  by eval+

end
