theory Example_Congruence_Arithmetic
  imports Voblint_Analysis.Congruence_Arithmetic
begin

section \<open>Executable Congruence arithmetic regressions\<close>

lemma congruence_literal_regression:
  "congruence_of_int (-3) = mk_congruence (-3) 0"
  by eval

lemma congruence_bottom_top_regression:
  "(bot :: congruence) + top = bot \<and>
   top * (bot :: congruence) = bot \<and>
   top * congruence_of_int 0 = congruence_of_int 0"
  by eval

lemma congruence_definite_arithmetic_regression:
  "congruence_of_int (-3) + congruence_of_int 5 =
      congruence_of_int 2 \<and>
   congruence_of_int 7 - congruence_of_int 10 =
      congruence_of_int (-3) \<and>
   congruence_of_int (-3) * congruence_of_int 4 =
      congruence_of_int (-12)"
  by eval

lemma congruence_modular_arithmetic_regression:
  "mk_congruence 1 4 + mk_congruence 3 6 =
      mk_congruence 0 2 \<and>
   mk_congruence 1 4 - mk_congruence 3 6 =
      mk_congruence 0 2 \<and>
   mk_congruence 1 4 * mk_congruence 3 6 =
      mk_congruence 3 6"
  by eval

lemma congruence_negative_modulus_arithmetic_regression:
  "mk_congruence 5 (-4) + congruence_of_int (-3) =
   mk_congruence 2 4"
  by eval

lemma aval_congruence_regression:
  "aval_congruence
      (Plus (V (STR ''x'')) (N 1))
      (\<lambda>_. mk_congruence 1 2) =
   mk_congruence 0 2"
  by eval

end
