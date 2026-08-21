theory Example_Congruence_Backward
  imports Voblint_Analysis.Congruence_Backward
begin

section \<open>Executable Congruence backward-analysis regressions\<close>

lemma congruence_intersection_crt_regression:
  "intersect_congruence (mk_congruence 1 4) (mk_congruence 3 6) =
   mk_congruence 9 12"
  by eval

lemma congruence_intersection_incompatible_regression:
  "intersect_congruence (mk_congruence 0 2) (mk_congruence 1 2) = bot"
  by eval

lemma inv_plus_congruence_regression:
  "inv_plus_congruence (mk_congruence 2 4)
      (top :: congruence) (congruence_of_int 1) =
   (mk_congruence 1 4, congruence_of_int 1)"
  by eval

lemma inv_minus_congruence_regression:
  "inv_minus_congruence (mk_congruence 2 4)
      (top :: congruence) (congruence_of_int 1) =
   (mk_congruence 3 4, congruence_of_int 1)"
  by eval

lemma inv_times_congruence_modular_regression:
  "inv_times_congruence (mk_congruence 2 6)
      (top :: congruence) (congruence_of_int 2) =
   (mk_congruence 1 3, congruence_of_int 2)"
  by eval

lemma inv_times_congruence_incompatible_regression:
  "fst (inv_times_congruence (mk_congruence 1 2)
      (top :: congruence) (congruence_of_int 2)) = bot"
  by eval

lemma inv_times_congruence_definite_regression:
  "inv_times_congruence (congruence_of_int 12)
      (top :: congruence) (congruence_of_int 3) =
   (congruence_of_int 4, congruence_of_int 3)"
  by eval

lemma inv_times_congruence_nonsingleton_fallback:
  "inv_times_congruence top
      (mk_congruence 1 4) (mk_congruence 3 6) =
   (mk_congruence 1 4, mk_congruence 3 6)"
  by eval

definition congruence_test_env :: "congruence abs_state" where
  "congruence_test_env = (\<lambda>_. top)"

lemma bfilter_congruence_linear_equality_regression:
  "bfilter_congruence
      (Eq (Plus (V (STR ''x'')) (N 1)) (N 3)) True
      congruence_test_env (STR ''x'') = congruence_of_int 2"
  unfolding congruence_test_env_def
  by eval

end
