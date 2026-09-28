(* src/Analyses/Congruence/Congruence_Backward.thy *)
lemma congruence_backward_domain:
  "backward_domain_mono inf aval_congruence congruence_tobool
     inv_less_congruence inv_eq_congruence
     inv_plus_congruence inv_minus_congruence inv_times_congruence"
