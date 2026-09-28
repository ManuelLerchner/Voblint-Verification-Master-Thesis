(* src/Analyses/Parity/Parity_Backward.thy *)
lemma parity_backward_domain:
  "backward_domain_mono inf aval_parity parity_tobool
     inv_conservative inv_eq_parity inv_plus_parity inv_minus_parity inv_times_parity"
