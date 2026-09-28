(* src/Analyses/Interval/Interval_Transfer.thy *)
lemma interval_check_domain:
  "abstract_check_domain interval_less interval_eq gamma_state aval_ivl"
