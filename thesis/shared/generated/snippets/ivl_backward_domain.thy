(* src/Analyses/Interval/Interval_Backward.thy *)
lemma ivl_backward_domain:
  "backward_domain_mono intersect_ivl aval_ivl interval_tobool
     inv_less_ivl inv_eq_ivl inv_conservative inv_conservative inv_conservative"
