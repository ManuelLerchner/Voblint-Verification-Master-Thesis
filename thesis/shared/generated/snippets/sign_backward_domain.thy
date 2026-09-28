(* src/Analyses/Sign/Sign_Backward.thy *)
lemma sign_backward_domain:
  "backward_domain_mono inf aval_sign sign_tobool
     inv_less_sign inv_eq_sign inv_conservative inv_conservative inv_conservative"
