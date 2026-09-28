(* src/Analyses/Int/Int_Backward.thy *)
lemma int_backward_domain:
  "backward_domain_reductive (intersect_int_dom_mode mode) (aval_int_dom mode) int_dom_tobool
     (inv_less_int_dom mode) (inv_eq_int_dom mode)
     (inv_plus_int_dom mode) (inv_minus_int_dom mode) (inv_times_int_dom mode)"
