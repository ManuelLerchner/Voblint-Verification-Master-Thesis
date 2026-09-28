(* src/Analyses/Int/Int_Transfer.thy *)
lemma int_check_domain:
  "abstract_check_domain int_less int_eq gamma_state (aval_int_dom mode)"
