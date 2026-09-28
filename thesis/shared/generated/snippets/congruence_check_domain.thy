(* src/Analyses/Congruence/Congruence_Transfer.thy *)
lemma congruence_check_domain:
  "abstract_check_domain congruence_lt congruence_eqb gamma_state aval_congruence"
