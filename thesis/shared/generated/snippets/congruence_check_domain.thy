(* src/Analyses/Congruence/Congruence_Classify.thy *)
global_interpretation congruence_check_domain:
  abstract_check_domain congruence_lt congruence_eqb gamma_state aval_congruence
  defines
    congruence_truthy_query = congruence_check_domain.truthy_query
    and congruence_check_query = congruence_check_domain.check_query
    and congruence_classify_check = congruence_check_domain.classify_check
    and congruence_eval_answer = congruence_check_domain.eval_answer
    and congruence_checks_proven = congruence_check_domain.abstract_checks_proven
