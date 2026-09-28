(* src/Analyses/Parity/Parity_Classify.thy *)
global_interpretation parity_check_domain:
  abstract_check_domain parity_less parity_eq gamma_state aval_parity
  defines
    parity_truthy_query = parity_check_domain.truthy_query
    and parity_check_query = parity_check_domain.check_query
    and parity_classify_check = parity_check_domain.classify_check
    and parity_eval_answer = parity_check_domain.eval_answer
    and parity_checks_proven = parity_check_domain.abstract_checks_proven
