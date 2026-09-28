(* src/Analyses/Interval/Interval_Classify.thy *)
global_interpretation interval_check_domain:
  abstract_check_domain interval_less interval_eq gamma_state aval_ivl
  defines
    interval_truthy_query = interval_check_domain.truthy_query
    and interval_check_query = interval_check_domain.check_query
    and interval_classify_check = interval_check_domain.classify_check
    and interval_eval_answer = interval_check_domain.eval_answer
    and interval_checks_proven = interval_check_domain.abstract_checks_proven
