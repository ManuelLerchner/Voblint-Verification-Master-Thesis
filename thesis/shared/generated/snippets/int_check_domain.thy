(* src/Analyses/Int/Int_Classify.thy *)
global_interpretation int_check_domain:
  abstract_check_domain int_less int_eq gamma_state aval_int_dom_fixpoint
  defines
    int_truthy_query = int_check_domain.truthy_query
    and int_check_query = int_check_domain.check_query
    and int_classify_check = int_check_domain.classify_check
    and int_eval_answer = int_check_domain.eval_answer
    and int_checks_proven = int_check_domain.abstract_checks_proven
