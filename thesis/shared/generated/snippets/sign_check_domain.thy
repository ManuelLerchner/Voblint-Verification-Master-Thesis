(* src/Analyses/Sign/Sign_Classify.thy *)
global_interpretation sign_check_domain:
  abstract_check_domain sign_less sign_eq gamma_state aval_sign
  defines
    sign_truthy_query = sign_check_domain.truthy_query
    and sign_check_query = sign_check_domain.check_query
    and sign_classify_check = sign_check_domain.classify_check
    and sign_eval_answer = sign_check_domain.eval_answer
    and sign_checks_proven = sign_check_domain.abstract_checks_proven
