(* src/Analyses/Sign/Sign_Backward.thy *)
global_interpretation sign_backward_domain:
    backward_domain_mono inf aval_sign sign_tobool
                    inv_less_sign inv_eq_sign inv_conservative inv_conservative inv_conservative
  defines
    afilter_sign = sign_backward_domain.afilter
    and feasible_sign = sign_backward_domain.feasible
    and bfilter_sign = sign_backward_domain.bfilter
    and branch_sign = sign_backward_domain.branch
    and branch_lifted_sign = sign_backward_domain.branch_lifted
    and afilter_sign_st = sign_backward_domain.afilter_st
    and bfilter_sign_st = sign_backward_domain.bfilter_st
    and branch_sign_st = sign_backward_domain.branch_st
    and afilter_sign_st_lift = sign_backward_domain.afilter_st_lift
    and bfilter_sign_st_lift = sign_backward_domain.bfilter_st_lift
    and sign_less_true_of_inv = sign_backward_domain.less_true
    and sign_less_false_of_inv = sign_backward_domain.less_false
    and sign_eq_true_of_less = sign_backward_domain.eq_true
    and sign_eq_false_of_intersection = sign_backward_domain.eq_false
