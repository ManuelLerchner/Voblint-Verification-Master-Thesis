(* src/Analyses/Interval/Interval_Backward.thy *)
global_interpretation ivl_backward_domain:
    backward_domain_mono intersect_ivl aval_ivl interval_tobool
                    inv_less_ivl inv_eq_ivl inv_conservative inv_conservative inv_conservative
  defines
    afilter_ivl = ivl_backward_domain.afilter
    and feasible_ivl = ivl_backward_domain.feasible
    and bfilter_ivl = ivl_backward_domain.bfilter
    and branch_ivl = ivl_backward_domain.branch
    and branch_lifted_ivl = ivl_backward_domain.branch_lifted
    and afilter_ivl_st = ivl_backward_domain.afilter_st
    and bfilter_ivl_st = ivl_backward_domain.bfilter_st
    and branch_ivl_st = ivl_backward_domain.branch_st
