(* src/Analyses/Int/Int_Backward.thy *)
global_interpretation int_dom_backward_once:
    backward_domain_mono
      intersect_int_dom_once aval_int_dom_once tobool_int_dom_once
      inv_less_int_dom_once inv_eq_int_dom_once
      inv_plus_int_dom_once inv_minus_int_dom_once inv_times_int_dom_once
  defines
    afilter_int_dom_once = int_dom_backward_once.afilter
    and feasible_int_dom_once = int_dom_backward_once.feasible
    and bfilter_int_dom_once = int_dom_backward_once.bfilter
    and branch_int_dom_once = int_dom_backward_once.branch
    and branch_lifted_int_dom_once = int_dom_backward_once.branch_lifted
    and afilter_int_dom_once_st = int_dom_backward_once.afilter_st
    and bfilter_int_dom_once_st = int_dom_backward_once.bfilter_st
    and branch_int_dom_once_st = int_dom_backward_once.branch_st
