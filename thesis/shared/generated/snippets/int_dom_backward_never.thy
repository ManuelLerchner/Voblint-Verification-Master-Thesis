(* src/Analyses/Int/Int_Backward.thy *)
global_interpretation int_dom_backward_never:
    backward_domain_mono
      intersect_int_dom_never aval_int_dom_never tobool_int_dom_never
      inv_less_int_dom_never inv_eq_int_dom_never
      inv_plus_int_dom_never inv_minus_int_dom_never inv_times_int_dom_never
  defines
    afilter_int_dom_never = int_dom_backward_never.afilter
    and feasible_int_dom_never = int_dom_backward_never.feasible
    and bfilter_int_dom_never = int_dom_backward_never.bfilter
    and branch_int_dom_never = int_dom_backward_never.branch
    and branch_lifted_int_dom_never = int_dom_backward_never.branch_lifted
    and afilter_int_dom_never_st = int_dom_backward_never.afilter_st
    and bfilter_int_dom_never_st = int_dom_backward_never.bfilter_st
    and branch_int_dom_never_st = int_dom_backward_never.branch_st
