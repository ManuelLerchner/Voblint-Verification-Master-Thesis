(* src/Analyses/Int/Int_Backward.thy *)
global_interpretation int_dom_backward_fixpoint:
    backward_domain_reductive
      intersect_int_dom_fixpoint aval_int_dom_fixpoint tobool_int_dom_fixpoint
      inv_less_int_dom_fixpoint inv_eq_int_dom_fixpoint
      inv_plus_int_dom_fixpoint inv_minus_int_dom_fixpoint inv_times_int_dom_fixpoint
  defines
    afilter_int_dom_fixpoint = int_dom_backward_fixpoint.afilter
    and feasible_int_dom_fixpoint = int_dom_backward_fixpoint.feasible
    and bfilter_int_dom_fixpoint = int_dom_backward_fixpoint.bfilter
    and branch_lifted_int_dom_fixpoint = int_dom_backward_fixpoint.branch_lifted
    and branch_int_dom_fixpoint = int_dom_backward_fixpoint.branch
    and afilter_int_dom_fixpoint_st = int_dom_backward_fixpoint.afilter_st
    and bfilter_int_dom_fixpoint_st = int_dom_backward_fixpoint.bfilter_st
    and branch_int_dom_fixpoint_st = int_dom_backward_fixpoint.branch_st
