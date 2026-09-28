(* src/Analyses/Congruence/Congruence_Backward.thy *)
global_interpretation congruence_backward_domain:
    backward_domain_mono inf aval_congruence congruence_tobool
      inv_less_congruence inv_eq_congruence
      inv_plus_congruence inv_minus_congruence inv_times_congruence
  defines
    afilter_congruence = congruence_backward_domain.afilter
    and feasible_congruence = congruence_backward_domain.feasible
    and bfilter_congruence = congruence_backward_domain.bfilter
    and branch_congruence = congruence_backward_domain.branch
    and branch_lifted_congruence = congruence_backward_domain.branch_lifted
    and afilter_congruence_st = congruence_backward_domain.afilter_st
    and bfilter_congruence_st = congruence_backward_domain.bfilter_st
    and branch_congruence_st = congruence_backward_domain.branch_st
