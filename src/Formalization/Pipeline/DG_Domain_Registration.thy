theory DG_Domain_Registration
  imports
    Run_Analysis_Sound
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.Sign_Exec"
begin

section \<open>Registered diagonal analyses\<close>

text \<open>
  Interval on the warrowing-apinis update rule and Sign on the always-join rule, each
  registered through \<^locale>\<open>unit_dg_exec_analysis\<close> from just its sound transfer, primitive
  commutation, and the vendored solver adapter.  Sign uses the \<^emph>\<open>same\<close> interface with no
  Interval-specific assumption, which validates that the registration design is not
  specialised to one domain.
\<close>

interpretation ivl_reg:
  unit_dg_exec_analysis ivl_tf ivl_tf_st
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
  by unfold_locales
     (rule ivl_is_sound_transfer ivl_tf_st_commute
           TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c)+

interpretation sign_reg:
  unit_dg_exec_analysis sign_tf sign_tf_st
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
  by unfold_locales
     (rule sign_is_sound_transfer sign_tf_st_commute
           TD_side_always_join_Interp.part_post_solution_of_solve_c)+

end
