theory DG_Domain_Registration
  imports
    Run_Analysis_Sound
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Parity_Exec"
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
  unit_dg_exec_analysis is_global ivl_tf ivl_tf_st ivl_enter_st
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
  apply unfold_locales
  apply (simp_all add: fun_of_exec_dg_st_for_is_global)
  apply (rule ivl_is_sound_transfer ivl_tf_st_commute ivl_enter_st_commute
              ivl_tf_st_ret_None ivl_tf_st_ret_Some
              TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c)+
  apply auto
  done

interpretation sign_reg:
  unit_dg_exec_analysis is_global sign_tf sign_tf_st sign_enter_st
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
  apply unfold_locales
  apply (simp_all add: fun_of_exec_dg_st_for_is_global)
  apply (rule sign_is_sound_transfer sign_tf_st_commute sign_enter_st_commute
              sign_tf_st_ret_none sign_tf_st_ret_some
              TD_side_always_join_Interp.part_post_solution_of_solve_c)+
  apply auto
  done

interpretation parity_reg:
  unit_dg_exec_analysis is_global parity_tf parity_tf_st parity_enter_st
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
  apply unfold_locales
  apply (simp_all add: fun_of_exec_dg_st_for_is_global)
  apply (rule parity_is_sound_transfer parity_tf_st_commute parity_enter_st_commute
              parity_tf_st_ret_none parity_tf_st_ret_some
              TD_side_always_join_Interp.part_post_solution_of_solve_c)+
  apply auto
  done

end
