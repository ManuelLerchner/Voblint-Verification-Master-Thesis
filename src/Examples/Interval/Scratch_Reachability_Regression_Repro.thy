theory Scratch_Reachability_Regression_Repro
  imports "Voblint_Analysis.Ivl_Exec" "Voblint_Analysis.Interval_Exec_Sound" "Voblint_VIMP.VIMP_Notation"
begin

definition guard_prog :: imp_prog where
  "guard_prog = program {
     void main() {
       x := 5;
       if (x < 0) {
         __voblint_check(false)
       } else {
         __voblint_check(true)
       }
     }
   }"

lemma guard_prog_declared_global_vars [simp]:
  "declared_global_vars guard_prog = []"
  by (simp add: guard_prog_def)

abbreviation guard_gs :: "vname \<Rightarrow> bool" where
  "guard_gs \<equiv> declared_global guard_prog"

definition guard_is_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "guard_is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars guard_prog)"

definition guard_never_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "guard_never_bot_pred = (\<lambda>_. False)"

definition guard_cfg :: cfg where
  "guard_cfg = compile_prog (prog_table guard_prog) (prog_procs guard_prog)
                  prog_main_name (prog_main guard_prog)"

definition guard_eqs :: "(pp, unit, ivl resolved_st_q lifted) eqsT" where
  "guard_eqs = side_cfg_T_eff_st guard_cfg (ivl_etf_st_for guard_is_bot_pred guard_gs)
                 bot cinit_ivl_st ()"

definition guard_eqs_never_bot :: "(pp, unit, ivl resolved_st_q lifted) eqsT" where
  "guard_eqs_never_bot = side_cfg_T_eff_st guard_cfg (ivl_etf_st_for guard_never_bot_pred guard_gs)
                 bot cinit_ivl_st ()"

value "guard_cfg"

value "TD_side_always_join_Interp_solve_c guard_eqs (cfg_exit guard_cfg) \<noteq> None"

value "TD_side_warrowing_apinis_Interp_solve_c guard_eqs_never_bot (cfg_exit guard_cfg) \<noteq> None"

value "TD_side_per_origin_Interp_solve_c guard_eqs (cfg_exit guard_cfg) \<noteq> None"

text \<open>Narrow trace: extract the stable sigma from the terminating always-join
  run, then hand-run \<^const>\<open>update_global_warrowing_apinis\<close> on the exact
  per-edge Side values Statement 4's own RHS evaluation would produce, for
  both the structural-Bot equations and the never-Bot control.\<close>

definition guard_always_join_sigma where
  "guard_always_join_sigma = snd (the (TD_side_always_join_Interp_solve_c guard_eqs (cfg_exit guard_cfg)))"

value "guard_always_join_sigma (Inl (Statement 1))"
value "guard_always_join_sigma (Inl (Statement 2))"
value "guard_always_join_sigma (Inl (Statement 3))"
value "guard_always_join_sigma (Inr ())"

text \<open>Per-edge local Answer and global Side contributions Statement 4's own
  RHS evaluation issues, computed directly from the etf/tree layer at the
  stable sigma above -- exactly what the solver's \<open>E\<close>-state would see for
  each \<open>Side\<close> node it walks.\<close>

value "traverse_rhs (apply_etf_st (ivl_etf_st_for guard_is_bot_pred guard_gs) (EA_Check (Bc False)) (Statement 2)) guard_always_join_sigma"
value "sides_of_rhs (apply_etf_st (ivl_etf_st_for guard_is_bot_pred guard_gs) (EA_Check (Bc False)) (Statement 2)) guard_always_join_sigma (Inr ())"

value "traverse_rhs (apply_etf_st (ivl_etf_st_for guard_is_bot_pred guard_gs) (EA_Check (Bc True)) (Statement 3)) guard_always_join_sigma"
value "sides_of_rhs (apply_etf_st (ivl_etf_st_for guard_is_bot_pred guard_gs) (EA_Check (Bc True)) (Statement 3)) guard_always_join_sigma (Inr ())"

text \<open>Same two edges under the never-Bot control, at the never-Bot solver's
  own stable sigma -- Statement 2's local slot there is an ordinary
  \<^const>\<open>Lifted\<close> non-canonical-empty interval,value "TD_side_warrowing_apinis_Interp_solve_c
         (entry_state_eqs_prog fact_gs prog_main_name fact_prog)
         (cfg_exit fact_cfg, []) \<noteq> None" not \<^const>\<open>Bot\<close>.\<close>

definition guard_never_bot_always_join_sigma where
  "guard_never_bot_always_join_sigma =
     snd (the (TD_side_always_join_Interp_solve_c guard_eqs_never_bot (cfg_exit guard_cfg)))"

value "guard_never_bot_always_join_sigma (Inl (Statement 2))"
value "guard_never_bot_always_join_sigma (Inr ())"

value "sides_of_rhs (apply_etf_st (ivl_etf_st_for guard_never_bot_pred guard_gs) (EA_Check (Bc False)) (Statement 2)) guard_never_bot_always_join_sigma (Inr ())"
value "sides_of_rhs (apply_etf_st (ivl_etf_st_for guard_never_bot_pred guard_gs) (EA_Check (Bc True)) (Statement 3)) guard_never_bot_always_join_sigma (Inr ())"

text \<open>Voblint issue #121, generator-layer buffering fix: the production
  \<open>ivl_exec_eqs\<close> (\<open>side_cfg_T_eff_st_buffered\<close> over \<open>ivl_etf_st_contribution_for\<close>)
  must terminate under the ORIGINAL, unmodified vendored
  \<^const>\<open>TD_side_warrowing_apinis_Interp_solve_c\<close> on the exact program that hung
  the original per-edge-Side-emitting generator.\<close>

value "ivl_exec_eqs guard_is_bot_pred guard_gs (prog_table guard_prog) (prog_procs guard_prog)
         prog_main_name (prog_main guard_prog)"

value "TD_side_warrowing_apinis_Interp_solve_c
         (ivl_exec_eqs guard_is_bot_pred guard_gs (prog_table guard_prog) (prog_procs guard_prog)
            prog_main_name (prog_main guard_prog))
         (cfg_exit guard_cfg) \<noteq> None"

definition guard_buffered_sigma where
  "guard_buffered_sigma = snd (the (TD_side_warrowing_apinis_Interp_solve_c
      (ivl_exec_eqs guard_is_bot_pred guard_gs (prog_table guard_prog) (prog_procs guard_prog)
         prog_main_name (prog_main guard_prog))
      (cfg_exit guard_cfg)))"

value "guard_buffered_sigma (Inl (Statement 2))"
value "guard_buffered_sigma (Inl (Statement 3))"
value "guard_buffered_sigma (Inr ())"

text \<open>Agreement check against the always-join baseline's stable sigma.\<close>

value "guard_buffered_sigma (Inl (Statement 2)) = guard_always_join_sigma (Inl (Statement 2))"
value "guard_buffered_sigma (Inl (Statement 3)) = guard_always_join_sigma (Inl (Statement 3))"
value "guard_buffered_sigma (Inr ()) = guard_always_join_sigma (Inr ())"

end
