theory Scratch_Parity_Buffering_Sanity
  imports "Voblint_Analysis.Parity_Exec" "Voblint_Analysis.Parity_Exec_Sound" "Voblint_VIMP.VIMP_Notation"
begin

text \<open>Sanity check for issue #121's generator-layer buffering migration, Parity
  instance: a merge node (an if/else with a check on each branch) whose RHS
  evaluation would previously issue one Side write per predecessor edge to the
  same Inr () unit global key. Confirms the buffered production \<open>parity_exec_eqs\<close>
  still terminates under the unmodified always-join solver Parity actually uses,
  and agrees with the original unbuffered \<open>side_cfg_T_eff_st\<close> generator's result.\<close>

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

definition guard_is_bot_pred :: "parity resolved_st_q \<Rightarrow> bool" where
  "guard_is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars guard_prog)"

definition guard_cfg :: cfg where
  "guard_cfg = compile_prog (prog_table guard_prog) (prog_procs guard_prog)
                  prog_main_name (prog_main guard_prog)"

definition guard_eqs_unbuffered :: "(pp, unit, parity resolved_st_q lifted) eqsT" where
  "guard_eqs_unbuffered = side_cfg_T_eff_st guard_cfg (parity_etf_st_for guard_is_bot_pred guard_gs)
                 bot cinit_parity_st ()"

value "TD_side_always_join_Interp_solve_c guard_eqs_unbuffered (cfg_exit guard_cfg) \<noteq> None"

value "TD_side_always_join_Interp_solve_c
         (parity_exec_eqs guard_is_bot_pred guard_gs (prog_table guard_prog) (prog_procs guard_prog)
            prog_main_name (prog_main guard_prog))
         (cfg_exit guard_cfg) \<noteq> None"

definition guard_unbuffered_sigma where
  "guard_unbuffered_sigma = snd (the (TD_side_always_join_Interp_solve_c guard_eqs_unbuffered (cfg_exit guard_cfg)))"

definition guard_buffered_sigma where
  "guard_buffered_sigma = snd (the (TD_side_always_join_Interp_solve_c
      (parity_exec_eqs guard_is_bot_pred guard_gs (prog_table guard_prog) (prog_procs guard_prog)
         prog_main_name (prog_main guard_prog))
      (cfg_exit guard_cfg)))"

value "guard_buffered_sigma (Inr ()) = guard_unbuffered_sigma (Inr ())"
value "guard_buffered_sigma (Inl (cfg_exit guard_cfg)) = guard_unbuffered_sigma (Inl (cfg_exit guard_cfg))"

end
