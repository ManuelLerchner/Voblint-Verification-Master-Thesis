section \<open>What a declared global costs in precision\<close>

theory Example_Interval_Global_Sequential_Precision
  imports
    "Voblint_Analysis.Interval_Checks"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Solver.TD_Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation"
begin

text \<open>
  \<open>x := 0; x := 1; check(x = 1)\<close> on a declared global. Read as a program the
  check is plainly true: the second write overwrites the first, and nothing
  runs in between. The analysis answers \<^const>\<open>Check_Unknown\<close>.

  The mechanism is ownership routing, not the interval domain. A declared
  global is published to one shared unknown, which accumulates the join of
  every write to it anywhere in the program; a read at any program point sees
  that accumulated value. Here the two writes give \<open>[0,0] \<squnion> [1,1] = [0,1]\<close>, and
  \<open>[0,1] = 1\<close> is not decidable. Making the same program's variable local proves
  the check, which is what pins the cause: this is flow insensitivity of the
  global channel, and the same program would be exact under any analysis that
  tracked the global per program point.

  This is a known imprecision, deliberately recorded as one. The assertion
  below is \<^const>\<open>Check_Unknown\<close> because that is what the analyzer computes;
  asserting \<^const>\<open>Check_Proved\<close> here would claim precision the pipeline does
  not have.
\<close>

subsection \<open>The same program with the variable global, then local\<close>

definition seq_global_prog :: imp_prog where
  "seq_global_prog = program {
     global x;
     void main() { x := 0; x := 1; __voblint_check(x == 1) }
   }"

definition seq_local_prog :: imp_prog where
  "seq_local_prog = program {
     void main() { x := 0; x := 1; __voblint_check(x == 1) }
   }"

lemma seq_global_x_is_global [simp]: "declared_global seq_global_prog (STR ''x'')"
  by (simp add: seq_global_prog_def)

lemma seq_local_x_not_global [simp]: "\<not> declared_global seq_local_prog (STR ''x'')"
  by (simp add: seq_local_prog_def)

subsection \<open>Solving both\<close>

definition seq_global_cfg :: cfg where
  "seq_global_cfg = compile_prog (prog_table seq_global_prog) (prog_procs seq_global_prog)"

definition seq_local_cfg :: cfg where
  "seq_local_cfg = compile_prog (prog_table seq_local_prog) (prog_procs seq_local_prog)"

definition seq_global_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "seq_global_eqs =
     dg_gen_of
       (unit_dg_spec_st_for (declared_global seq_global_prog)
          (ivl_tf_st_for (declared_global seq_global_prog))
          (ivl_enter_st_for (declared_global seq_global_prog)))
       seq_global_cfg bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

definition seq_local_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "seq_local_eqs =
     dg_gen_of
       (unit_dg_spec_st_for (declared_global seq_local_prog)
          (ivl_tf_st_for (declared_global seq_local_prog))
          (ivl_enter_st_for (declared_global seq_local_prog)))
       seq_local_cfg bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

lemma seq_global_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c seq_global_eqs (cfg_exit seq_global_cfg, ()) \<noteq> None"
  by eval

lemma seq_local_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c seq_local_eqs (cfg_exit seq_local_cfg, ()) \<noteq> None"
  by eval

definition seq_global_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
where
  "seq_global_sol =
     TD_side_warrowing_apinis_Interp_solve seq_global_eqs (cfg_exit seq_global_cfg, ())"

definition seq_local_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
where
  "seq_local_sol =
     TD_side_warrowing_apinis_Interp_solve seq_local_eqs (cfg_exit seq_local_cfg, ())"

subsection \<open>The two verdicts\<close>

text \<open>The check node is the same in both programs; only the declaration differs.\<close>

lemma seq_global_checks:
  "checks seq_global_cfg = {(Statement 2, exp.Eq (V (STR ''x'')) (N 1))}"
  unfolding seq_global_cfg_def by eval

lemma seq_local_checks:
  "checks seq_local_cfg = {(Statement 2, exp.Eq (V (STR ''x'')) (N 1))}"
  unfolding seq_local_cfg_def by eval

text \<open>Global: the shared unknown holds \<open>[0,1]\<close>, so the check cannot be decided.\<close>

lemma seq_global_check_unknown:
  "interval_classify_check (exp.Eq (V (STR ''x'')) (N 1))
     (fun_of_exec_dg_st_for (declared_global seq_global_prog)
       (dg_hook_D (snd seq_global_sol) (Statement 2)
          \<squnion> dg_hook_G (snd seq_global_sol)))
   = Check_Unknown"
  by eval

text \<open>Local: the value is carried per program point and the check is decided.\<close>

lemma seq_local_check_proved:
  "interval_classify_check (exp.Eq (V (STR ''x'')) (N 1))
     (fun_of_exec_dg_st_for (declared_global seq_local_prog)
       (dg_hook_D (snd seq_local_sol) (Statement 2)
          \<squnion> dg_hook_G (snd seq_local_sol)))
   = Check_Proved"
  by eval

end
