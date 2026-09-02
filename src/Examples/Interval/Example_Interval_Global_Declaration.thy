section \<open>What makes a variable global\<close>

theory Example_Interval_Global_Declaration
  imports
    "Voblint_Analysis.Interval_Checks"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Solver.TD_Solver_Menu"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Examples.Example_Inc_Proc"
begin

text \<open>
  A variable is global because its program declared it so, never because of how
  it is spelled. \<^const>\<open>inc_program\<close> is built to make the difference visible: it
  declares \<open>counter\<close>, whose name suggests nothing, and uses a local \<open>Glocal\<close>,
  whose name suggests a global. The classification itself is already settled
  there off \<^const>\<open>declared_global\<close> alone; what this theory adds is that the
  analysis pipeline agrees, by solving the program and reading the two values
  back rather than asserting them.
\<close>

abbreviation inc_gs :: "vname \<Rightarrow> bool" where
  "inc_gs \<equiv> declared_global inc_program"

definition inc_decl_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "inc_decl_eqs =
     dg_gen_of (ownership_split_dg_spec_st_for inc_gs (ivl_tf_st_for inc_gs) (ivl_enter_st_for inc_gs))
       inc_g bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

lemma inc_decl_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c inc_decl_eqs (cfg_exit inc_g, ()) \<noteq> None"
  by eval

definition inc_decl_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
where
  "inc_decl_sol = TD_side_warrowing_apinis_Interp_solve inc_decl_eqs (cfg_exit inc_g, ())"

text \<open>
  \<open>Glocal\<close> keeps its exact value: it is local, so it is never routed through the
  shared global channel, whatever its spelling. \<open>counter\<close> is the declared global
  and reaches the exit widened, because every write to it lands on the one
  shared unknown -- an imprecision of the ownership routing, not of the
  classification. The next theory isolates that effect on its own.
\<close>

lemma inc_decl_glocal_exact:
  "fun_of_exec_dg_st_for inc_gs
     (dg_hook_D (snd inc_decl_sol) (FunctionResult prog_main_name)
        \<squnion> dg_hook_G (snd inc_decl_sol)) (STR ''Glocal'')
   = Ivl (Fin 1) (Fin 1)"
  by eval

lemma inc_decl_counter_widened:
  "fun_of_exec_dg_st_for inc_gs
     (dg_hook_D (snd inc_decl_sol) (FunctionResult prog_main_name)
        \<squnion> dg_hook_G (snd inc_decl_sol)) (STR ''counter'')
   = Ivl (Fin 0) PlusInf"
  by eval

end
