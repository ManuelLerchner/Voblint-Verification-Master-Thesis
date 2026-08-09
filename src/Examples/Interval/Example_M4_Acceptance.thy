section \<open>M4 (G4) Phase 1 acceptance: A1/A2/A3\<close>

theory Example_M4_Acceptance
  imports
    "Voblint_Analysis.Interval_Checks"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Core.Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation"
    Example_Inc_Proc
    Example_Interval_Placement
begin

text \<open>
  The three Phase 1 acceptance cases named in the M4 design doc (section 6,
  "Analysis roadmap"): A1 (explicitly declared mixed interval analysis), A2
  (fully flow-sensitive sequential globals), A3 (selectively flow-sensitive
  variables). Each subsection below computes, not asserts, the values the
  design doc's own success criteria name.
\<close>

subsection \<open>A1 -- explicitly declared mixed interval analysis\<close>

text \<open>
  Reuses \<^const>\<open>inc_program\<close> (\<open>Example_Inc_Proc\<close>) rather than inventing a
  second witness: \<open>counter\<close> is the declared global with no naming hint,
  \<open>Glocal\<close> the \<open>G\<close>-prefixed local, and both classifications
  (\<open>inc_program_counter_global\<close>/\<open>inc_program_glocal_not_global\<close>) are
  already proven there off \<^const>\<open>declared_global\<close> alone. What's new here is
  running the mixed local/global program through the executable, placement-
  aware D/G pipeline (classic placement: \<open>counter\<close> side-effected, \<open>Glocal\<close>
  flow-sensitive because it is local) and reading off real computed values.
\<close>

fun a1_node_owner :: "pp \<Rightarrow> pname" where
  "a1_node_owner (FunctionEntry p) = p"
| "a1_node_owner (FunctionResult p) = p"
| "a1_node_owner (Statement n) = (if n < 2 then (STR ''p'') else prog_main_name)"

definition a1_locations_of :: "pp \<Rightarrow> location list" where
  "a1_locations_of node = scope_locations inc_program (a1_node_owner node)"

definition a1_dg_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "a1_dg_eqs =
    placed_dg_gen_of_strict (declared_global inc_program) a1_node_owner a1_locations_of
      classic_keep_local classic_publish_side
      (ivl_tf_st_for (declared_global inc_program)) (ivl_enter_st_for (declared_global inc_program))
      inc_g bot cinit_ivl_st
      (project_resolved_on_strict prog_main_name
        (a1_locations_of (cfg_entry inc_g)) classic_publish_side cinit_ivl_st)"

definition a1_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
where
  "a1_sol = TD_side_warrowing_apinis_Interp_solve a1_dg_eqs (cfg_exit inc_g, ())"

lemma a1_terminates: "TD_side_warrowing_apinis_Interp_solve_c a1_dg_eqs (cfg_exit inc_g, ()) \<noteq> None"
  by eval

text \<open>The mixed-placement result, computed: the declared global \<open>counter\<close>
  reaches the exit as \<open>[0, +inf)\<close> under classic (exclusive, side-effected)
  placement -- imprecise, but this is a placement-precision fact, not a
  storage-classification fact. \<open>Glocal\<close> stays exactly \<open>[1, 1]\<close>: never
  routed through the side channel because it is local, regardless of its
  \<open>G\<close> spelling.\<close>

lemma a1_counter_result:
  "fun_of_exec_dg_st_for (declared_global inc_program)
     (dg_hook_D (snd a1_sol) (FunctionResult prog_main_name) \<squnion> dg_hook_G (snd a1_sol)) (STR ''counter'')
   = Ivl (Fin 0) PlusInf"
  by eval

lemma a1_glocal_result:
  "fun_of_exec_dg_st_for (declared_global inc_program)
     (dg_hook_D (snd a1_sol) (FunctionResult prog_main_name) \<squnion> dg_hook_G (snd a1_sol)) (STR ''Glocal'')
   = Ivl (Fin 1) (Fin 1)"
  by eval

text \<open>
  \<^bold>\<open>Baseline agreement.\<close> \<^const>\<open>declared_global\<close> decides membership off the
  program's own \<open>global\<close> declarations (\<^const>\<open>declared_global_vars\<close>) alone;
  classic placement's transfer and combine behavior is a function of that
  classification, never of spelling. \<open>counter\<close> is unambiguously the
  program's one declared global -- it is the only name in \<open>global ...;\<close> --
  so \<open>a1_counter_result\<close> is the unique value classic placement can produce
  for this program: no alternative classifier could route \<open>counter\<close>
  differently without contradicting its declaration.
\<close>

subsection \<open>A2 -- fully flow-sensitive sequential globals\<close>

text \<open>
  \<open>global x; x := 0; x := 1; __voblint_check(x == 1)\<close>, exactly as specified.
  Two placements of the same program, same classifier, same check: classic
  (\<open>x\<close> exclusively side-effected) against all-flow-sensitive
  (\<open>keep_local = True\<close>, \<open>publish_side = False\<close> for every location, so the
  shared \<open>G\<close> unknown never receives a write and stays \<open>bot\<close> for the whole
  solve -- \<open>d \<squnion> g = d \<squnion> bot = d\<close>, so nothing dilutes the flow-sensitive
  read). This is not assumed: both solves are run and both check results are
  computed via \<^const>\<open>interval_classify_check\<close>, the same node-local
  classifier \<^theory>\<open>Voblint_Analysis.Interval_Checks\<close> already proves sound
  and \<open>Example_Checks_Store_Only\<close> exercises on locals.
\<close>

definition a2_program :: imp_prog where
  "a2_program = program {
     global x;
     void main() { x := 0; x := 1; __voblint_check(x == 1) }
   }"

abbreviation a2_gs :: "vname \<Rightarrow> bool" where
  "a2_gs \<equiv> declared_global a2_program"

lemma a2_x_global [simp]: "a2_gs (STR ''x'')"
  by (simp add: a2_program_def)

definition a2_cfg :: cfg where
  "a2_cfg = compile_prog (prog_table a2_program) (prog_procs a2_program) prog_main_name (prog_main a2_program)"

lemma a2_checks_eval: "checks a2_cfg = {(Statement 2, bexp.Eq (V (STR ''x'')) (N 1))}"
  unfolding a2_cfg_def by eval

fun a2_node_owner :: "pp \<Rightarrow> pname" where
  "a2_node_owner _ = prog_main_name"

definition a2_locations_of :: "pp \<Rightarrow> location list" where
  "a2_locations_of node = scope_locations a2_program (a2_node_owner node)"

definition a2_keep_flowsens_sl :: "scoped_location \<Rightarrow> bool" where
  "a2_keep_flowsens_sl loc = True"

definition a2_publish_flowsens_sl :: "scoped_location \<Rightarrow> bool" where
  "a2_publish_flowsens_sl loc = False"

definition a2_dg_eqs_classic ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "a2_dg_eqs_classic =
    placed_dg_gen_of_strict a2_gs a2_node_owner a2_locations_of
      classic_keep_local classic_publish_side
      (ivl_tf_st_for a2_gs) (ivl_enter_st_for a2_gs)
      a2_cfg bot cinit_ivl_st
      (project_resolved_on_strict prog_main_name
        (a2_locations_of (cfg_entry a2_cfg)) classic_publish_side cinit_ivl_st)"

definition a2_dg_eqs_flowsens ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "a2_dg_eqs_flowsens =
    placed_dg_gen_of_strict a2_gs a2_node_owner a2_locations_of
      a2_keep_flowsens_sl a2_publish_flowsens_sl
      (ivl_tf_st_for a2_gs) (ivl_enter_st_for a2_gs)
      a2_cfg bot cinit_ivl_st
      (project_resolved_on_strict prog_main_name
        (a2_locations_of (cfg_entry a2_cfg)) a2_publish_flowsens_sl cinit_ivl_st)"

definition a2_sol_classic ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
where
  "a2_sol_classic = TD_side_warrowing_apinis_Interp_solve a2_dg_eqs_classic (cfg_exit a2_cfg, ())"

definition a2_sol_flowsens ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
where
  "a2_sol_flowsens = TD_side_warrowing_apinis_Interp_solve a2_dg_eqs_flowsens (cfg_exit a2_cfg, ())"

lemma a2_classic_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c a2_dg_eqs_classic (cfg_exit a2_cfg, ()) \<noteq> None"
  by eval

lemma a2_flowsens_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c a2_dg_eqs_flowsens (cfg_exit a2_cfg, ()) \<noteq> None"
  by eval

text \<open>The computed environment at the check node (\<open>Statement 2\<close>, the point
  \<open>__voblint_check(x == 1)\<close> compiles to): classic joins both writes into
  \<open>[0, +inf)\<close> and cannot prove the assertion; all-flow-sensitive keeps the
  exact post-write value \<open>[1, 1]\<close>.\<close>

lemma a2_classic_env:
  "fun_of_exec_dg_st_for a2_gs
     (dg_hook_D (snd a2_sol_classic) (Statement 2) \<squnion> dg_hook_G (snd a2_sol_classic)) (STR ''x'')
   = Ivl (Fin 0) PlusInf"
  by eval

lemma a2_flowsens_env:
  "fun_of_exec_dg_st_for a2_gs
     (dg_hook_D (snd a2_sol_flowsens) (Statement 2) \<squnion> dg_hook_G (snd a2_sol_flowsens)) (STR ''x'')
   = Ivl (Fin 1) (Fin 1)"
  by eval

text \<open>The check itself, discharged through \<^const>\<open>interval_classify_check\<close>:
  \<open>Check_Unknown\<close> under classic, \<open>Check_Proved\<close> under all-flow-sensitive.
  This is A2's required result: semantic globalness (\<open>a2_x_global\<close>) does not
  force flow insensitivity -- placement, not storage class, decides it.\<close>

lemma a2_classic_check_unknown:
  "interval_classify_check (bexp.Eq (V (STR ''x'')) (N 1))
     (fun_of_exec_dg_st_for a2_gs
       (dg_hook_D (snd a2_sol_classic) (Statement 2) \<squnion> dg_hook_G (snd a2_sol_classic)))
   = Check_Unknown"
  by eval

lemma a2_flowsens_check_proved:
  "interval_classify_check (bexp.Eq (V (STR ''x'')) (N 1))
     (fun_of_exec_dg_st_for a2_gs
       (dg_hook_D (snd a2_sol_flowsens) (Statement 2) \<squnion> dg_hook_G (snd a2_sol_flowsens)))
   = Check_Proved"
  by eval

subsection \<open>A3 -- selectively flow-sensitive variables\<close>

text \<open>
  Reuses \<^const>\<open>placement_prog\<close> (\<open>Example_Interval_Placement\<close>) rather than a
  new program: \<open>balance\<close> and \<open>request_count\<close> are already the two declared
  globals with independent placement, and \<^const>\<open>placement_dg_td_sol\<close> (that
  theory's own selective-placement executable solve) is cited directly below
  instead of re-solved. What's new here is running the identical program
  under classic and all-flow-sensitive placement too, so all three policies
  A3 names are compared on the same source, holding the program fixed and
  varying only placement -- the opposite axis from that theory's own
  \<open>section 3090\<close> flat-vs-D/G-split comparison, which holds placement fixed
  and varies architecture.
\<close>

definition a3_keep_flowsens :: "scoped_location \<Rightarrow> bool" where
  "a3_keep_flowsens loc = True"

definition a3_publish_flowsens :: "scoped_location \<Rightarrow> bool" where
  "a3_publish_flowsens loc = False"

definition a3_dg_eqs_classic ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "a3_dg_eqs_classic =
    placed_dg_gen_of_strict (declared_global placement_prog) placement_node_owner
      placement_locations_of classic_keep_local classic_publish_side
      (ivl_tf_st_for (declared_global placement_prog)) (ivl_enter_st_for (declared_global placement_prog))
      placement_cfg bot cinit_ivl_st
      (project_resolved_on_strict prog_main_name
        (placement_locations_of (cfg_entry placement_cfg)) classic_publish_side cinit_ivl_st)"

definition a3_dg_eqs_flowsens ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "a3_dg_eqs_flowsens =
    placed_dg_gen_of_strict (declared_global placement_prog) placement_node_owner
      placement_locations_of a3_keep_flowsens a3_publish_flowsens
      (ivl_tf_st_for (declared_global placement_prog)) (ivl_enter_st_for (declared_global placement_prog))
      placement_cfg bot cinit_ivl_st
      (project_resolved_on_strict prog_main_name
        (placement_locations_of (cfg_entry placement_cfg)) a3_publish_flowsens cinit_ivl_st)"

definition a3_sol_classic ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
where
  "a3_sol_classic = TD_side_warrowing_apinis_Interp_solve a3_dg_eqs_classic (cfg_exit placement_cfg, ())"

definition a3_sol_flowsens ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
where
  "a3_sol_flowsens = TD_side_warrowing_apinis_Interp_solve a3_dg_eqs_flowsens (cfg_exit placement_cfg, ())"

lemma a3_classic_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c a3_dg_eqs_classic (cfg_exit placement_cfg, ()) \<noteq> None"
  by eval

lemma a3_flowsens_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c a3_dg_eqs_flowsens (cfg_exit placement_cfg, ()) \<noteq> None"
  by eval

text \<open>Result comparison, all three policies, same program, same target
  variable (\<open>answer\<close>, main's caller-local binding \<open>add(3)\<close>'s return into).

  \<^item> classic: \<open>[0, +inf)\<close>, \<open>10\<close> equations
  \<^item> all-flow-sensitive: \<open>[3, 3]\<close>, \<open>10\<close> equations
  \<^item> selective: \<open>[3, 3]\<close>, \<open>10\<close> equations
\<close>

lemma a3_classic_answer:
  "fun_of_exec_dg_st_for (declared_global placement_prog)
     (dg_hook_D (snd a3_sol_classic) (Statement 6) \<squnion> dg_hook_G (snd a3_sol_classic)) (STR ''answer'')
   = Ivl (Fin 0) PlusInf"
  by eval

lemma a3_flowsens_answer:
  "fun_of_exec_dg_st_for (declared_global placement_prog)
     (dg_hook_D (snd a3_sol_flowsens) (Statement 6) \<squnion> dg_hook_G (snd a3_sol_flowsens)) (STR ''answer'')
   = Ivl (Fin 3) (Fin 3)"
  by eval

text \<open>The selective result is cited from \<open>Example_Interval_Placement\<close>
  directly, not re-solved: \<open>placement_dg_td_values\<close> there already proves
  \<open>answer = Ivl (Fin 3) (Fin 3)\<close> for \<^const>\<open>placement_dg_td_sol\<close>.\<close>

lemma a3_selective_answer:
  "lookup_resolved_st_q (locals (snd placement_dg_td_sol (Inl (Statement 6, ()))))
     (Local_Location (STR ''answer'')) = Ivl (Fin 3) (Fin 3)"
  by (rule placement_dg_td_values)

lemma a3_classic_equations: "card (fst a3_sol_classic) = 10" by eval
lemma a3_flowsens_equations: "card (fst a3_sol_flowsens) = 10" by eval
lemma a3_selective_equations: "card (fst placement_dg_td_sol) = 10" by eval

text \<open>Selective placement matches all-flow-sensitive precision for
  \<open>answer\<close> (both \<open>[3, 3]\<close>, both exact) while classic does not (\<open>[0, +inf)\<close>):
  \<open>balance\<close>'s selective placement (kept local) is doing the precision work,
  independently of \<open>request_count\<close>'s selective placement (published) -- the
  two globals' placements do not interfere. Equation-system size (the number
  of stabilized unknowns) is identical across all three: for this program's
  shape, placement changes precision, not the size of the equation system.\<close>

end
