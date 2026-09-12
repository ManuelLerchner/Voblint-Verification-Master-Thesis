theory Exec_Int_DG_Run
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    "Voblint_Analysis_Int.Int_Exec"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Routing.Compiled_Routed_Equations"
begin

section \<open>The composite domain carried through a real solver run\<close>

text \<open>
  Everything else in this folder calls a composite operation directly. Here the
  guard \<open>y + 1 = 3\<close> arrives the way it does in production: compiled from VIMP
  source into a CFG, turned into a D/G equation system, and handed to the
  vendored TD solver. The two runs cover the modes the CLI cannot select:
  \<open>Refine_Never\<close> and \<open>Refine_Once\<close>. The production CLI fixes
  \<open>Refine_Fixpoint\<close>, whose result is covered by its CLI regression.
  Each lemma below projects its node result directly from \<open>solve_c\<close>, so
  termination and the observed value require one solver evaluation together.
  Vocabulary: an \<open>eqs\<close> constant is the equation system one mode generates,
  \<open>int_ex_read\<close> projects one variable's abstract value out of a node's local
  unknown, and \<open>Statement 1\<close> names the point after the true-branch guard.
\<close>

text \<open>
  Disambiguate VIMP's numeral constructor \<open>N\<close> from the \<open>phase\<close> datatype's
  constructor of the same name.
\<close>

hide_const phase.N

definition int_ex_prog :: imp_prog where
  "int_ex_prog = program { fun main() { if (y + 1 == 3) { x = 1; } else { x = 0; } } }"

abbreviation int_ex_gs :: "vname => bool" where
  "int_ex_gs == declared_global int_ex_prog"

definition int_ex_pi :: proc_table where
  "int_ex_pi = prog_table int_ex_prog"

definition gExI :: cfg where
  "gExI = compile_prog int_ex_pi (prog_procs int_ex_prog)"

text \<open>
  The Base construction routes the whole abstract state through the local
  unknown, reachability-lifted: \<open>int_ex_read\<close> reads a computed \<open>exec_dg_st
  lifted\<close> value back through \<^const>\<open>fun_of_exec_dg_st_for\<close>, matching
  \<open>parity_lookup\<close>'s role in Parity's own DG flagship -- a genuinely
  unreachable local unknown (\<open>Bot\<close>) reads back as \<open>top\<close>, never spuriously
  observed here since every inspected node below is reachable.
\<close>

abbreviation int_ex_read :: "int_dom exec_dg_st lifted => vname => int_dom" where
  "int_ex_read d x ==
     (case map_lift (fun_of_exec_dg_st_for int_ex_gs) d of
        Lifted f => f x | Bot => top)"

abbreviation int_ex_result where
  "int_ex_result eqs ==
     map_option
       (\<lambda>(_, sol). int_ex_read (locals (sol (Inl (Statement 1, ())))) (STR ''y''))
       (TD_side_always_join_Interp_solve_c eqs (cfg_exit gExI, ()))"

subsection \<open>Computed post-solutions for the non-CLI modes\<close>

text \<open>
  \<open>y + 1 = 3\<close> is the same composite guard as
  \<open>Example_Int_Backward.bfilter_int_dom_once_plus_eq_exact\<close>, now reached
  through a real compiled \<open>if\<close> and the vendored solver instead of a direct
  \<open>bfilter\<close> call. \<open>Statement 1\<close> is the interior node right after
  the true branch's guard and before the branches rejoin at \<open>Statement 3\<close>
  (a join would erase the refinement, since the false branch never
  constrains \<open>y\<close>), so that is where \<open>y\<close>'s mode-dependent precision is
  observable in the solver's own computed result.

  Each mode is registered on the generic Base construction
  \<^const>\<open>local_state_dg_spec_st_for_lifted\<close> (\<^theory>\<open>Voblint_Exec.DG_Local_State_Exec\<close>),
  matching Sign's own production route: the local unknown carries the whole
  reachability-lifted \<open>int_dom exec_dg_st\<close>, with no separate local/global
  split for \<open>int_ex_prog\<close>'s (empty) set of declared globals to route through.
\<close>

definition dgExI_never_eqs ::
    "pp * unit => (pp * unit, (unit, unit) routed_gk,
       (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) strategy_tree"
where
  "dgExI_never_eqs = compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed route_unit
     (local_state_dg_spec_st_for_lifted int_ex_gs
       (resolved_st_q_is_bot_for (declared_global_vars int_ex_prog))
       (int_tf_st_never_for int_ex_gs) (int_dom_enter_never_st_for int_ex_gs))
     gExI (Lifted cinit_int_dom_st) (Lifted cinit_int_dom_st)"

lemma dgExI_never_result:
  "int_ex_result dgExI_never_eqs =
   Some (int_dom_sipc STop top PTop (congruence_of_int 2))"
  by eval

definition dgExI_once_eqs ::
    "pp * unit => (pp * unit, (unit, unit) routed_gk,
       (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) strategy_tree"
where
  "dgExI_once_eqs = compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed route_unit
     (local_state_dg_spec_st_for_lifted int_ex_gs
       (resolved_st_q_is_bot_for (declared_global_vars int_ex_prog))
       (int_tf_st_once_for int_ex_gs) (int_dom_enter_once_st_for int_ex_gs))
     gExI (Lifted cinit_int_dom_st) (Lifted cinit_int_dom_st)"

lemma dgExI_once_result:
  "int_ex_result dgExI_once_eqs =
   Some (int_dom_sipc SPos (Ivl (Fin 2) (Fin 2)) PEven (congruence_of_int 2))"
  by eval

text \<open>
  The retained mode contrast comes from two real solver runs on the same
  compiled program. \<open>Refine_Never\<close> narrows only the Congruence component
  through its own inverse. \<open>Refine_Once\<close> propagates that information to
  Sign, Interval, and Parity and reaches the exact singleton.
\<close>

corollary dgExI_never_ne_once:
  "int_ex_result dgExI_never_eqs \<noteq> int_ex_result dgExI_once_eqs"
  apply (simp only: dgExI_never_result dgExI_once_result option.inject)
  apply (rule notI)
  apply (drule arg_cong[where f = int_sign])
  by (simp add: int_dom_sipc_def)


end

