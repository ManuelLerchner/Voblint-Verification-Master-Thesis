theory Exec_Int_DG_Run
  imports
    "Voblint_Core.Exec_DG_Bridge"
    "Voblint_Core.DG_Base_Exec"
    "Voblint_Analysis.Int_Exec"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Soundness.Run_Analysis_Sound"
begin

hide_const phase.N

definition int_ex_prog :: imp_prog where
  "int_ex_prog = program { void main() { if (y + 1 == 3) { x := 1 } else { x := 0 } } }"

abbreviation int_ex_gs :: "vname => bool" where
  "int_ex_gs == declared_global int_ex_prog"

definition int_ex_pi :: proc_table where
  "int_ex_pi = prog_table int_ex_prog"

definition gExI :: cfg where
  "gExI = compile_prog int_ex_pi (prog_procs int_ex_prog) prog_main_name (prog_main int_ex_prog)"

text \<open>
  The Base construction routes the whole abstract state through the local
  unknown, reachability-lifted: \<open>int_ex_read\<close> reads a computed \<open>exec_dg_st
  lifted\<close> value back through \<^const>\<open>fun_of_exec_dg_st_for\<close>, matching
  \<open>sign_ex_lookup\<close>'s role in Sign's own DG flagship -- a genuinely
  unreachable local unknown (\<open>Bot\<close>) reads back as \<open>top\<close>, never spuriously
  observed here since every inspected node below is reachable.
\<close>
abbreviation int_ex_read :: "int_dom exec_dg_st lifted => vname => int_dom" where
  "int_ex_read d x == (case map_lift (fun_of_exec_dg_st_for int_ex_gs) d of Lifted f => f x | Bot => top)"

lemma gExI_calls: "calls gExI = {}" by eval
lemma gExI_entry: "cfg_entry gExI = FunctionEntry (STR ''main'')" by eval
lemma gExI_finE: "finite (intra gExI)" unfolding gExI_def using compile_prog_finite by simp
lemma gExI_finC: "finite (calls gExI)" unfolding gExI_def using compile_prog_finite by simp

subsection \<open>Computed post-solution, one per refinement mode\<close>

text \<open>
  \<open>y + 1 = 3\<close> is the same composite guard as
  \<open>Example_Int_Backward.bfilter_int_dom_once_plus_eq_exact\<close> and
  \<open>Example_Int_Transfer.apply_tf_once_assume_exact\<close>, now reached through a
  real compiled \<open>if\<close> and the vendored solver instead of a direct
  \<open>bfilter\<close>/\<open>apply_tf\<close> call. \<open>Statement 1\<close> is the interior node right after
  the true branch's guard and before the branches rejoin at \<open>Statement 3\<close>
  (a join would erase the refinement, since the false branch never
  constrains \<open>y\<close>), so that is where \<open>y\<close>'s mode-dependent precision is
  observable in the solver's own computed result.

  Each mode is registered on the generic Base construction
  \<^const>\<open>base_dg_spec_st_for_lifted\<close> (\<^theory>\<open>Voblint_Core.DG_Base_Exec\<close>),
  matching Sign's own production route: the local unknown carries the whole
  reachability-lifted \<open>int_dom exec_dg_st\<close>, with no separate local/global
  split for \<open>int_ex_prog\<close>'s (empty) set of declared globals to route through.
\<close>

definition dgExI_never_eqs ::
    "pp * unit => (pp * unit, unit, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) strategy_tree"
where
  "dgExI_never_eqs = dg_gen_of
     (base_dg_spec_st_for_lifted int_ex_gs (resolved_st_q_is_bot_for (declared_global_vars int_ex_prog))
       (int_tf_st_never_for int_ex_gs) (int_dom_enter_never_st_for int_ex_gs))
     gExI bot (Lifted cinit_int_dom_st) (Lifted cinit_int_dom_st)"

definition dgExI_never_sol ::
    "(pp * unit) set * (pp * unit + unit => (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
where
  "dgExI_never_sol = TD_side_always_join_Interp_solve dgExI_never_eqs (cfg_exit gExI, ())"

lemma dgExI_never_terminates_c:
  "TD_side_always_join_Interp_solve_c dgExI_never_eqs (cfg_exit gExI, ()) ~= None"
  by eval

lemma dgExI_never_inspect_y_at_Statement_1:
  "int_ex_read (locals (snd dgExI_never_sol (Inl (Statement 1, ())))) (STR ''y'') =
   int_dom_sipc STop top PTop (congruence_of_int 2)"
  by eval

definition dgExI_once_eqs ::
    "pp * unit => (pp * unit, unit, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) strategy_tree"
where
  "dgExI_once_eqs = dg_gen_of
     (base_dg_spec_st_for_lifted int_ex_gs (resolved_st_q_is_bot_for (declared_global_vars int_ex_prog))
       (int_tf_st_once_for int_ex_gs) (int_dom_enter_once_st_for int_ex_gs))
     gExI bot (Lifted cinit_int_dom_st) (Lifted cinit_int_dom_st)"

definition dgExI_once_sol ::
    "(pp * unit) set * (pp * unit + unit => (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
where
  "dgExI_once_sol = TD_side_always_join_Interp_solve dgExI_once_eqs (cfg_exit gExI, ())"

lemma dgExI_once_terminates_c:
  "TD_side_always_join_Interp_solve_c dgExI_once_eqs (cfg_exit gExI, ()) ~= None"
  by eval

lemma dgExI_once_inspect_y_at_Statement_1:
  "int_ex_read (locals (snd dgExI_once_sol (Inl (Statement 1, ())))) (STR ''y'') =
   int_dom_sipc SPos (Ivl (Fin 2) (Fin 2)) PEven (congruence_of_int 2)"
  by eval

definition dgExI_fixpoint_eqs ::
    "pp * unit => (pp * unit, unit, (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state) strategy_tree"
where
  "dgExI_fixpoint_eqs = dg_gen_of
     (base_dg_spec_st_for_lifted int_ex_gs (resolved_st_q_is_bot_for (declared_global_vars int_ex_prog))
       (int_tf_st_fixpoint_for int_ex_gs) (int_dom_enter_fixpoint_st_for int_ex_gs))
     gExI bot (Lifted cinit_int_dom_st) (Lifted cinit_int_dom_st)"

definition dgExI_fixpoint_sol ::
    "(pp * unit) set * (pp * unit + unit => (int_dom exec_dg_st lifted, int_dom exec_dg_st lifted) dg_state)"
where
  "dgExI_fixpoint_sol = TD_side_always_join_Interp_solve dgExI_fixpoint_eqs (cfg_exit gExI, ())"

lemma dgExI_fixpoint_terminates_c:
  "TD_side_always_join_Interp_solve_c dgExI_fixpoint_eqs (cfg_exit gExI, ()) ~= None"
  by eval

lemma dgExI_fixpoint_inspect_y_at_Statement_1:
  "int_ex_read (locals (snd dgExI_fixpoint_sol (Inl (Statement 1, ())))) (STR ''y'') =
   int_dom_sipc SPos (Ivl (Fin 2) (Fin 2)) PEven (congruence_of_int 2)"
  by eval

text \<open>
  The mode contrast, established through three real solver runs on the same
  compiled program rather than three direct \<open>apply_tf\<close> calls:
  \<open>Refine_Never\<close> only narrows the congruence component (Congruence's own
  real inverse, not cross-component refinement), while \<open>Refine_Once\<close> and
  \<open>Refine_Fixpoint\<close> both reach the exact singleton -- the sequence of
  one-round refinements performed during this backward traversal already
  suffices here, so \<open>Fixpoint\<close> finds nothing further beyond what \<open>Once\<close>
  already computed.
\<close>

corollary dgExI_never_ne_once:
  "int_ex_read (locals (snd dgExI_never_sol (Inl (Statement 1, ())))) (STR ''y'') ~=
   int_ex_read (locals (snd dgExI_once_sol (Inl (Statement 1, ())))) (STR ''y'')"
  unfolding dgExI_never_inspect_y_at_Statement_1 dgExI_once_inspect_y_at_Statement_1
  by eval

text \<open>
  \<open>Once\<close> and \<open>Fixpoint\<close> compute the same result at this program point.
  This does not mean that one standalone reduction round is generally
  enough -- \<open>refinement_round_is_progressive\<close> (\<open>Example_Int_Domain.thy\<close>)
  is itself a witness where a single round is not exact and a further round
  still makes progress. \<open>Refine_Once\<close> performs one round per invocation of
  the composite operation, and recursive backward filtering invokes
  refinement at multiple points: once while propagating the arithmetic
  inverse through \<open>+\<close>, and again when the resulting candidate is
  intersected into the \<open>y\<close> leaf. For this guard those successive one-round
  reductions already expose the exact singleton, so \<open>Fixpoint\<close> has no
  further precision to add here.
\<close>

corollary dgExI_once_eq_fixpoint:
  "int_ex_read (locals (snd dgExI_once_sol (Inl (Statement 1, ())))) (STR ''y'') =
   int_ex_read (locals (snd dgExI_fixpoint_sol (Inl (Statement 1, ())))) (STR ''y'')"
  unfolding dgExI_once_inspect_y_at_Statement_1 dgExI_fixpoint_inspect_y_at_Statement_1
  by eval

end

