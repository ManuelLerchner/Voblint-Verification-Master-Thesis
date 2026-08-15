theory Exec_Int_DG_Run
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Int_Exec"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Formalization.Run_Analysis_Sound"
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

abbreviation int_ex_lookup :: "('a::bot) exec_dg_st => vname => 'a" where
  "int_ex_lookup s x == lookup_resolved_st_q s (location_of int_ex_gs x)"

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
\<close>

definition dgExI_never_eqs ::
    "pp * unit => (pp * unit, unit, (int_dom resolved_st_q, int_dom resolved_st_q) dg_state) strategy_tree"
where
  "dgExI_never_eqs = dg_gen_of
     (unit_dg_spec_st_for int_ex_gs (int_tf_st_never_for int_ex_gs) (int_dom_enter_never_st_for int_ex_gs))
     gExI bot cinit_int_dom_st cinit_int_dom_st"

definition dgExI_never_sol ::
    "(pp * unit) set * (pp * unit + unit => (int_dom resolved_st_q, int_dom resolved_st_q) dg_state)"
where
  "dgExI_never_sol = TD_side_always_join_Interp_solve dgExI_never_eqs (cfg_exit gExI, ())"

lemma dgExI_never_terminates_c:
  "TD_side_always_join_Interp_solve_c dgExI_never_eqs (cfg_exit gExI, ()) ~= None"
  by eval

lemma dgExI_never_inspect_y_at_Statement_1:
  "int_ex_lookup (locals (snd dgExI_never_sol (Inl (Statement 1, ())))) (STR ''y'') =
   int_dom_sipc STop top PTop (congruence_of_int 2)"
  by eval

definition dgExI_once_eqs ::
    "pp * unit => (pp * unit, unit, (int_dom resolved_st_q, int_dom resolved_st_q) dg_state) strategy_tree"
where
  "dgExI_once_eqs = dg_gen_of
     (unit_dg_spec_st_for int_ex_gs (int_tf_st_once_for int_ex_gs) (int_dom_enter_once_st_for int_ex_gs))
     gExI bot cinit_int_dom_st cinit_int_dom_st"

definition dgExI_once_sol ::
    "(pp * unit) set * (pp * unit + unit => (int_dom resolved_st_q, int_dom resolved_st_q) dg_state)"
where
  "dgExI_once_sol = TD_side_always_join_Interp_solve dgExI_once_eqs (cfg_exit gExI, ())"

lemma dgExI_once_terminates_c:
  "TD_side_always_join_Interp_solve_c dgExI_once_eqs (cfg_exit gExI, ()) ~= None"
  by eval

lemma dgExI_once_inspect_y_at_Statement_1:
  "int_ex_lookup (locals (snd dgExI_once_sol (Inl (Statement 1, ())))) (STR ''y'') =
   int_dom_sipc SPos (Ivl (Fin 2) (Fin 2)) PEven (congruence_of_int 2)"
  by eval

definition dgExI_fixpoint_eqs ::
    "pp * unit => (pp * unit, unit, (int_dom resolved_st_q, int_dom resolved_st_q) dg_state) strategy_tree"
where
  "dgExI_fixpoint_eqs = dg_gen_of
     (unit_dg_spec_st_for int_ex_gs (int_tf_st_fixpoint_for int_ex_gs) (int_dom_enter_fixpoint_st_for int_ex_gs))
     gExI bot cinit_int_dom_st cinit_int_dom_st"

definition dgExI_fixpoint_sol ::
    "(pp * unit) set * (pp * unit + unit => (int_dom resolved_st_q, int_dom resolved_st_q) dg_state)"
where
  "dgExI_fixpoint_sol = TD_side_always_join_Interp_solve dgExI_fixpoint_eqs (cfg_exit gExI, ())"

lemma dgExI_fixpoint_terminates_c:
  "TD_side_always_join_Interp_solve_c dgExI_fixpoint_eqs (cfg_exit gExI, ()) ~= None"
  by eval

lemma dgExI_fixpoint_inspect_y_at_Statement_1:
  "int_ex_lookup (locals (snd dgExI_fixpoint_sol (Inl (Statement 1, ())))) (STR ''y'') =
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
  "int_ex_lookup (locals (snd dgExI_never_sol (Inl (Statement 1, ())))) (STR ''y'') ~=
   int_ex_lookup (locals (snd dgExI_once_sol (Inl (Statement 1, ())))) (STR ''y'')"
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
  "int_ex_lookup (locals (snd dgExI_once_sol (Inl (Statement 1, ())))) (STR ''y'') =
   int_ex_lookup (locals (snd dgExI_fixpoint_sol (Inl (Statement 1, ())))) (STR ''y'')"
  unfolding dgExI_once_inspect_y_at_Statement_1 dgExI_fixpoint_inspect_y_at_Statement_1
  by eval

end
