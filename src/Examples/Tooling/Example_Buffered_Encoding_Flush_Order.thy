theory Example_Buffered_Encoding_Flush_Order
  imports
    "Voblint_Exec.Exec_DG_Generator"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation" "Voblint_Compile.Compile_Wellformed"
begin

section \<open>Whether the two encodings solve alike\<close>

text \<open>
  A recursive callee that also writes a declared global. Each activation
  publishes twice from one evaluation: to \<^const>\<open>Analysis_Global\<close>, because
  \<open>g\<close> is owned by the global channel, and to the callee's
  \<^const>\<open>Activation_Seed\<close>, because the call activates \<open>up\<close> again. The two
  keys therefore compete for first-occurrence position in the flush, which is
  the only thing the two encodings order differently.

  \<open>g := n\<close>, not \<open>g := g + n\<close>: the global must stay bounded by the guard, or
  the analysis global ascends without a bound the interval domain can narrow
  back and the fixpoint does not converge under warrowing at all.
\<close>

definition fo_program :: imp_prog where
  "fo_program = program {
     global g;
     void up(n) { g := n; return 0 }
     void main() { g := 0; a := up(1); b := up(2) }
   }"

abbreviation fo_gs :: "vname \<Rightarrow> bool" where "fo_gs \<equiv> declared_global fo_program"

definition fo_cfg :: cfg where
  "fo_cfg = compile_prog (prog_table fo_program) (prog_procs fo_program)"

definition fo_spec ::
  "(pp \<times> unit, (unit, unit) routed_gk, unit, ivl exec_dg_st, ivl exec_dg_st) dg_spec" where
  "fo_spec = ownership_split_dg_spec_st_for fo_gs (ivl_tf_st_for fo_gs) (ivl_enter_st_for fo_gs)"

definition fo_direct ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree" where
  "fo_direct = unit_routed_eqs fo_spec fo_cfg bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

definition fo_buffered ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree" where
  "fo_buffered = unit_routed_eqs_buffered fo_spec fo_cfg bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

abbreviation fo_sol where
  "fo_sol E \<equiv> snd (TD_side_seed_join_warrowing_Interp_solve is_activation_seed E (cfg_exit fo_cfg, ()))"

abbreviation fo_look where
  "fo_look s x \<equiv> lookup_resolved_st_q s (location_of fo_gs x)"

subsection \<open>Interval, seed-join warrowing\<close>

lemma fo_ivl_terminates:
  "TD_side_seed_join_warrowing_Interp_solve_c is_activation_seed fo_direct (cfg_exit fo_cfg, ()) \<noteq> None"
  "TD_side_seed_join_warrowing_Interp_solve_c is_activation_seed fo_buffered (cfg_exit fo_cfg, ()) \<noteq> None"
  by eval+

text \<open>The analysis global is the observation a different flush order would
  move: both encodings publish to it and to the callee's seed from one
  evaluation, so which key the flush reaches first is exactly what differs.\<close>

lemma fo_ivl_global_agrees:
  "fo_look (globs (fo_sol fo_direct (Inr (Analysis_Global ())))) (STR ''g'')
     = fo_look (globs (fo_sol fo_buffered (Inr (Analysis_Global ())))) (STR ''g'')"
  by eval

lemma fo_ivl_global_value:
  "fo_look (globs (fo_sol fo_direct (Inr (Analysis_Global ())))) (STR ''g'') = Ivl (Fin 0) PlusInf"
  by eval

lemma fo_ivl_seed_agrees:
  "fo_look (locals (fo_sol fo_direct (Inr (Activation_Seed (FunctionEntry (STR ''up'')) ())))) (STR ''n'')
     = fo_look (locals (fo_sol fo_buffered (Inr (Activation_Seed (FunctionEntry (STR ''up'')) ())))) (STR ''n'')"
  by eval

lemma fo_ivl_entry_agrees:
  "fo_look (locals (fo_sol fo_direct (Inl (FunctionEntry (STR ''up''), ())))) (STR ''n'')
     = fo_look (locals (fo_sol fo_buffered (Inl (FunctionEntry (STR ''up''), ())))) (STR ''n'')"
  by eval

lemma fo_ivl_exit_agrees:
  "fo_look (locals (fo_sol fo_direct (Inl (cfg_exit fo_cfg, ())))) (STR ''z'')
     = fo_look (locals (fo_sol fo_buffered (Inl (cfg_exit fo_cfg, ())))) (STR ''z'')"
  by eval

subsection \<open>The same comparison under the per-origin update rule\<close>

abbreviation fo_sol_po where
  "fo_sol_po E \<equiv> snd (TD_side_per_origin_Interp_solve E (cfg_exit fo_cfg, ()))"

text \<open>The per-origin rule is the one buffering exists to protect, and it is
  strictly more precise here than warrowing --- \<open>[0,2]\<close> rather than
  \<open>[0,\<infinity>]\<close> --- so it does observe how contributions land. It still
  cannot tell the two encodings apart.\<close>

lemma fo_per_origin_terminates:
  "TD_side_per_origin_Interp_solve_c fo_direct (cfg_exit fo_cfg, ()) \<noteq> None"
  "TD_side_per_origin_Interp_solve_c fo_buffered (cfg_exit fo_cfg, ()) \<noteq> None"
  by eval+

lemma fo_per_origin_global_agrees:
  "fo_look (globs (fo_sol_po fo_direct (Inr (Analysis_Global ())))) (STR ''g'')
     = fo_look (globs (fo_sol_po fo_buffered (Inr (Analysis_Global ())))) (STR ''g'')"
  by eval

lemma fo_per_origin_global_value:
  "fo_look (globs (fo_sol_po fo_direct (Inr (Analysis_Global ())))) (STR ''g'') = Ivl (Fin 0) (Fin 2)"
  by eval

lemma fo_per_origin_seed_agrees:
  "fo_look (locals (fo_sol_po fo_direct (Inr (Activation_Seed (FunctionEntry (STR ''up'')) ())))) (STR ''n'')
     = fo_look (locals (fo_sol_po fo_buffered (Inr (Activation_Seed (FunctionEntry (STR ''up'')) ())))) (STR ''n'')"
  by eval

subsection \<open>The same comparison at Sign, join-only\<close>

definition fo_sign_spec ::
  "(pp \<times> unit, (unit, unit) routed_gk, unit, sign exec_dg_st, sign exec_dg_st) dg_spec" where
  "fo_sign_spec = ownership_split_dg_spec_st_for fo_gs (sign_tf_st_for fo_gs) (sign_enter_st_for fo_gs)"

definition fo_sign_direct ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "fo_sign_direct = unit_routed_eqs fo_sign_spec fo_cfg bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

definition fo_sign_buffered ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "fo_sign_buffered = unit_routed_eqs_buffered fo_sign_spec fo_cfg bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

abbreviation fo_sign_sol where
  "fo_sign_sol E \<equiv> snd (TD_side_always_join_Interp_solve E (cfg_exit fo_cfg, ()))"

lemma fo_sign_terminates:
  "TD_side_always_join_Interp_solve_c fo_sign_direct (cfg_exit fo_cfg, ()) \<noteq> None"
  "TD_side_always_join_Interp_solve_c fo_sign_buffered (cfg_exit fo_cfg, ()) \<noteq> None"
  by eval+

lemma fo_sign_global_agrees:
  "fo_look (globs (fo_sign_sol fo_sign_direct (Inr (Analysis_Global ())))) (STR ''g'')
     = fo_look (globs (fo_sign_sol fo_sign_buffered (Inr (Analysis_Global ())))) (STR ''g'')"
  by eval

lemma fo_sign_global_value:
  "fo_look (globs (fo_sign_sol fo_sign_direct (Inr (Analysis_Global ())))) (STR ''g'') = SNonNeg"
  by eval

lemma fo_sign_seed_agrees:
  "fo_look (locals (fo_sign_sol fo_sign_direct (Inr (Activation_Seed (FunctionEntry (STR ''up'')) ())))) (STR ''n'')
     = fo_look (locals (fo_sign_sol fo_sign_buffered (Inr (Activation_Seed (FunctionEntry (STR ''up'')) ())))) (STR ''n'')"
  by eval

text \<open>
  Three update rules --- warrowing with joined seeds, per-origin, and plain
  join at a finite domain --- and the two encodings answer alike at every
  observation, including the analysis global that a reordered flush would be
  the one to move.

  That is evidence, not a theorem. The declarative correspondence already says
  the two agree at a fixed valuation; what these runs add is that the solver's
  own iteration does not separate them here either. The gap that remains is a
  recursive procedure that writes a declared global: no encoding solves that
  under warrowing --- the analysis global ascends past what the interval domain
  narrows back --- so the most scheduling-sensitive shape cannot be compared at
  all, by either generator.
\<close>

end
