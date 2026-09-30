theory Example_Interval_DG_Seed_Join_Recursion
  imports
    "Voblint_Routing.Compiled_Routed_Equations"
    "Voblint_Framework.DG_Reader_Transport"
    "Voblint_Exec.Ownership_Split_Exec"
    "Voblint_Analysis_Interval.Interval_Exec"
    "Voblint_Solver.Globals_Rule"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation" "Voblint_Compile.Compile_Wellformed"
begin

unbundle resolved_st_syntax

section \<open>How a recursive callee is activated over and over\<close>

text \<open>
  A context-insensitive recursion activates one callee unknown from many call
  sites --- here from \<open>main\<close> once and from the callee's own body five times ---
  and every one of those activations has to reach it. It reaches it through a
  single \<^emph>\<open>activation seed\<close>: a framework-owned global key holding the join
  of every entered state published at it, which the callee's entry equation
  reads back. So the seed climbs while the recursion is being discovered, and
  the entry unknown climbs with it.

  This theory runs that climb to its fixpoint and pins where it stops. Under
  the joining global rule \<^const>\<open>Globals_Join\<close> the seed is joined and never
  widened. What the assertions below fix is the route: the value at the
  callee's entry unknown is the value at its seed, and both are the exact join
  of the six entered states rather than anything the iteration invented on the
  way up.
\<close>

subsection \<open>A recursion whose entered state ascends\<close>

text \<open>Each activation enters with one more than the last, from \<open>0\<close> up to the
  guard. The seed therefore sees six distinct entered states, and no single
  publication to it is the answer.\<close>

definition sj_program :: imp_prog where
  "sj_program = program {
     fun up(n) {
       if (n < 5) {
         r = up(n + 1);
         return 0;
       } else {
         return 0;
       }
     }
     fun main() { z = up(0); }
   }"

abbreviation sj_gs :: "vname \<Rightarrow> bool" where "sj_gs \<equiv> declared_global sj_program"

definition sj_cfg :: cfg where
  "sj_cfg = compile_prog (prog_table sj_program) (prog_procs sj_program)"

abbreviation sj_lookup :: "ivl exec_dg_st \<Rightarrow> vname \<Rightarrow> ivl" where
  "sj_lookup s x \<equiv> s\<langle>location_of sj_gs x\<rangle>"

abbreviation sj_seed :: "(pp \<times> unit) set \<times>
    (pp \<times> unit + (unit, unit) global_unknown \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)
  \<Rightarrow> vname \<Rightarrow> ivl" where
  "sj_seed sol x \<equiv>
     sj_lookup (dg_local (snd sol (Inr (Activation_Seed (FunctionEntry (STR ''up'')) ())))) x"

abbreviation sj_at :: "(pp \<times> unit) set \<times>
    (pp \<times> unit + (unit, unit) global_unknown \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)
  \<Rightarrow> pp \<Rightarrow> vname \<Rightarrow> ivl" where
  "sj_at sol u x \<equiv> sj_lookup (dg_local (snd sol (Inl (u, ())))) x"

definition sj_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) global_unknown, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree"
where
  "sj_eqs = compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed route_unit
     (ownership_split_dg_spec_st_for sj_gs (ivl_tf_st_for sj_gs) (ivl_enter_st_for sj_gs))
     sj_cfg cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

definition sj_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) global_unknown \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)"
    where
  "sj_sol = TD_side_rule_Interp_solve Globals_Join sj_eqs (cfg_exit sj_cfg, ())"

lemma sj_terminates:
  "TD_side_rule_Interp_solve_c Globals_Join sj_eqs (cfg_exit sj_cfg, ()) \<noteq> None"
  by eval

subsection \<open>Where the climb stops\<close>

text \<open>The seed holds the join of the six entered states, \<open>[0,0] \<squnion> \<dots> \<squnion> [5,5]\<close>,
  and nothing wider: an activation seed is joined, so no iteration step may
  extrapolate past the states its callers actually published.\<close>

lemma sj_seed_is_the_join:
  "sj_seed sj_sol (STR ''n'') = Ivl (Fin 0) (Fin 5)"
  by eval

text \<open>The callee's entry unknown is exactly what its seed carries. This is the
  whole activation route in one equation: nothing else publishes to that key,
  and the entry equation reads no other.\<close>

lemma sj_entry_is_its_seed:
  "sj_at sj_sol (FunctionEntry (STR ''up'')) (STR ''n'') = sj_seed sj_sol (STR ''n'')"
  by eval

lemma sj_result_keeps_the_join:
  "sj_at sj_sol (FunctionResult (STR ''up'')) (STR ''n'') = Ivl (Fin 0) (Fin 5)"
  by eval

text \<open>The caller is unaffected by the recursion's own ascent: every activation
  returns \<open>0\<close>, so \<open>main\<close>'s \<open>z\<close> is exact.\<close>

lemma sj_caller_result_exact:
  "sj_at sj_sol (cfg_exit sj_cfg) (STR ''z'') = Ivl (Fin 0) (Fin 0)"
  by eval

subsection \<open>What the join policy is not\<close>

text \<open>
  Running the same equations under \<^const>\<open>Globals_Warrow\<close>, which warrows every
  global and so the seed, answers the same thing. Warrowing widens on an increase
  and narrows on a decrease, and here the guard \<open>n < 5\<close> bounds the recursion in
  the interval domain itself, so the narrowing phase recovers \<open>[0,5]\<close> from
  whatever the widening phase overshot to.
\<close>

lemma sj_warrowed_seed_agrees:
  "sj_lookup (dg_local (snd (TD_side_rule_Interp_solve Globals_Warrow sj_eqs
       (cfg_exit sj_cfg, ())) (Inr (Activation_Seed (FunctionEntry (STR ''up'')) ()))))
     (STR ''n'') = Ivl (Fin 0) (Fin 5)"
  by eval

unbundle no resolved_st_syntax

end
