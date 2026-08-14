theory Example_Interval_DG_EntryState_Ctx
  imports
    Example_Interval_DG_EntryState_Base
    "Voblint_Core.Routed_Context"
begin

section \<open>Context-sensitive interval analysis of \<open>rc_program\<close> (executable)\<close>

text \<open>
  The generalized D/G generator is instantiated with routed context hooks.  The one
  call to \<open>p\<close> receives the abstract entry value of formal \<open>a\<close> as its context: since
  \<open>x\<close> was just assigned from \<open>__voblint_nondet_int()\<close>, its interval at the call site is \<open>Top\<close>, so
  the routed context is \<open>Top\<close> itself --- one context, not a family of contexts
  covering the infinitely many concrete arguments \<open>__voblint_nondet_int()\<close> can produce.
\<close>

subsection \<open>Global key: real globals vs callee-entry seed slots\<close>

datatype gk = Global | Seed (seed_pp: pp) (seed_ivl: "ivl list")

subsection \<open>The routed context hooks\<close>

definition Spoly :: "(ivl exec_dg_st, ivl exec_dg_st) dg_spec" where
  "Spoly = unit_dg_spec_st_for rc_gs (ivl_tf_st_for rc_gs) (ivl_enter_st_for rc_gs)"

text \<open>The callee-entry local store produced by a \<^const>\<open>CallEdge\<close> from a caller-local
  state (globals defaulted to \<open>bot\<close>: \<open>rc_program\<close> has none).\<close>
definition entered_ivl :: "ivl exec_dg_st \<Rightarrow> call_action \<Rightarrow> ivl exec_dg_st" where
  "entered_ivl d ca =
     (case ca of CallEdge dst fs as \<Rightarrow> snd (dgs_enter Spoly fs as d bot))"

text \<open>The routing function: the context a call selects is the entered value of the
  callee's declared formals, in the order the matched \<^const>\<open>CallEdge\<close> already
  carries them.\<close>
definition route_ivl :: "ivl exec_dg_st \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "route_ivl d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (rc_lookup (entered_ivl d ca)))"

text \<open>The generator's routing hook is generic over call site and caller context; this
  instance needs neither, using only the entered store.\<close>
definition route_ivl_gen :: "pp \<Rightarrow> ivl list \<Rightarrow> ivl exec_dg_st \<Rightarrow> call_action \<Rightarrow> ivl list" where
  "route_ivl_gen u ctx d ca = route_ivl d ca"

subsection \<open>The routed equation system and its solution\<close>

definition rc_ctx_eqs ::
  "(pp \<times> ivl list, gk, (ivl exec_dg_st, ivl exec_dg_st) dg_state) eqsT" where
  "rc_ctx_eqs =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. Global) route_ivl_gen
       (routed_cmb Spoly Global Seed) (routed_extra Seed Global)
       rc_cfg Spoly bot cinit_ivl_st (restrict_global_resolved_q cinit_ivl_st)"

text \<open>The main context is \<open>[]\<close> (\<open>main\<close> is the root activation, no formal binds it).\<close>
definition rc_ctx_sol ::
  "(pp \<times> ivl list) set \<times> (pp \<times> ivl list + gk \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)" where
  "rc_ctx_sol = TD_side_warrowing_apinis_Interp_solve rc_ctx_eqs (cfg_exit rc_cfg, [])"

lemma rc_ctx_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c rc_ctx_eqs (cfg_exit rc_cfg, []) \<noteq> None"
  by eval

subsection \<open>The routed context is exactly \<open>Top\<close>\<close>

definition ctx_call :: "ivl list" where
  "ctx_call = route_ivl (locals (snd rc_ctx_sol (Inl (Statement 3, []))))
                 (CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')])"

lemma ctx_call_val: "ctx_call = [ivl_top]" by eval

text \<open>The callee entry is materialized once, under the wide context, and never under
  the root context.\<close>
lemma callee_covered_call: "(FunctionEntry (STR ''p''), ctx_call) \<in> fst rc_ctx_sol" by eval
lemma callee_not_under_main: "(FunctionEntry (STR ''p''), []) \<notin> fst rc_ctx_sol" by eval

end
