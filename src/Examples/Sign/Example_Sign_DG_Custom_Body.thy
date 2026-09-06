theory Example_Sign_DG_Custom_Body
  imports
    "Voblint_Exec.Exec_DG_Generator"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Sign_Transfer"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation" "Voblint_Compile.Compile_Wellformed"
begin

section \<open>What a procedure-entry transfer can change\<close>

text \<open>
  A procedure's first transition is a field of \<^typ>\<open>('x, 'k, 'v, 'dl, 'dg) dg_spec\<close>
  like any other: \<^const>\<open>dgs_body\<close> is what runs on the \<^const>\<open>EA_Body\<close> edge
  leaving \<open>FunctionEntry p\<close>, matching Goblint's \<open>body\<close> on its own \<open>Entry\<close> edge.
  Every domain in this development leaves it at the identity, because a VIMP
  procedure declares no locals beyond the formals the call already bound --- so
  nothing else in the tree distinguishes a specification that implements it from
  one that ignores it.

  This theory witnesses that the field is genuinely free and genuinely reached.
  It takes the ordinary executable Sign specification, overrides \<^emph>\<open>only\<close>
  \<^const>\<open>dgs_body\<close>, and runs the result through the same
  \<^const>\<open>unit_routed_eqs\<close> generator and the same vendored solver a production
  analysis uses. The override forgets the callee's formal on entry, which is
  sound --- it only moves the entry state up the lattice --- and observable,
  which is the point: the two solved systems agree everywhere except inside the
  callee.

  It is a regression in the strict sense. Both executable specification builders
  once wired \<^const>\<open>dgs_body\<close> to the \<^emph>\<open>skip\<close> transfer, and no test could
  see it: without an \<^const>\<open>EA_Body\<close> edge there was no transition to dispatch
  on, so a specification's procedure-entry work was discarded silently. The
  disagreement below is exactly what that defect suppressed.
\<close>

subsection \<open>A procedure entry that forgets the formals\<close>

text \<open>
  The stock body transfer is the identity. This one sends the callee's formal to
  \<^const>\<open>STop\<close> as the activation starts, in the same shape a domain with real
  local declarations would use to give them their initial abstract value. Raising
  a variable to \<^const>\<open>STop\<close> can only lose precision, so the result stays sound;
  it is strictly less precise, and it is a different operation.
\<close>

definition sign_body_forget ::
  "(vname \<Rightarrow> bool) \<Rightarrow> vname
   \<Rightarrow> ('x,'k,unit,sign exec_dg_st,sign exec_dg_st) man_transfer"
where
  "sign_body_forget gs x =
     local_transfer (\<lambda>d. update_resolved_st_q d (location_of gs x) STop)"

subsection \<open>The Sign specification that uses it\<close>

definition sign_dg_spec_body_forget ::
  "(vname \<Rightarrow> bool) \<Rightarrow> vname
   \<Rightarrow> (edge_action \<Rightarrow> sign exec_dg_st \<Rightarrow> sign exec_dg_st)
   \<Rightarrow> (call_info \<Rightarrow> sign exec_dg_st \<Rightarrow> sign exec_dg_st)
   \<Rightarrow> ('x, 'k, unit, sign exec_dg_st, sign exec_dg_st) dg_spec" where
  "sign_dg_spec_body_forget gs x tf_st enter_st =
     (ownership_split_dg_spec_st_for gs tf_st enter_st)
       \<lparr> dgs_body := (\<lambda>p. sign_body_forget gs x) \<rparr>"

text \<open>Only the procedure-entry transfer differs; every other field is the stock
  one, so any disagreement below is attributable to it alone.\<close>

lemma dgs_enter_sign_dg_spec_body_forget [simp]:
  "enter\<^sup># (sign_dg_spec_body_forget gs x tf_st enter_st)
     = enter\<^sup># (ownership_split_dg_spec_st_for gs tf_st enter_st)"
  by (simp add: sign_dg_spec_body_forget_def)

lemma dgs_combine_env_sign_dg_spec_body_forget [simp]:
  "combine_env\<^sup># (sign_dg_spec_body_forget gs x tf_st enter_st)
     = combine_env\<^sup># (ownership_split_dg_spec_st_for gs tf_st enter_st)"
  by (simp add: sign_dg_spec_body_forget_def)

lemma dgs_combine_assign_sign_dg_spec_body_forget [simp]:
  "combine_assign\<^sup># (sign_dg_spec_body_forget gs x tf_st enter_st)
     = combine_assign\<^sup># (ownership_split_dg_spec_st_for gs tf_st enter_st)"
  by (simp add: sign_dg_spec_body_forget_def)

text \<open>The edge dispatch differs at exactly one action.\<close>

lemma dg_spec_step_sign_dg_spec_body_forget_body [simp]:
  "dg_spec_step (sign_dg_spec_body_forget gs x tf_st enter_st) (EA_Body p)
     = sign_body_forget gs x"
  by (simp add: sign_dg_spec_body_forget_def)

lemma dgs_body_sign_dg_spec_body_forget [simp]:
  "body\<^sup># (sign_dg_spec_body_forget gs x tf_st enter_st) = (\<lambda>p. sign_body_forget gs x)"
  by (simp add: sign_dg_spec_body_forget_def)

subsection \<open>Both specifications, on one program\<close>

text \<open>
  \<open>bf_program\<close>'s callee takes a positive actual, so its formal is \<^const>\<open>SPos\<close>
  at the procedure entry node under either specification. Both compile the same
  program to the same CFG, generate equations with the same
  \<^const>\<open>unit_routed_eqs\<close>, and are solved by the same vendored solver; only
  \<^const>\<open>dgs_body\<close> differs between them.
\<close>

definition bf_program :: imp_prog where
  "bf_program = program {
     void mark(p) { r := 0 - 1; return p }
     void main() { r := 1; z := mark(7) }
   }"

abbreviation bf_prog_gs :: "vname \<Rightarrow> bool" where
  "bf_prog_gs \<equiv> declared_global bf_program"

definition bf_cfg :: cfg where
  "bf_cfg = compile_prog (prog_table bf_program) (prog_procs bf_program)"

abbreviation bf_lookup :: "sign exec_dg_st \<Rightarrow> vname \<Rightarrow> sign" where
  "bf_lookup s x \<equiv> lookup_resolved_st_q s (location_of bf_prog_gs x)"

definition bf_stock_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "bf_stock_eqs = unit_routed_eqs
     (ownership_split_dg_spec_st_for bf_prog_gs (sign_tf_st_for bf_prog_gs) (sign_enter_st_for bf_prog_gs))
     bf_cfg bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

definition bf_custom_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "bf_custom_eqs = unit_routed_eqs
     (sign_dg_spec_body_forget bf_prog_gs (STR ''p'')
        (sign_tf_st_for bf_prog_gs) (sign_enter_st_for bf_prog_gs))
     bf_cfg bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

lemma bf_stock_terminates:
  "TD_side_seed_join_warrowing_Interp_solve_c is_activation_seed bf_stock_eqs (cfg_exit bf_cfg, ()) \<noteq> None"
  by eval

lemma bf_custom_terminates:
  "TD_side_seed_join_warrowing_Interp_solve_c is_activation_seed bf_custom_eqs (cfg_exit bf_cfg, ()) \<noteq> None"
  by eval

definition bf_stock_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "bf_stock_sol = TD_side_seed_join_warrowing_Interp_solve is_activation_seed bf_stock_eqs (cfg_exit bf_cfg, ())"

definition bf_custom_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "bf_custom_sol = TD_side_seed_join_warrowing_Interp_solve is_activation_seed bf_custom_eqs (cfg_exit bf_cfg, ())"

subsection \<open>The procedure-entry edge, and what runs on it\<close>

text \<open>The compiled callee is bracketed by an \<^const>\<open>EA_Body\<close> edge: this is the
  transition \<^const>\<open>dgs_body\<close> is dispatched at, and the only one whose action
  names the procedure it belongs to.\<close>

lemma bf_body_edge:
  "(FunctionEntry (STR ''mark''), EA_Body (STR ''mark''), Statement 0) \<in> intra bf_cfg"
  by eval

text \<open>
  Where the procedure-entry transfer sits. \<open>FunctionEntry mark\<close> holds the state
  the call activated it with, before any of the callee's own work: the formal is
  still \<^const>\<open>SPos\<close> there under both specifications, because
  \<^const>\<open>dgs_body\<close> has not run yet. That is Goblint's placement --- the entry
  node carries the joined activation and \<open>body\<close> runs on the edge out of it, not
  into it.
\<close>

lemma bf_entry_node_is_pre_body:
  "bf_lookup (locals (snd bf_stock_sol (Inl (FunctionEntry (STR ''mark''), ())))) (STR ''p'') = SPos"
  "bf_lookup (locals (snd bf_custom_sol (Inl (FunctionEntry (STR ''mark''), ())))) (STR ''p'') = SPos"
  by eval+

text \<open>
  Regression witness. One edge later --- across \<^const>\<open>EA_Body\<close> --- the two
  solved systems disagree at the formal: the stock identity keeps
  \<^const>\<open>SPos\<close>, the override publishes \<^const>\<open>STop\<close>. Nothing but
  \<^const>\<open>dgs_body\<close> differs between the two specifications, so this equation is
  the whole observable content of the field.
\<close>

lemma bf_stock_keeps_the_formal:
  "bf_lookup (locals (snd bf_stock_sol (Inl (Statement 0, ())))) (STR ''p'') = SPos"
  by eval

lemma bf_custom_forgets_the_formal:
  "bf_lookup (locals (snd bf_custom_sol (Inl (Statement 0, ())))) (STR ''p'') = STop"
  by eval

text \<open>Outside the callee the two agree: the caller's own locals never meet the
  procedure-entry transfer, so the call site and the resume point are unchanged
  by the override.\<close>

lemma bf_caller_unaffected:
  "bf_lookup (locals (snd bf_stock_sol (Inl (Statement 4, ())))) (STR ''r'') = SPos"
  "bf_lookup (locals (snd bf_custom_sol (Inl (Statement 4, ())))) (STR ''r'') = SPos"
  by eval+

end
