theory Example_Interval_DG_IP_Flagship
  imports
    "Voblint_Analysis_Interval.Interval_Transfer"
    "Voblint_Analysis_Interval.Interval_Exec"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Compile.Compile_Wellformed"
    "Voblint_VIMP.VIMP_Notation"
    Example_Interval_DG_Flagship
begin

section \<open>The context-insensitive (monovariant) interval flagship\<close>

text \<open>
  This is the non-context IP baseline: every call to \<open>twice\<close> is analyzed
  under a single, shared abstract state at \<open>FunctionEntry (STR ''twice'')\<close>,
  regardless of which call site reached it. It is the flagship the
  context-sensitive sibling \<open>Example_Interval_DG_Ctx_Flagship\<close> sharpens by
  routing on the entered argument's abstract value -- so run this file first to
  see the precision loss two calls to the same procedure with different
  arguments incur when their entry states are forced to join, then compare
  against the routed variant.
\<close>

definition twice_program :: imp_prog where
  "twice_program = program {
     void twice(p) { return p + p }
     void main() { x := twice(3); y := twice(10) }
   }"

definition twice_pi :: proc_table where "twice_pi = prog_table twice_program"
definition twice_procs :: "pname list" where "twice_procs = prog_procs twice_program"
definition twice_main :: "VIMP_Proc.com" where "twice_main = prog_main twice_program"

text \<open>The storage classifier: \<open>twice_program\<close> declares no globals, so \<open>twice_gs\<close>
  classifies every variable this chain touches as local, matching the
  \<open>declared_global\<close> pattern used by every other flagship rather than
  the \<open>is_global\<close> naming convention.\<close>
abbreviation twice_gs :: "vname \<Rightarrow> bool" where
  "twice_gs \<equiv> declared_global twice_program"

definition twice_cfg :: cfg where
  "twice_cfg = compile_prog twice_pi twice_procs"

text \<open>
  The compiled CFG.  Procedure \<open>twice\<close> runs between
  \<open>FunctionEntry (STR ''twice'')\<close> and \<open>FunctionResult (STR ''twice'')\<close>: the body's \<open>return p + p\<close>
  publishes through \<open>EA_Ret\<close> at statement \<open>0\<close>.  \<open>twice\<close> never falls through, so the
  continuation-passing compiler reserves no epilogue edge --- statement \<open>1\<close> is an
  unused index, not a node of the compiled graph.  \<open>main\<close> occupies statements \<open>2..4\<close>:
  \<open>2\<close> is the first call site, continuing directly at \<open>3\<close>, which is also the second
  call site, continuing at \<open>4\<close>.  Both call edges name the same callee entry
  \<open>FunctionEntry (STR ''twice'')\<close> --- this is the monovariant (single-context) view.
\<close>

interpretation twice: compiled_cfg twice_pi twice_procs twice_cfg
  by (unfold_locales; unfold twice_cfg_def; simp add: compile_prog_finite)

text \<open>The two call edges' shape, computed directly from \<open>twice_cfg\<close>: each call site \<open>u\<close>
  pins down its destination variable, callee, arguments, and continuation. Exported for the
  routed/context-sensitive sibling \<open>Example_Interval_DG_Ctx_Collect\<close>, which case-splits on
  the same two call sites.\<close>
lemma twice_calls_shape:
  "\<forall>(u, ca, ce, cont) \<in> calls twice_cfg.
     case ca of CallEdge dst pars args \<Rightarrow>
       (case ce of FunctionEntry p \<Rightarrow>
          (u = Statement 2 \<and> dst = Some (STR ''x'') \<and> pars = [(STR ''p'')]
             \<and> args = [VIMP_Syntax.N 3]
             \<and> p = (STR ''twice'') \<and> cont = Statement 3) \<or>
          (u = Statement 3 \<and> dst = Some (STR ''y'') \<and> pars = [(STR ''p'')]
             \<and> args = [VIMP_Syntax.N 10]
             \<and> p = (STR ''twice'') \<and> cont = Statement 4)
        | _ \<Rightarrow> True)"
  unfolding twice_cfg_def by eval

text \<open>Each call site has exactly one outgoing edge.\<close>
lemma twice_calls_unique_site:
  "\<forall>(u1, ca1, ce1, k1) \<in> calls twice_cfg. \<forall>(u2, ca2, ce2, k2) \<in> calls twice_cfg.
      u1 = u2 \<longrightarrow> ca1 = ca2 \<and> ce1 = ce2 \<and> k1 = k2"
  unfolding twice_cfg_def by eval

lemmas twice_finE = twice.finite_intra
lemmas twice_finC = twice.finite_calls

lemma twice_cfg_prog_cfg: "twice_cfg = prog_cfg twice_program"
  by (simp add: twice_cfg_def twice_pi_def twice_procs_def prog_cfg_def)

subsection \<open>The analysis, and its equation system at this program\<close>

text \<open>The analysis is \<open>interval_seed_join\<close> from \<open>Example_Interval_DG_Flagship\<close>:
  the routed analysis at the unit context, solved by the seed-joining warrowing rule.
  Both call sites publish into the one seed
  \<open>Activation_Seed (FunctionEntry (STR ''twice'')) ()\<close>, which is the monovariant view.\<close>

definition twice_eqs ::
  "pp \<times> unit
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
       (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) strategy_tree" where
  "twice_eqs = interval_sj_equations twice_gs twice_program"

lemma twice_terminates_c:
  "TD_side_seed_join_warrowing_Interp_solve_c is_activation_seed twice_eqs
     (cfg_exit twice_cfg, ()) \<noteq> None"
  by eval

lemma twice_terminates: "interval_sj_terminates twice_gs twice_program"
  unfolding interval_seed_join.terminates_code
  using TD_side_seed_join_warrowing_Interp.solve_dom_of_solve_c[OF twice_terminates_c]
  by (simp add: twice_eqs_def twice_cfg_prog_cfg)

text \<open>
  Coverage is read off the solved key set: a routed callee entry is solved only once
  a caller publishes its seed, so which nodes this run visited --- here both call
  sites, the shared callee entry, and both continuations --- is decided by
  \<^const>\<open>vars_cover_exec\<close> over the two edge enumerations.
\<close>

lemma twice_vars_cover:
  "vars_cover (prog_cfg twice_program) (interval_sj_vars twice_gs twice_program)"
  by (rule interval_seed_join.vars_cover_of_exec_prog) eval

subsection \<open>Inspecting the certified result\<close>

lemma twice_p_at_entry:
  "interval_sj_state_at twice_gs twice_program (FunctionEntry (STR ''twice'')) (STR ''p'')
     = Ivl (Fin 3) (Fin 10)"
  by eval

lemma twice_ret_at_exit:
  "interval_sj_state_at twice_gs twice_program (FunctionResult (STR ''twice'')) (STR ''#ret'')
     = Ivl (Fin 6) (Fin 20)"
  by eval

lemma twice_x_computed:
  "interval_sj_state_at twice_gs twice_program (Statement 3) (STR ''x'') = Ivl (Fin 6) (Fin 20)"
  by eval

lemma twice_y_computed:
  "interval_sj_state_at twice_gs twice_program (Statement 4) (STR ''y'') = Ivl (Fin 6) (Fin 20)"
  by eval

subsection \<open>Source-level soundness\<close>

lemma twice_main_body [simp]: "main_body twice_pi = twice_main"
  by (simp add: main_body_def prog_main_name_def twice_pi_def twice_program_def
        twice_main_def)

lemma twice_wf: "wf_compile_input twice_gs twice_pi twice_procs"
  by (auto simp: wf_compile_input_simps
      twice_pi_def twice_procs_def twice_main_def twice_program_def
      split: if_splits option.splits)

theorem twice_source_run_sound:
  assumes run: "star (pstep twice_gs twice_pi) (twice_main, s, []) src'"
      and init: "s \<in> cinit_stores twice_gs"
  shows "\<exists>v t stk. csim twice_pi twice_cfg src' (v, t, stk)
                   \<and> t \<in> \<lbrakk>interval_sj_state_at twice_gs twice_program v\<rbrakk>"
proof -
  obtain residual t frs where src': "src' = (residual, t, frs)" by (cases src')
  have run': "star (pstep twice_gs (prog_table twice_program))
                (main_body (prog_table twice_program), s, []) (residual, t, frs)"
    using run[unfolded src'] by (simp flip: twice_pi_def)
  have wf: "wf_compile_input twice_gs (prog_table twice_program) (prog_procs twice_program)"
    using twice_wf by (simp add: twice_pi_def twice_procs_def)
  have cert:
    "\<exists>v stk. csim twice_pi twice_cfg (residual, t, frs) (v, t, stk)
       \<and> t \<in> \<lbrakk>interval_sj_state_at twice_gs twice_program v\<rbrakk>"
    using interval_seed_join.source_sound[OF twice_terminates twice_vars_cover wf init run']
    by (simp add: twice_cfg_prog_cfg twice_pi_def)
  show ?thesis using cert src' by blast
qed

end




