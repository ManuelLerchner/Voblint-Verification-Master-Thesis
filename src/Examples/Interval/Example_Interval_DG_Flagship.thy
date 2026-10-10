section \<open>Flagship: interval analysis of a counting loop, executed and certified on the D/G spine\<close>

text \<open>
  A bounded counting loop is compiled to a CFG, the D/G framework turns that graph into
  an equation system, the verified solver computes an interval solution for it inside
  Isabelle, and the context-insensitive analysis turns that solution into a statement
  about every VIMP run of the source:
  \<open>flagship_source_run_sound\<close> bounds every store a run reaches by the published state at
  its matched program point. The bound is informative --- \<open>x in [0,20]\<close> at the loop head,
  \<open>[0,19]\<close> in the body, \<open>[20,20]\<close> on exit --- and \<open>flagship_head_bound_proper\<close> exhibits a
  store it rejects.

  The analysis is Interval's production registration at the unit context,
  \<open>interval_rule\<close>, with the joining global rule \<open>Globals_Join\<close>.
  \<open>Example_Interval_DG_IP_Flagship\<close> runs the same analysis on a program with
  calls.
\<close>

theory Example_Interval_DG_Flagship
  imports
    "Voblint_Analysis_Interval.Interval_Analyses"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Examples_CFG.Example_Compile_Call_Free"
begin

subsection \<open>The VIMP source program\<close>

text \<open>
  A bounded counting loop: initialise \<open>x\<close> to \<open>0\<close>, increment while \<open>x < 20\<close>.  On
  exit \<open>x = 20\<close>.  No procedures, no globals; \<open>x\<close> is a single flow-sensitive local.
  The analysis must \<^emph>\<open>discover\<close> the bound, not assume it.  The regression
  \<open>tests/regression/02-control-flow/precision/11-bounded_loop_guard_refines_body.vimp\<close>
  pins the same loop's head, body and exit values through the CLI.
\<close>

definition flagship_prog :: imp_prog where
  "flagship_prog = program { fun main() { x = 0; while (x < 20) { x = x + 1; } } }"

text \<open>The storage classifier: \<open>flagship_prog\<close> declares no globals, so \<open>flagship_gs\<close>
  classifies \<open>x\<close> as local.\<close>
abbreviation flagship_gs :: "vname \<Rightarrow> bool" where
  "flagship_gs \<equiv> declared_global flagship_prog"

subsection \<open>CFG construction\<close>

text \<open>
  The source compiles to an interprocedural CFG by \<open>compile_prog\<close>.  The whole program is
  the body of \<open>main\<close>, so it runs between \<open>FunctionEntry (STR ''main'')\<close> and
  \<open>FunctionResult (STR ''main'')\<close>; inside, \<open>x := 0\<close> falls directly into the loop head \<open>1\<close> (the
  continuation-passing compiler needs no separate join node), the guard \<open>x < 20\<close> branches
  to body \<open>2\<close> or exit \<open>3\<close>, and the increment at \<open>2\<close> jumps back to \<open>1\<close>.
\<close>

definition flagship_pi :: proc_table where
  "flagship_pi = prog_table flagship_prog"

definition flagship_cfg :: cfg where
  "flagship_cfg = compile_prog flagship_pi (prog_procs flagship_prog)"

interpretation flagship: compiled_cfg flagship_pi "prog_procs flagship_prog" flagship_cfg
  by (unfold_locales; unfold flagship_cfg_def; simp add: compile_prog_finite)

lemma flagship_calls: "calls flagship_cfg = {}"
  unfolding flagship_cfg_def flagship_pi_def
  by (rule compile_prog_calls_empty)
     (simp_all add: flagship_prog_def main_body_def prog_main_name_def)

lemma flagship_cfg_prog_cfg: "flagship_cfg = prog_cfg flagship_prog"
  by (simp add: flagship_cfg_def flagship_pi_def prog_cfg_def)

subsection \<open>Equation generation and the executable solve\<close>

text \<open>
  The solver --- pointwise interval warrowing at the loop head for termination ---
  \<^emph>\<open>computes\<close> a solution.  Termination is a code-generated \<^verbatim>\<open>by eval\<close> fact;
  the solution is not written by hand.
\<close>

definition flagship_eqs ::
  "pp \<times> unit
   \<Rightarrow> (pp \<times> unit, (unit, unit) global_unknown,
       (ivl default_st lifted, ivl default_st lifted) dg_state) strategy_tree" where
  "flagship_eqs = interval_rule.equations flagship_gs flagship_prog"

lemma flagship_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join flagship_eqs (cfg_exit flagship_cfg, ()) \<noteq> None"
  by eval

lemma flagship_terminates: "interval_rule.terminates Globals_Join flagship_gs flagship_prog"
  unfolding interval_rule.terminates_code
  using TD_side_rule_Interp.solve_dom_of_solve_c[OF flagship_terminates_c]
  by (simp add: flagship_eqs_def flagship_cfg_prog_cfg)

subsection \<open>Inspecting the certified result\<close>

text \<open>The published state at a program point, at the one unit context.\<close>

abbreviation flagship_at :: "pp \<Rightarrow> ivl abs_state" where
  "flagship_at \<equiv> interval_rule.state_at Globals_Join flagship_gs flagship_prog ()"

lemma flagship_head_computed:
  "flagship_at (Statement 1) (STR ''x'')
     = Ivl (Fin 0) (Fin 20)"
  by eval

lemma flagship_body_computed:
  "flagship_at (Statement 2) (STR ''x'')
     = Ivl (Fin 0) (Fin 19)"
  by eval

lemma flagship_exit_computed:
  "flagship_at (Statement 3) (STR ''x'')
     = Ivl (Fin 20) (Fin 20)"
  by eval

subsection \<open>Source-level soundness\<close>

text \<open>
  \<open>interval_rule.fun_route_source_sound\<close> turns the single \<^verbatim>\<open>by eval\<close> solver
  success \<open>flagship_terminates_c\<close> into a source-level guarantee: every reachable VIMP
  store is bounded by the interval state published at its matched program point,
  under the one context \<open>()\<close> the unit route names.
\<close>

lemma flagship_wf:
  "wf_compile_input flagship_gs flagship_pi (prog_procs flagship_prog)"
  unfolding wf_compile_input_def
  by (auto simp: wf_compile_input_simps flagship_pi_def flagship_prog_def split: if_splits)

theorem flagship_source_run_sound:
  assumes run:
    "flagship_gs, flagship_pi \<turnstile> (prog_main flagship_prog, s, []) \<rightarrow>\<^sub>p\<^sup>* (residual, t, frs)"
      and init: "s \<in> cinit_stores flagship_gs"
  shows "\<exists>v stk. flagship_pi, flagship_cfg \<turnstile> (residual, t, frs) \<approx> (v, t, stk)
                 \<and> t \<in> \<gamma> (flagship_at v)"
proof -
  have run':
    "flagship_gs, prog_table flagship_prog \<turnstile> (main_body (prog_table flagship_prog), s, []) \<rightarrow>\<^sub>p\<^sup>* (residual, t, frs)"
    using run by (simp add: flagship_pi_def)
  have wf: "wf_compile_input flagship_gs (prog_table flagship_prog) (prog_procs flagship_prog)"
    using flagship_wf by (simp add: flagship_pi_def)
  have unit_route: "\<And>u ctx d ca s. route_unit u ctx d ca = enterc_unit u ctx s" by simp
  show ?thesis
    using interval_rule.fun_route_source_sound[OF unit_route wf flagship_terminates init run']
    by (simp add: flagship_cfg_prog_cfg flagship_pi_def)
qed

text \<open>
  \<^bold>\<open>The bound is proper.\<close>  The published loop-head state constrains \<open>x\<close> to exactly
  \<open>[0,20]\<close> and rejects, e.g., a store with \<open>x = 100\<close>.  The guarantee therefore says
  something --- it is not the trivial \<open>\<gamma> \<top> = UNIV\<close>.
\<close>

theorem flagship_head_bound_proper:
  "(\<lambda>_. 100) \<notin> \<gamma> (flagship_at (Statement 1))"
proof
  assume "(\<lambda>_. 100) \<in> \<gamma> (flagship_at (Statement 1))"
  then have "(100::int) \<in> \<gamma> (flagship_at (Statement 1)
      (STR ''x''))"
    by (simp add: gamma_state_def)
  then show False using flagship_head_computed by simp
qed


end
