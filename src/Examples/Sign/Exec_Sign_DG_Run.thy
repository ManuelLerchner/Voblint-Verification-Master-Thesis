theory Exec_Sign_DG_Run
  imports
    "Voblint_Analysis_Sign.Sign_Assembly"
    "Voblint_Analysis_Sign.Sign_Exec"
    "Voblint_Solver.TD_Solver_Bridge"
    "TD.TD_side_upd_rule"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Compile.Compile_Invariants"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Examples_CFG.Example_Compile_Call_Free"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N

section \<open>Running the verified solver on the native D/G spine (Sign)\<close>

text \<open>
  A concrete call-free Sign program is compiled to a CFG, its equation system is handed to
  the vendored always-join TD-side solver, and what the solver computes is turned into a
  guarantee about every source run of that program: whatever store a run reaches, the
  analysis result at the matching node describes it.

  Nothing here is registered locally. The equation system, the solve and every soundness
  endpoint are Sign's production always-join assembly, \<open>sign_join\<close>: the context-insensitive
  instance of the routed analysis, at the unit context. This file supplies only the
  program, one \<^verbatim>\<open>by eval\<close> termination fact and one coverage fact.

  The final theorem \<open>dgEx_source_run_sound\<close> turns that single solver success into the
  source-level guarantee, and it rests on the \<^emph>\<open>computed\<close> table, not on a hand-written
  candidate solution.
\<close>

subsection \<open>The concrete program and its compiled CFG\<close>

text \<open>
  A minimal call-free program \<^verbatim>\<open>x := 1; y := x\<close> inside \<open>main\<close>: the body occupies
  \<open>Statement 0\<close>--\<open>Statement 2\<close> between \<open>FunctionEntry (STR ''main'')\<close> and
  \<open>FunctionResult (STR ''main'')\<close>, and \<open>calls\<close> is empty.
\<close>

definition sign_ex_prog :: imp_prog where
  "sign_ex_prog = program { fun main() { x = 1; y = x; } }"

text \<open>The storage classifier: \<open>sign_ex_prog\<close> declares no globals, so \<open>sign_ex_gs\<close>
  classifies every variable this chain touches as local.\<close>
abbreviation sign_ex_gs :: "vname \<Rightarrow> bool" where
  "sign_ex_gs \<equiv> declared_global sign_ex_prog"

definition sign_ex_pi :: proc_table where
  "sign_ex_pi = prog_table sign_ex_prog"

definition gEx :: cfg where
  "gEx = compile_prog sign_ex_pi (prog_procs sign_ex_prog)"

lemma gEx_prog_cfg: "gEx = prog_cfg sign_ex_prog"
  by (simp add: gEx_def sign_ex_pi_def prog_cfg_def)

lemma gEx_calls: "calls gEx = {}"
  unfolding gEx_def sign_ex_pi_def
  by (rule compile_prog_calls_empty)
     (simp_all add: sign_ex_prog_def main_body_def prog_main_name_def)
interpretation gEx: compiled_cfg sign_ex_pi "prog_procs sign_ex_prog" gEx
  by (unfold_locales; unfold gEx_def; simp add: compile_prog_finite)

lemmas gEx_entry = gEx.entry[unfolded prog_main_name_def]
lemmas gEx_finE = gEx.finite_intra
lemmas gEx_finC = gEx.finite_calls

subsection \<open>The equation system and its solve\<close>

text \<open>\<open>dgEx_eqs\<close> is the production equation system at this program. The executable
  option-valued solver terminates on it --- a code-generated \<^verbatim>\<open>by eval\<close> fact --- which
  is the solver-domain predicate the assembly's endpoints take.\<close>

definition dgEx_eqs ::
  "pp \<times> unit
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
        (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) strategy_tree" where
  "dgEx_eqs = sign_unit_equations sign_ex_gs sign_ex_prog"

lemma dgEx_terminates_c: "TD_side_always_join_Interp_solve_c dgEx_eqs (cfg_exit gEx, ()) \<noteq> None"
  by eval

lemma dgEx_terminates: "sign_unit_terminates sign_ex_gs sign_ex_prog"
  unfolding sign_join.terminates_code
  using TD_side_always_join_Interp.solve_dom_of_solve_c[OF dgEx_terminates_c]
  by (simp add: dgEx_eqs_def gEx_prog_cfg)

subsection \<open>Well-formedness of the compiled input\<close>

lemma dgEx_wf:
  "wf_compile_input sign_ex_gs sign_ex_pi (prog_procs sign_ex_prog)"
  by (auto simp: wf_compile_input_simps sign_ex_pi_def sign_ex_prog_def split: if_splits)

subsection \<open>Collecting-semantics over-approximation from the computed result\<close>

text \<open>Coverage is read off the solved key set. A routed callee entry is solved only
  once a caller publishes its seed, so which nodes the solver visited is a fact
  about this run, decided by \<^const>\<open>vars_cover_exec\<close> over the two edge
  enumerations. \<open>gEx\<close> has no calls, so here it says every intra target was solved.\<close>

lemma dgEx_vars_cover:
  "vars_cover (prog_cfg sign_ex_prog) (sign_unit_vars sign_ex_gs sign_ex_prog)"
  by (rule sign_join.vars_cover_of_exec_prog) eval

theorem dgEx_source_run_sound:
  assumes run: "star (pstep sign_ex_gs sign_ex_pi) (prog_main sign_ex_prog, s, [])
                     (residual, t, frs)"
      and init: "s \<in> cinit_stores sign_ex_gs"
  shows "\<exists>v stk. csim sign_ex_pi gEx (residual, t, frs) (v, t, stk)
                 \<and> t \<in> \<lbrakk>sign_unit_state_at sign_ex_gs sign_ex_prog v\<rbrakk>"
proof -
  have run': "star (pstep sign_ex_gs (prog_table sign_ex_prog))
                (main_body (prog_table sign_ex_prog), s, []) (residual, t, frs)"
    using run by (simp add: sign_ex_pi_def)
  have wf: "wf_compile_input sign_ex_gs (prog_table sign_ex_prog) (prog_procs sign_ex_prog)"
    using dgEx_wf by (simp add: sign_ex_pi_def)
  show ?thesis
    using sign_join.source_sound[OF dgEx_terminates dgEx_vars_cover wf init run']
    by (simp add: gEx_prog_cfg sign_ex_pi_def)
qed

subsection \<open>Inspecting the computed result\<close>

text \<open>The unit instance routes the whole abstract state through the local unknown,
  reachability-lifted: the local answer at the exit is exactly \<open>Lifted\<close> of a state
  mapping \<open>x\<close> to \<open>SPos\<close>, with no separate global/side slot to inspect for a purely
  local name. Nothing further consumes this equation --- it is the readable form of what
  the solver computed, beside the theorem above that quantifies over every run.\<close>

lemma dgEx_inspect:
  "map_option (\<lambda>sol. case map_lift (fun_of_exec_dg_st_for sign_ex_gs)
                            (locals (snd sol (Inl (Statement 2, ()))))
                      of Lifted s \<Rightarrow> Some (s (STR ''x'')) | Bot \<Rightarrow> None)
     (TD_side_always_join_Interp_solve_c dgEx_eqs (cfg_exit gEx, ())) = Some (Some SPos)"
  by eval

end

