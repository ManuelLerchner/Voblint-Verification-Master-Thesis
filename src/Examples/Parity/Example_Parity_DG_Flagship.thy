section \<open>Flagship: parity analysis of an even-step loop, executed and certified on the D/G spine\<close>

text \<open>
  \<^bold>\<open>Second domain, same assembly.\<close>  Parity reaches source-level soundness through
  its own production unit-context registration \<open>parity_rule\<close>, at the always-join
  rule \<open>Globals_Join\<close> --- the context-insensitive instance of the routed analysis --- with
  \<^emph>\<open>no\<close> example-local registration, \<open>strategy_tree\<close>, \<open>Inl\<close>/\<open>Inr\<close>, or manual
  post-solution transport lemmas.  A VIMP program is compiled to a CFG; the generic
  D/G framework generates the equation system; the \<^emph>\<open>verified\<close> always-join solver
  \<^emph>\<open>computes\<close> a parity solution inside Isabelle (the lattice is finite, so no
  widening is needed); and the assembly's \<open>source_sound\<close> endpoint lifts that result
  to actual source runs.

  The result is informative: the analysis \<^emph>\<open>discovers\<close> that \<open>x\<close> is even at
  every program point (\<open>x = 0\<close> initially, then \<open>x := x + 2\<close> preserves parity),
  so the invariant holds without any guard refinement --- parity ignores the
  guard.  \<open>Gcount\<close>, incremented by one on the same back edge, alternates and
  joins to \<open>PTop\<close>; the two locals therefore separate what the loop preserves
  from what it destroys.

  The local unknown carries the whole reachability-lifted \<open>parity exec_dg_st\<close>,
  locals and \<open>total\<close> (the one declared global) alike, with no separate
  flow-insensitive \<open>G\<close> slot to reconstruct through.  \<open>total\<close> is therefore read back
  exactly as \<open>x\<close> and \<open>Gcount\<close> are: through the local unknown at a program point,
  not through a global summary.
\<close>

theory Example_Parity_DG_Flagship
  imports
    "Voblint_Analysis_Parity.Parity_Analyses"
    "Voblint_Analysis_Parity.Parity_Exec"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Compile.Compile_Wellformed"
    "Voblint_VIMP.VIMP_Notation"
begin

text \<open>The vendored solver's \<open>phase\<close> datatype and VIMP's expression syntax both
  declare a constructor \<open>N\<close>, and VIMP's is the integer literal every numeral in
  the program below elaborates to.  Hiding the solver's leaves \<open>N\<close> resolving to
  VIMP's.  Sibling theories write the same hiding as \<open>hide_const phase.N\<close>, which
  names the same constructor through its datatype instead of its theory.\<close>
hide_const (open) Update_rules.N

subsection \<open>The VIMP source program\<close>

text \<open>
  A bounded counting loop that increments by two: initialise \<open>x\<close> to \<open>0\<close>, add
  \<open>2\<close> while \<open>x < 20\<close>.  No procedures beyond \<open>main\<close>; \<open>x\<close> is a single
  flow-sensitive local, \<open>Gcount\<close> a second, \<open>G\<close>-prefixed local, and \<open>total\<close> the
  one declared global despite carrying no naming hint.  The parity of \<open>x\<close> stays
  even at every reachable point regardless of the guard, which the analysis
  must discover, not assume.
\<close>

definition parity_program :: imp_prog where
  "parity_program = program {

      global total;

      fun main() {
        x = 0;
        Gcount=1;
        while (x < 20) {
          x = x + 2;
          Gcount=Gcount + 1;
        }
        total= x + Gcount;
      }
}"

definition parity_prog :: "VIMP_Proc.com" where
  "parity_prog = prog_main parity_program"

text \<open>The storage classifier: \<open>total\<close> is declared global despite its plain
  name, and \<open>Gcount\<close> stays local despite its \<open>G\<close> prefix, so \<open>parity_gs\<close> reads
  the program's own declaration rather than a naming convention.  The two
  lemmas below pin both directions.\<close>
abbreviation parity_gs :: "vname \<Rightarrow> bool" where
  "parity_gs \<equiv> declared_global parity_program"

lemma parity_total_global [simp]: "parity_gs (STR ''total'')"
  by (simp add: parity_program_def)

lemma parity_gcount_not_global [simp]: "\<not> parity_gs (STR ''Gcount'')"
  by (simp add: parity_program_def)

text \<open>
  The Base construction routes the whole abstract state through the local
  unknown, reachability-lifted: \<open>parity_lookup\<close> reads a computed
  \<open>exec_dg_st lifted\<close> value back through \<^const>\<open>fun_of_exec_dg_st_for\<close>,
  matching Sign's own DG flagship -- a genuinely unreachable local unknown
  (\<open>Bot\<close>) reads back as \<open>PTop\<close>, never spuriously observed here since every
  inspected node below is reachable.
\<close>
abbreviation parity_lookup :: "parity exec_dg_st lifted \<Rightarrow> vname \<Rightarrow> parity" where
  "parity_lookup d x \<equiv>
     (case map_lift (fun_of_exec_dg_st_for parity_gs) d of Lifted f \<Rightarrow> f x | Bot \<Rightarrow> PTop)"

definition parity_pi :: proc_table where
  "parity_pi = prog_table parity_program"

subsection \<open>CFG construction\<close>

text \<open>
  The source compiles to an interprocedural CFG by \<open>compile_prog\<close>.  The whole
  program is the body of \<open>main\<close>, so it runs between
  \<open>FunctionEntry (STR ''main'')\<close> and \<open>FunctionResult (STR ''main'')\<close>, and the
  compiler allocates one \<open>Statement\<close> point per command in source order: \<open>0\<close>
  before \<open>x := 0\<close>, \<open>1\<close> before \<open>Gcount := 1\<close>, \<open>2\<close> the loop head carrying the
  guard \<open>x < 20\<close>, \<open>3\<close> the loop body's first point before \<open>x := x + 2\<close>, \<open>4\<close>
  before \<open>Gcount := Gcount + 1\<close> (whose edge closes the loop back to \<open>2\<close>), \<open>5\<close>
  where the guard's false edge leaves the loop, and \<open>6\<close> after
  \<open>total := x + Gcount\<close>.  The readings further below inspect \<open>2\<close> and \<open>5\<close>.
\<close>

definition parity_cfg :: cfg where
  "parity_cfg = compile_prog parity_pi []"

text \<open>Interpreting \<^locale>\<open>compiled_cfg\<close> at that defining equation supplies
  finiteness of both edge relations, the entry and exit nodes, and
  well-formedness at once, already phrased in this file's own graph name.\<close>
interpretation parity_flagship: compiled_cfg parity_pi "[]" parity_cfg
  by (unfold_locales; unfold parity_cfg_def; simp add: compile_prog_finite)

lemma parity_cfg_prog_cfg: "parity_cfg = prog_cfg parity_program"
  by (simp add: parity_cfg_def parity_pi_def prog_cfg_def parity_program_def)

lemma parity_wf: "wf_compile_input parity_gs parity_pi []"
  by (auto simp: wf_compile_input_simps parity_pi_def parity_prog_def parity_program_def
      split: if_splits)

subsection \<open>Equation generation and the executable solve\<close>

text \<open>The equation system is \<open>parity_rule.equations\<close> at this program: the
  routed generator at the unit context, over the local-state specification.  The
  always-join solver suffices because parity has finite height.\<close>

definition parity_eqs ::
  "pp \<times> unit
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
        (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) strategy_tree" where
  "parity_eqs = parity_rule.equations parity_gs parity_program"

lemma parity_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join parity_eqs (cfg_exit parity_cfg, ()) \<noteq> None"
  by eval

lemma parity_terminates: "parity_rule.terminates Globals_Join parity_gs parity_program"
  unfolding parity_rule.terminates_code
  using TD_side_rule_Interp.solve_dom_of_solve_c[OF parity_terminates_c]
  by (simp add: parity_eqs_def parity_cfg_prog_cfg)

definition parity_sol ::
  "(pp \<times> unit) set
   \<times> (pp \<times> unit + (unit, unit) routed_gk
        \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "parity_sol = TD_side_rule_Interp_solve Globals_Join parity_eqs (cfg_exit parity_cfg, ())"

subsection \<open>Coverage\<close>

text \<open>Coverage is read off the solved key set: a routed callee entry is solved
  only once a caller publishes its seed, so which nodes this run visited is a
  fact about the run, decided by \<^const>\<open>vars_cover_exec\<close> over the two edge
  enumerations.  Here \<open>main\<close> calls no procedure and no other procedure is
  compiled, so \<open>parity_cfg\<close> carries no call edges at all and the fact says
  every intra target was solved.\<close>

lemma parity_vars_cover:
  "vars_cover (prog_cfg parity_program)
     (parity_rule.sol_vars Globals_Join parity_gs parity_program)"
  by (rule parity_rule.vars_cover_of_exec_prog) eval

subsection \<open>Inspecting the certified result\<close>

text \<open>Four readings of the solved table, all through the same local unknown.
  \<open>x\<close> is \<open>PEven\<close> at the loop head and still \<open>PEven\<close> where the loop is left, so
  the even-step invariant survives the join with the back edge.  \<open>Gcount\<close> does
  not survive it: incremented by one, it joins odd against even and reaches
  \<open>PTop\<close>.  \<open>total\<close>, the declared global, is read at the same node out of the
  same unknown as the two locals, and still carries its zero-initialised
  \<open>PEven\<close> there because the loop never writes it.\<close>

lemma parity_head_computed:
  "parity_lookup (locals (snd parity_sol (Inl (Statement 2, ())))) (STR ''x'') = PEven"
  unfolding parity_sol_def parity_eqs_def by eval

lemma parity_head_gcount_computed:
  "parity_lookup (locals (snd parity_sol (Inl (Statement 2, ())))) (STR ''Gcount'') = PTop"
  unfolding parity_sol_def parity_eqs_def by eval

lemma parity_exit_computed:
  "parity_lookup (locals (snd parity_sol (Inl (Statement 5, ())))) (STR ''x'') = PEven"
  unfolding parity_sol_def parity_eqs_def by eval

lemma parity_exit_total_computed:
  "parity_lookup (locals (snd parity_sol (Inl (Statement 5, ())))) (STR ''total'') = PEven"
  unfolding parity_sol_def parity_eqs_def by eval

subsection \<open>Source-level soundness through the production assembly\<close>

text \<open>
  \<open>parity_rule.source_sound\<close> turns the single \<^verbatim>\<open>by eval\<close> solver success
  \<open>parity_terminates_c\<close> into a source-level guarantee: every reachable VIMP store
  is described by the published state at its matched program point.  No transport
  lemma, \<^const>\<open>part_post_solution\<close>, or readback appears in this proof.
\<close>

lemma parity_main_body [simp]: "main_body parity_pi = parity_prog"
  by (simp add: main_body_def prog_main_name_def parity_pi_def parity_program_def
        parity_prog_def)

theorem parity_source_run_sound:
  assumes run: "parity_gs, parity_pi \<turnstile> (parity_prog, s, []) \<rightarrow>\<^sub>p\<^sup>* (residual, t, frs)"
      and init: "s \<in> cinit_stores parity_gs"
  shows "\<exists>v stk. parity_pi, parity_cfg \<turnstile> (residual, t, frs) \<approx> (v, t, stk)
                 \<and> t \<in> \<lbrakk>parity_rule.state_at Globals_Join parity_gs parity_program v\<rbrakk>"
proof -
  have run': "parity_gs, prog_table parity_program \<turnstile> (main_body (prog_table parity_program), s, []) \<rightarrow>\<^sub>p\<^sup>* (residual, t, frs)"
    using run by (simp flip: parity_pi_def)
  have wf: "wf_compile_input parity_gs (prog_table parity_program) (prog_procs parity_program)"
    using parity_wf parity_cfg_prog_cfg
    by (simp add: parity_pi_def parity_program_def)
  show ?thesis
    using parity_rule.source_sound[OF parity_terminates parity_vars_cover wf init run']
    by (simp add: parity_cfg_prog_cfg parity_pi_def)
qed

subsection \<open>The result is not vacuous\<close>

text \<open>
  \<open>parity_source_run_sound\<close> would say nothing if the state it reads through
  concretized to all of \<^const>\<open>UNIV\<close>.  It does not: the published state at the
  loop head maps \<open>x\<close> to \<open>PEven\<close>, whose concretization holds no odd integer, so
  it rejects the constant store \<open>\<lambda>_. 1\<close>.  A store is therefore genuinely
  excluded, which is what makes the guarantee informative.
\<close>

lemma parity_head_proper:
  "parity_lookup (locals (snd parity_sol (Inl (Statement 2, ())))) (STR ''x'') \<noteq> PTop"
  by (simp add: parity_head_computed)

lemma parity_head_excludes_odd:
  fixes n :: int
  assumes "n \<in> gamma_parity
     (parity_lookup (locals (snd parity_sol (Inl (Statement 2, ())))) (STR ''x''))"
  shows "even n"
  using assms by (simp add: parity_head_computed)

lemma parity_state_at_head_x:
  "parity_rule.state_at Globals_Join parity_gs parity_program (Statement 2) (STR ''x'') = PEven"
  unfolding parity_rule.state_at_unfold by eval

theorem parity_head_excludes_odd_store:
  "(\<lambda>_. 1) \<notin> \<lbrakk>parity_rule.state_at Globals_Join parity_gs parity_program (Statement 2)\<rbrakk>"
proof
  assume "(\<lambda>_. 1) \<in> \<lbrakk>parity_rule.state_at Globals_Join parity_gs parity_program (Statement 2)\<rbrakk>"
  then have "(1::int) \<in> gamma_parity
      (parity_rule.state_at Globals_Join parity_gs parity_program (Statement 2) (STR ''x''))"
    by (simp add: gamma_state_def)
  then show False by (simp add: parity_state_at_head_x)
qed

end

