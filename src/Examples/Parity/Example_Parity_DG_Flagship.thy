section \<open>Flagship: parity analysis of an even-step loop, executed and certified on the D/G spine\<close>

text \<open>
  \<^bold>\<open>Second domain, same registration.\<close>  Parity is the second domain to reuse
  the domain-registration API without copying any of it: it registers through
  the \<open>local_state_dg_exec_analysis\<close> locale (as \<open>parity_ex_reg\<close> below, at this
  file's own storage classifier \<open>parity_gs\<close>) with \<^emph>\<open>no\<close> copied \<open>Hstep\<close>,
  \<open>Hcomb\<close>, \<open>strategy_tree\<close>, \<open>Inl\<close>/\<open>Inr\<close>, or manual post-solution transport
  lemmas.  A VIMP program is compiled to a CFG; the generic D/G framework
  generates the equation system; the \<^emph>\<open>verified\<close> always-join solver
  \<^emph>\<open>computes\<close> a parity solution inside Isabelle (the lattice is finite, so no
  widening is needed); and the single registered endpoint
  \<open>parity_ex_reg.run_source_sound\<close> lifts that result to actual source runs.

  The result is informative: the analysis \<^emph>\<open>discovers\<close> that \<open>x\<close> is even at
  every program point (\<open>x = 0\<close> initially, then \<open>x := x + 2\<close> preserves parity),
  so the invariant holds without any guard refinement --- parity ignores the
  guard.  \<open>Gcount\<close>, incremented by one on the same back edge, alternates and
  joins to \<open>PTop\<close>; the two locals therefore separate what the loop preserves
  from what it destroys.

  Registration is on the generic Base construction (\<open>DG_Local_State_Exec\<close>),
  matching Sign's own production route: the local unknown carries the whole
  reachability-lifted \<open>parity exec_dg_st\<close>, locals and \<open>total\<close> (the one
  declared global) alike, with no separate flow-insensitive \<open>G\<close> slot to
  reconstruct through.  \<open>total\<close> is therefore read back exactly as \<open>x\<close> and
  \<open>Gcount\<close> are: through the local unknown at a program point, not through a
  global summary.
\<close>

theory Example_Parity_DG_Flagship
  imports
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
    "Voblint_Analysis_Parity.Parity_Exec"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Compile.Compile_Wellformed"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Soundness.Run_Analysis_Sound"
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

      void main() {
        x := 0;
        Gcount:=1;
        while (x < 20) {
          x := x + 2;
          Gcount:=Gcount + 1
        };
        total:= x + Gcount
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

subsection \<open>Executable parity D/G specification\<close>

text \<open>
  Parity forms the Base D/G analysis, with executable mirror
  \<^const>\<open>local_state_dg_spec_st_for_lifted\<close> \<open>parity_gs\<close> over
  \<open>parity_tf_st_for\<close>/\<open>parity_enter_st_for\<close>.  The registration
  \<^locale>\<open>local_state_dg_exec_analysis\<close> --- interpreted as \<open>parity_ex_reg\<close>
  below, at this file's own classifier \<open>parity_gs\<close>, from
  \<open>parity_tf.is_sound_transfer_for\<close> and \<open>parity_tf_st_for_commute\<close> alone ---
  discharges the transport, soundness, and solver-crossing obligations
  generically.  This example supplies only the program, the executable solve,
  and the coverage witnesses.

  Two of those obligations are about this program rather than about parity, so
  they are proved first.  \<open>parity_wf\<close> is the compiler's well-formedness
  precondition on \<open>parity_pi\<close>.  \<open>parity_is_bot_exact\<close> is the
  emptiness-exactness obligation: the executable bottom test on a placed state
  must agree with emptiness of the state read back through \<open>parity_gs\<close>.  That
  is not automatic --- a placed state carries a value at both the local and the
  global tag of every name, while the readback keeps only the tag the
  classifier selects --- so the test has to filter the others out.
\<close>

lemma parity_wf: "wf_compile_input parity_gs parity_pi []"
  by (auto simp: wf_compile_input_simps parity_pi_def parity_prog_def parity_program_def
      split: if_splits)

lemma parity_is_bot_exact:
  fixes s :: "parity resolved_st_q"
  shows "resolved_st_q_is_bot_for (declared_global_vars parity_program) s
           = is_empty_state (fun_of_exec_dg_st_for parity_gs s)"
  by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff,
        folded fun_of_exec_dg_st_for_def])

subsection \<open>Registration through the classifier-parametric registration locale\<close>

text \<open>Interpret \<^locale>\<open>local_state_dg_exec_analysis\<close> once here at
  \<^const>\<open>parity_gs\<close> with the classifier-parametric transfer/enter functions,
  matching the pattern in \<open>Exec_Sign_DG_Run\<close>.  The interpretation absorbs the
  sound-transfer, primitive-commutation, and \<open>empty_pred\<close>-exactness obligations
  once, so \<open>parity_source_run_sound\<close> below only supplies the compiled-input and
  solver facts.\<close>

interpretation parity_ex_reg:
  local_state_dg_exec_analysis parity_gs
    skip_parity assign_parity special_parity branch_parity body_parity return_parity
    "enter_parity_ci_for parity_gs" event_parity
    "parity_tf_st_for parity_gs" "parity_enter_st_for parity_gs"
    "resolved_st_q_is_bot_for (declared_global_vars parity_program)"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret parity_ex_transfer: sound_transfer_for parity_gs
      skip_parity assign_parity special_parity branch_parity body_parity return_parity
      "enter_parity_ci_for parity_gs" event_parity
    by (rule parity_tf.is_sound_transfer_for)
  show "local_state_dg_exec_analysis parity_gs
          skip_parity assign_parity special_parity branch_parity body_parity return_parity
          (enter_parity_ci_for parity_gs) event_parity
          (parity_tf_st_for parity_gs) (parity_enter_st_for parity_gs)
          (resolved_st_q_is_bot_for (declared_global_vars parity_program))
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule parity_wf[THEN wf_compile_input_reserved_ret_var]
             parity_ex_transfer.tf_sound_assign_for parity_ex_transfer.tf_sound_special_for
             parity_ex_transfer.tf_sound_branch_for
             parity_ex_transfer.tf_sound_enter_entry_for
             parity_tf_st_for_commute[unfolded parity_tf.tf_abs_def,
                                      folded fun_of_exec_dg_st_for_def]
             parity_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             parity_is_bot_exact
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

subsection \<open>Equation generation\<close>

text \<open>The registration locale owns the equation system: \<open>parity_eqs\<close> names
  \<^const>\<open>parity_ex_reg.routed_eqs\<close> at this program, the routed generator at the
  unit context.\<close>

definition parity_eqs ::
  "pp \<times> unit
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
        (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state) strategy_tree" where
  "parity_eqs = parity_ex_reg.routed_eqs parity_pi [] bot
                  (Lifted cinit_parity_st) (Lifted cinit_parity_st)"

subsection \<open>Executable solve (always-join; parity is finite-height)\<close>

lemma parity_terminates_c:
  "TD_side_always_join_Interp_solve_c parity_eqs (cfg_exit parity_cfg, ()) \<noteq> None"
  by eval

definition parity_sol ::
  "(pp \<times> unit) set
   \<times> (pp \<times> unit + (unit, unit) routed_gk
        \<Rightarrow> (parity exec_dg_st lifted, parity exec_dg_st lifted) dg_state)" where
  "parity_sol = TD_side_always_join_Interp_solve parity_eqs (cfg_exit parity_cfg, ())"

subsection \<open>Soundness premises for the registered endpoint\<close>

text \<open>Coverage is read off the solved key set: a routed callee entry is solved
  only once a caller publishes its seed, so which nodes this run visited is a
  fact about the run, decided by \<^const>\<open>vars_cover_exec\<close> over the two edge
  enumerations.  Here \<open>main\<close> calls no procedure and no other procedure is
  compiled, so \<open>parity_cfg\<close> carries no call edges at all and the fact says
  every intra target was solved.\<close>

lemma parity_vars_cover: "vars_cover parity_cfg (fst parity_sol)"
  by (rule vars_cover_of_exec[OF parity_flagship.finite_intra parity_flagship.finite_calls])
     eval

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

subsection \<open>Source-level soundness through the registered analysis\<close>

text \<open>
  The registered endpoint \<open>parity_ex_reg.run_source_sound\<close> turns the single
  \<open>by eval\<close> solver success \<open>parity_terminates_c\<close> directly into a source-level
  guarantee: every reachable VIMP store is bounded by the computed parity at
  its matched program point, read through the semantic accessor
  \<open>parity_ex_reg.gamma\<close>.  No transport lemma, \<^const>\<open>part_post_solution\<close>,
  \<open>solve_dom\<close>, or \<open>fun_of_dg_st_for\<close> appears in this proof.
\<close>

lemma parity_main_body [simp]: "main_body parity_pi = parity_prog"
  by (simp add: main_body_def prog_main_name_def parity_pi_def parity_program_def
        parity_prog_def)

text \<open>The initial stores are covered by the registered concretization at the
  initial local value. Stated in \<^const>\<open>parity_ex_reg.gamma_exec\<close> itself rather
  than in its unfolding, because that is the vocabulary \<open>run_source_sound\<close>
  assumes.\<close>
lemma parity_sound0:
  "cinit_stores parity_gs
     \<subseteq> parity_ex_reg.gamma_exec (Lifted cinit_parity_st) (Lifted cinit_parity_st)"
  by (auto simp add: parity_ex_reg.gamma_exec_def fun_of_exec_dg_st_for_def
      fun_of_st_cinit_parity_st_for cinit_stores_def gamma_state_def)

theorem parity_source_run_sound:
  assumes run: "star (pstep parity_gs parity_pi) (parity_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores parity_gs"
  shows "\<exists>v stk. csim parity_pi parity_cfg (residual, t, frs) (v, t, stk)
                 \<and> t \<in> parity_ex_reg.gamma (fst parity_sol) (snd parity_sol) v"
proof -
  have run': "star (pstep parity_gs parity_pi) (main_body parity_pi, s, []) (residual, t, frs)"
    using run by simp
  show ?thesis
    unfolding parity_sol_def parity_eqs_def parity_cfg_def
    by (rule parity_ex_reg.run_source_sound
          [OF parity_terminates_c[unfolded parity_eqs_def parity_cfg_def]
              parity_wf
              parity_vars_cover[unfolded parity_sol_def parity_eqs_def parity_cfg_def]
              parity_flagship.finite_intra[unfolded parity_cfg_def]
              parity_sound0
              init run'])
qed

subsection \<open>The result is not vacuous\<close>

text \<open>
  \<open>parity_source_run_sound\<close> would say nothing if the concretization it reads
  through were all of \<^const>\<open>UNIV\<close>.  It is not, and the three steps below
  descend from the computed domain element to a concrete store: \<open>PEven\<close> is
  strictly below \<open>PTop\<close>, its concretization holds no odd integer, and so the
  loop head's own concretization --- stated in \<^const>\<open>parity_ex_reg.gamma_exec\<close>,
  the vocabulary \<open>parity_sound0\<close> and \<open>run_source_sound\<close> use --- rejects the
  constant store \<open>\<lambda>_. 1\<close>.  A store is therefore genuinely excluded, which is
  what makes the guarantee informative.
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

lemma parity_gamma_exec_pointwise:
  assumes "s \<in> parity_ex_reg.gamma_exec d g"
  shows "s x \<in> gamma_parity (parity_lookup d x)"
  using assms
  by (cases "map_lift (fun_of_exec_dg_st_for parity_gs) d")
     (auto simp: parity_ex_reg.gamma_exec_def fun_of_exec_dg_st_for_def gamma_state_def)

theorem parity_head_excludes_odd_store:
  "(\<lambda>_. 1) \<notin> parity_ex_reg.gamma_exec
                 (locals (snd parity_sol (Inl (Statement 2, ())))) bot"
proof
  assume "(\<lambda>_. 1) \<in> parity_ex_reg.gamma_exec
                      (locals (snd parity_sol (Inl (Statement 2, ())))) bot"
  from parity_gamma_exec_pointwise[OF this, where x = "STR ''x''"]
  have "(1::int) \<in> gamma_parity
      (parity_lookup (locals (snd parity_sol (Inl (Statement 2, ())))) (STR ''x''))"
    by simp
  from parity_head_excludes_odd[OF this] show False by simp
qed

end

