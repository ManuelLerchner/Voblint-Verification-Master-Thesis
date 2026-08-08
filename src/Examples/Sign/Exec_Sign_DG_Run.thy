section \<open>Running the verified solver on the native D/G spine (Sign)\<close>

text \<open>
  An end-to-end certified run on the carrier-opaque D/G equation system, registered
  through the \<open>unit_dg_exec_analysis\<close> locale (interpreted as \<open>sign_ex_reg\<close> below, at
  this file's own storage classifier \<open>sign_ex_gs\<close>, from just \<open>sign_is_sound_transfer_for\<close>
  and \<open>sign_tf_st_for_commute\<close>).
  A concrete call-free Sign program is compiled to a CFG; the executable D/G
  generator (\<open>dg_gen_of (unit_dg_spec_st sign_tf_st)\<close>, values in
  \<open>(sign exec_dg_st, sign exec_dg_st) dg_state\<close>) is handed to the vendored always-join TD-side
  solver; the solver \<^emph>\<open>computes\<close> a partial post-solution.

  The final theorem \<open>dgEx_source_run_sound\<close> turns the single \<open>by eval\<close> solver success
  directly into a source-level guarantee, matching the pattern in
  \<open>Example_Interval_DG_Flagship\<close>: no transport lemma, \<open>part_post_solution\<close>, \<open>solve_dom\<close>,
  or \<open>fun_of_dg_st\<close> appears in this file's own proofs.  It depends on the \<^emph>\<open>computed\<close>
  solver result \<open>snd dgEx_sol\<close>, not on any hand-written candidate solution.
\<close>

theory Exec_Sign_DG_Run
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Analysis.Sign_DG"
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Formalization.Run_Analysis_Sound"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
subsection \<open>The concrete program and its compiled CFG\<close>

text \<open>
  A minimal call-free program \<^verbatim>\<open>x := 1; y := x\<close> inside \<open>main\<close>: the body occupies
  \<open>Statement 0\<close>--\<open>Statement 2\<close> between \<open>FunctionEntry ''main''\<close> and
  \<open>FunctionResult ''main''\<close>, and \<open>calls\<close> is empty.  \<open>gEx_eq\<close> proves the compilation
  equals the explicit graph, matching the source-soundness pattern in
  \<open>Example_Interval_DG_Flagship\<close>.
\<close>

definition sign_ex_prog :: imp_prog where
  "sign_ex_prog = program { void main() { x := 1; y := x } }"

text \<open>The storage classifier: \<open>sign_ex_prog\<close> declares no globals, so \<open>sign_ex_gs\<close>
  classifies every variable this chain touches as local. This validates
  domain-independence of the generic transport, matching \<open>parity_gs\<close>'s role for the
  parity flagship, rather than global/local separation.\<close>
abbreviation sign_ex_gs :: "vname \<Rightarrow> bool" where
  "sign_ex_gs \<equiv> declared_global sign_ex_prog"

text \<open>Local shorthand for the executable state's lookup projection, fixed at this
  file's own \<open>sign_ex_gs\<close> classifier.\<close>
abbreviation sign_ex_lookup :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "sign_ex_lookup s x \<equiv> lookup_resolved_st_q s (location_of sign_ex_gs x)"

definition sign_ex_pi :: proc_table where
  "sign_ex_pi = prog_table sign_ex_prog"

definition gEx :: cfg where
  "gEx = compile_prog sign_ex_pi (prog_procs sign_ex_prog) prog_main_name (prog_main sign_ex_prog)"

lemma gEx_calls: "calls gEx = {}" by eval
lemma gEx_entry: "cfg_entry gEx = FunctionEntry ''main''" by eval
lemma gEx_finE: "finite (intra gEx)" unfolding gEx_def using compile_prog_finite by simp
lemma gEx_finC: "finite (calls gEx)" unfolding gEx_def using compile_prog_finite by simp

definition dgEx_eqs :: "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "dgEx_eqs = dg_gen_of (unit_dg_spec_st_for sign_ex_gs (sign_tf_st_for sign_ex_gs) (sign_enter_st_for sign_ex_gs)) gEx bot cinit_sign_st cinit_sign_st"

definition dgEx_sol :: "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "dgEx_sol = TD_side_always_join_Interp_solve dgEx_eqs (cfg_exit gEx, ())"

subsection \<open>The solver computes a partial post-solution\<close>

text \<open>
  The executable option-valued solver terminates on the D/G equation system --- a
  code-generated \<open>by eval\<close> fact --- so the solver-domain predicate holds and the
  vendored partial-post-solution theorem applies to the computed result.
\<close>

lemma dgEx_terminates_c: "TD_side_always_join_Interp_solve_c dgEx_eqs (cfg_exit gEx, ()) \<noteq> None"
  by eval

lemma dgEx_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE((sign exec_dg_st, sign exec_dg_st) dg_state) dgEx_eqs (cfg_exit gEx, ())"
  using dgEx_terminates_c
  unfolding TD_side_always_join_Interp.term_equivalence TD_side_always_join_Interp.solve_c_dom_def
  by simp

lemma dgEx_pp_st:
  "part_post_solution dgEx_eqs (cfg_exit gEx, ()) (snd dgEx_sol) (fst dgEx_sol)"
  using TD_side_always_join_Interp.partial_post_solution[OF dgEx_solve_dom, of "fst dgEx_sol" "snd dgEx_sol"]
  unfolding dgEx_sol_def by simp

subsection \<open>Well-formedness of the compiled input\<close>

lemma dgEx_wf:
  "wf_compile_input sign_ex_gs sign_ex_pi (prog_procs sign_ex_prog) prog_main_name (prog_main sign_ex_prog)"
  unfolding wf_compile_input_def wf_source_program_def wf_proc_decl_def
    sign_ex_pi_def sign_ex_prog_def
  by (auto simp: source_aexp_def source_bexp_def proc_decl_of_def ret_var_def
      reserved_ret_var_def split: if_splits)

subsection \<open>Collecting-semantics over-approximation from the computed result\<close>

lemma dgEx_cover_entry: "(cfg_entry gEx, ()) \<in> fst dgEx_sol"
  unfolding dgEx_sol_def gEx_entry by eval

lemma dgEx_cover_edge_ball: "\<forall>(u, a, w) \<in> intra gEx. (w, ()) \<in> fst dgEx_sol"
  unfolding dgEx_sol_def by eval
lemma dgEx_cover_edge: "\<And>u a w. (u, a, w) \<in> intra gEx \<Longrightarrow> (w, ()) \<in> fst dgEx_sol"
  using dgEx_cover_edge_ball by auto
lemma dgEx_cover_enter:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls gEx
     \<Longrightarrow> (FunctionEntry p, ()) \<in> fst dgEx_sol"
  by (simp add: gEx_calls)
lemma dgEx_cover_combine:
  "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls gEx
     \<Longrightarrow> (k, ()) \<in> fst dgEx_sol"
  by (simp add: gEx_calls)
lemma dgEx_sound0:
  "cinit_stores sign_ex_gs \<subseteq> \<lbrakk>fun_of_exec_dg_st_for sign_ex_gs cinit_sign_st \<squnion> fun_of_exec_dg_st_for sign_ex_gs cinit_sign_st\<rbrakk>"
  by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for cinit_stores_def gamma_state_def sup.idem)

subsection \<open>Registration through the classifier-parametric registration locale\<close>

text \<open>Interpret \<^locale>\<open>unit_dg_exec_analysis\<close> once here at \<^const>\<open>sign_ex_gs\<close>
  with the classifier-parametric transfer/enter functions, matching the pattern in
  \<open>Example_Parity_DG_Flagship\<close>.  The interpretation absorbs the sound-transfer and
  primitive-commutation obligations once, so \<open>dgEx_source_run_sound\<close> below only
  supplies the compiled-input and solver facts.\<close>

interpretation sign_ex_reg:
  unit_dg_exec_analysis sign_ex_gs
    "sign_tf_for sign_ex_gs" "sign_tf_st_for sign_ex_gs" "sign_enter_st_for sign_ex_gs"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret sign_ex_transfer: sound_transfer_for sign_ex_gs "sign_tf_for sign_ex_gs"
    by (rule sign_is_sound_transfer_for)
  show "unit_dg_exec_analysis sign_ex_gs (sign_tf_for sign_ex_gs) (sign_tf_st_for sign_ex_gs)
          (sign_enter_st_for sign_ex_gs)
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule sign_ex_transfer.tf_sound_assign_for sign_ex_transfer.tf_sound_random_for
             sign_ex_transfer.tf_sound_assume_for sign_ex_transfer.tf_sound_assume_not_for
             sign_ex_transfer.tf_sound_enter_for sign_ex_transfer.tf_sound_combine_for
             sign_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             sign_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF sign_tf_st_for_reduces]
             action_reduces.ret_some[OF sign_tf_st_for_reduces]
             action_reduces.check[OF sign_tf_st_for_reduces]
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

theorem dgEx_source_run_sound:
  assumes run: "star (pstep sign_ex_gs sign_ex_pi) (prog_main sign_ex_prog, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores sign_ex_gs"
  shows "\<exists>v stk. csim sign_ex_pi gEx (residual, t, frs) (v, t, stk)
                 \<and> t \<in> sign_ex_reg.gamma (snd dgEx_sol) v"
proof -
  show ?thesis
    unfolding dgEx_sol_def dgEx_eqs_def gEx_def
    by (rule sign_ex_reg.run_source_sound
          [OF dgEx_terminates_c[unfolded dgEx_eqs_def gEx_def]
              dgEx_wf
              dgEx_cover_entry[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
              dgEx_cover_edge[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
              dgEx_cover_enter[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
              dgEx_cover_combine[unfolded dgEx_sol_def dgEx_eqs_def gEx_def]
              gEx_finE[unfolded gEx_def]
              gEx_finC[unfolded gEx_def]
              dgEx_sound0[folded gamma_unit_def]
              init run[unfolded gEx_def]])
qed

subsection \<open>Inspecting the computed result\<close>

text \<open>The diagonal Sign instance joins local answers and global side effects at
  each edge. The executable result is therefore sound but imprecise at the exit.\<close>

lemma dgEx_inspect:
  "map_option (\<lambda>sol. (sign_ex_lookup (locals (snd sol (Inl (Statement 2, ())))) ''x'',
                       sign_ex_lookup (globs (snd sol (Inr ()))) ''x''))
     (TD_side_always_join_Interp_solve_c dgEx_eqs (cfg_exit gEx, ())) = Some (STop, STop)"
  by eval

subsection \<open>Whole-program entry point: an arbitrary VIMP program\<close>

text \<open>
  \<open>gEx\<close>/\<open>dgEx_eqs\<close>/\<open>dgEx_sol\<close> above fix one hard-coded example.  This section
  widens that same native D/G chain to an arbitrary classifier \<open>gs\<close> and
  program \<open>p\<close>, reusing \<^const>\<open>prog_cfg\<close> for the compiled CFG.  The locale
  interpretation below is the classifier-generic twin of \<open>sign_ex_reg\<close> above:
  the same five transfer facts discharge \<^locale>\<open>unit_dg_exec_analysis\<close> at
  any classifier, not only at \<open>sign_ex_gs\<close>, because \<open>sign_is_sound_transfer_for\<close>,
  \<open>sign_tf_st_for_commute\<close>, and \<open>sign_enter_st_for_commute\<close> are already stated
  for an arbitrary \<open>gs\<close>.  \<open>gs\<close> stays an explicit parameter (rather than
  hard-wired to \<^const>\<open>declared_global\<close> applied to \<open>p\<close>) so a caller can
  override which variables count as global; \<open>analyse_sign\<close> below is the
  convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
    and p :: imp_prog
begin

interpretation p_reg:
  unit_dg_exec_analysis gs
    "sign_tf_for gs" "sign_tf_st_for gs" "sign_enter_st_for gs"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret p_transfer: sound_transfer_for gs "sign_tf_for gs"
    by (rule sign_is_sound_transfer_for)
  show "unit_dg_exec_analysis gs (sign_tf_for gs)
          (sign_tf_st_for gs) (sign_enter_st_for gs)
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule p_transfer.tf_sound_assign_for p_transfer.tf_sound_random_for
             p_transfer.tf_sound_assume_for p_transfer.tf_sound_assume_not_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_for
             sign_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             sign_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF sign_tf_st_for_reduces]
             action_reduces.ret_some[OF sign_tf_st_for_reduces]
             action_reduces.check[OF sign_tf_st_for_reduces]
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

text \<open>
  \<open>p_reg\<close> is local to this context block, so its qualified constants do not
  survive past the closing \<open>end\<close> --- \<open>analyse_sign_gamma_for\<close> names the
  fully-applied locale concretization once, the same way \<open>Sign_DG\<close>'s
  \<open>sign_dg_gamma\<close> names \<open>sound_dg_spec.dg_gamma\<close>, so \<open>analyse_sign_sound\<close> below
  can state its conclusion after the context closes.
\<close>

definition analyse_sign_gamma_for ::
  "(pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_sign_gamma_for = p_reg.gamma"

text \<open>
  The native D/G equation system and its solved result, at an arbitrary
  classifier \<open>gs\<close> and program \<open>p\<close>.  \<open>analyse_sign_eqs_for\<close> and \<open>analyse_sign_for\<close>
  are exactly \<open>dgEx_eqs\<close> and \<open>dgEx_sol\<close> with \<open>gs\<close> and \<open>p\<close> in place of
  \<open>sign_ex_gs\<close> and \<open>sign_ex_prog\<close> --- \<^const>\<open>prog_cfg\<close> plays the role \<open>gEx\<close>
  played there.
\<close>

definition analyse_sign_eqs_for ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "analyse_sign_eqs_for =
     dg_gen_of
       (unit_dg_spec_st_for gs (sign_tf_st_for gs) (sign_enter_st_for gs))
       (prog_cfg prog_main_name p) bot cinit_sign_st cinit_sign_st"

definition analyse_sign_for ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "analyse_sign_for = TD_side_always_join_Interp_solve analyse_sign_eqs_for (cfg_exit (prog_cfg prog_main_name p), ())"

text \<open>
  The connection lemma: soundness for an arbitrary \<open>gs\<close> and \<open>p\<close> reuses
  \<open>unit_dg_exec_analysis.run_source_sound\<close> exactly as \<open>dgEx_source_run_sound\<close>
  does, just with the solver-domain, well-formedness, and coverage facts left
  as hypotheses instead of discharged \<open>by eval\<close> --- symbolic \<open>gs\<close>/\<open>p\<close> cannot be
  run through the executable solver at proof time the way the one hard-coded
  \<open>sign_ex_gs\<close>/\<open>sign_ex_prog\<close> can.  \<open>sound0\<close> stays internal: it never depended
  on the program, only on \<open>cinit_sign_st\<close> and the classifier, exactly as in
  \<open>dgEx_sound0\<close>.
\<close>

theorem analyse_sign_sound_for:
  assumes solve: "TD_side_always_join_Interp_solve_c analyse_sign_eqs_for (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst analyse_sign_for"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst analyse_sign_for"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst analyse_sign_for"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst analyse_sign_for"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and run: "star (pstep gs (prog_table p)) (prog_main p, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores gs"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg prog_main_name p) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> analyse_sign_gamma_for (snd analyse_sign_for) v"
proof -
  have sound0:
    "cinit_stores gs \<subseteq>
       \<lbrakk>fun_of_exec_dg_st_for gs cinit_sign_st \<squnion>
        fun_of_exec_dg_st_for gs cinit_sign_st\<rbrakk>"
    by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for cinit_stores_def
                  gamma_state_def sup.idem)
  show ?thesis
    unfolding analyse_sign_gamma_for_def analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def
    by (rule p_reg.run_source_sound
          [OF solve[unfolded analyse_sign_eqs_for_def prog_cfg_def]
              wf
              cover_entry[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              cover_edge[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              cover_enter[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              cover_combine[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0[folded gamma_unit_def] init run])
qed

end

text \<open>
  Convenience instances at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching the shape
  \<open>gEx\<close>/\<open>dgEx_eqs\<close>/\<open>dgEx_sol\<close> already used for \<open>sign_ex_gs\<close> above.
\<close>

definition analyse_sign_eqs :: "imp_prog \<Rightarrow> pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "analyse_sign_eqs p = analyse_sign_eqs_for (declared_global p) p"

definition analyse_sign :: "imp_prog \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "analyse_sign p = analyse_sign_for (declared_global p) p"

corollary analyse_sign_sound:
  fixes p :: imp_prog
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and run: "star (pstep (declared_global p) (prog_table p)) (prog_main p, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores (declared_global p)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg prog_main_name p) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> analyse_sign_gamma_for (declared_global p) (snd (analyse_sign p)) v"
  unfolding analyse_sign_def analyse_sign_eqs_def
  by (rule analyse_sign_sound_for
        [OF solve[unfolded analyse_sign_def analyse_sign_eqs_def]
            wf
            cover_entry[unfolded analyse_sign_def]
            cover_edge[unfolded analyse_sign_def]
            cover_enter[unfolded analyse_sign_def]
            cover_combine[unfolded analyse_sign_def]
            finI finC run init])

text \<open>
  \<open>gEx\<close>, \<open>dgEx_eqs\<close>, and \<open>dgEx_sol\<close> really are the \<open>gs = sign_ex_gs\<close>,
  \<open>p = sign_ex_prog\<close> instance of the arbitrary-classifier, arbitrary-program
  chain above, not a separate parallel definition.
\<close>

lemma gEx_prog_cfg: "gEx = prog_cfg prog_main_name sign_ex_prog"
  unfolding gEx_def prog_cfg_def sign_ex_pi_def by simp

lemma dgEx_eqs_is_analyse_sign_eqs: "dgEx_eqs = analyse_sign_eqs sign_ex_prog"
  unfolding dgEx_eqs_def analyse_sign_eqs_def analyse_sign_eqs_for_def gEx_prog_cfg by simp

lemma dgEx_sol_is_analyse_sign: "dgEx_sol = analyse_sign sign_ex_prog"
  unfolding dgEx_sol_def analyse_sign_def analyse_sign_for_def dgEx_eqs_is_analyse_sign_eqs
    analyse_sign_eqs_def gEx_prog_cfg by simp

subsection \<open>Executable code generation\<close>

text \<open>
  \<open>dgEx_sol\<close> exports through Isabelle's code generator, not merely through
  \<open>eval\<close>/\<open>value\<close>: this is a stronger guarantee, since the code generator
  demands a complete code equation for every constant on the dependency path
  rather than falling back to the ML interpreter's built-in evaluation of the
  logical constants involved.
\<close>

subsection \<open>A second program through the same entry point\<close>

text \<open>
  \<open>analyse_sign_demo2_prog\<close> is a different program from \<open>sign_ex_prog\<close>, run
  through the very same \<open>analyse_sign\<close>: the entry point above is not
  specialized to one hard-coded example.
\<close>

definition analyse_sign_demo2_prog :: imp_prog where
  "analyse_sign_demo2_prog = program { void main() { a := 1; b := a; c := b } }"

text \<open>
  Same always-join imprecision as \<open>dgEx_inspect\<close> above (every edge joins local
  answers with global side effects): the computed exit value is \<open>STop\<close>, not a
  hand-picked precise witness.  What matters here is that \<open>analyse_sign\<close>
  computes at all on a program it was never specialized to, not the resulting
  precision.
\<close>

lemma analyse_sign_demo2_result:
  "map_option (\<lambda>sol. lookup_resolved_st_q
                        (locals (snd sol (Inl (cfg_exit (prog_cfg prog_main_name analyse_sign_demo2_prog), ()))))
                        (location_of (declared_global analyse_sign_demo2_prog) ''c''))
     (TD_side_always_join_Interp_solve_c (analyse_sign_eqs analyse_sign_demo2_prog)
        (cfg_exit (prog_cfg prog_main_name analyse_sign_demo2_prog), ())) = Some STop"
  by eval

export_code dgEx_sol analyse_sign_for analyse_sign
  in Haskell module_name Sign_Demo file_prefix "Sign_Demo"

export_code dgEx_sol analyse_sign_for analyse_sign
  in OCaml module_name Sign_Demo file_prefix "Sign_Demo_OCaml"

end

