theory Int_Checks
  imports Int_Exec_Sound "Voblint_Core.Abstract_Checks"
    "Voblint_Core.Analysis_Result"
begin

hide_const phase.N

section \<open>Int instance of the generic check-discharge interface\<close>

text \<open>
  \<open>int_dom\<close> already carries a \<open>sound_domain\<close> instance (\<^theory>\<open>Voblint_Analysis.Int_Domain\<close>) and
  three \<^locale>\<open>backward_domain\<close> interpretations, one per refinement mode
  (\<^theory>\<open>Voblint_Analysis.Int_Backward\<close>). Unlike Sign and Interval, which each hand-roll their own
  sharper \<open>less_true\<close>/\<open>less_false\<close>/\<open>eq_true\<close>/\<open>eq_false\<close> comparison tables
  (\<open>Sign_Numeric_Queries\<close>, \<open>Interval_Numeric_Queries\<close>), \<open>int_dom\<close> reuses the generic derivation
  \<^theory>\<open>Voblint_Core.Abstract_Numeric_Queries\<close> already proves for free off any
  \<^locale>\<open>backward_domain\<close> instance: \<open>int_dom_backward_fixpoint.less_true\<close>/\<open>less_false\<close> come from
  \<open>inv_less_int_dom_fixpoint\<close> via \<^locale>\<open>derived_less_queries\<close>, and
  \<open>int_dom_backward_fixpoint.eq_true\<close>/\<open>eq_false\<close> come from \<open>less_false\<close>/
  \<open>intersect_int_dom_fixpoint\<close> via \<^locale>\<open>derived_eq_true_from_less\<close>/
  \<^locale>\<open>derived_eq_false_from_intersection\<close>.

  \<open>int_less_true\<close>/\<open>int_less_false\<close>/\<open>int_eq_true\<close>/\<open>int_eq_false\<close> below restate those same four
  formulas as plain top-level \<open>definition\<close>s rather than citing the locale-derived constants
  directly: a \<open>definition\<close> gets a \<open>[code]\<close> equation automatically, while a constant introduced
  through \<^locale>\<open>backward_domain\<close>'s sublocale chain (parameterised over an abstract \<open>inv_less\<close>)
  does not, so \<open>int_classify_check\<close> could not code-generate through the CLI directly against
  \<open>int_dom_backward_fixpoint.less_true\<close> \<open>et al.\<close>. Soundness for the four restated definitions is
  not re-derived: each is definitionally the exact same formula as its locale-derived
  counterpart (\<open>int_less_true_eq\<close> \<open>et al.\<close> below), so \<open>int_dom_backward_fixpoint.less_true_sound\<close>
  \<open>et al.\<close> transports over in one line. A sharper, hand-tuned composite table (reduced through
  all four components at once rather than \<open>int_ivl\<close>'s own \<open>inv_less\<close>/\<open>intersect\<close> alone) is
  future precision work, not required for this report route to be sound.
\<close>

definition int_less_true :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_less_true a b =
     (fst (inv_less_int_dom Refine_Fixpoint False a b) = bot \<or> snd (inv_less_int_dom Refine_Fixpoint False a b) = bot)"

definition int_less_false :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_less_false a b =
     (fst (inv_less_int_dom Refine_Fixpoint True a b) = bot \<or> snd (inv_less_int_dom Refine_Fixpoint True a b) = bot)"

definition int_eq_true :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_eq_true a b = (int_less_false a b \<and> int_less_false b a)"

definition int_eq_false :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_eq_false a b = (intersect_int_dom_mode Refine_Fixpoint a b = bot)"

lemma int_less_true_eq: "int_less_true a b = int_dom_backward_fixpoint.less_true a b"
  unfolding int_less_true_def int_dom_backward_fixpoint.less_true_def by (rule refl)

lemma int_less_false_eq: "int_less_false a b = int_dom_backward_fixpoint.less_false a b"
  unfolding int_less_false_def int_dom_backward_fixpoint.less_false_def by (rule refl)

lemma int_eq_true_eq: "int_eq_true a b = int_dom_backward_fixpoint.eq_true a b"
  unfolding int_eq_true_def int_less_false_eq int_dom_backward_fixpoint.eq_true_def by (rule refl)

lemma int_eq_false_eq: "int_eq_false a b = int_dom_backward_fixpoint.eq_false a b"
  unfolding int_eq_false_def int_dom_backward_fixpoint.eq_false_def by (rule refl)

lemma int_less_true_sound:
  assumes "int_less_true a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "i < j"
  using assms unfolding int_less_true_eq by (rule int_dom_backward_fixpoint.less_true_sound)

lemma int_less_false_sound:
  assumes "int_less_false a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "\<not> i < j"
  using assms unfolding int_less_false_eq by (rule int_dom_backward_fixpoint.less_false_sound)

lemma int_eq_true_sound:
  assumes "int_eq_true a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "i = j"
  using assms unfolding int_eq_true_eq by (rule int_dom_backward_fixpoint.eq_true_sound)

lemma int_eq_false_sound:
  assumes "int_eq_false a b" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "i \<noteq> j"
  using assms unfolding int_eq_false_eq by (rule int_dom_backward_fixpoint.eq_false_sound)

global_interpretation int_dom_numeric_queries:
  abstract_numeric_queries gamma int_less_true int_less_false int_eq_true int_eq_false
  by unfold_locales
    (auto simp add: int_less_true_sound int_less_false_sound int_eq_true_sound int_eq_false_sound)

global_interpretation int_check_domain:
  abstract_check_domain gamma int_less_true int_less_false int_eq_true int_eq_false
    gamma_state aval_int_dom_fixpoint
  defines
    int_check_true = int_check_domain.check_true
    and int_check_false = int_check_domain.check_false
    and int_classify_check = int_check_domain.classify_check
    and int_checks_proven = int_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: exp and \<sigma> :: "int_dom abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then show "aval e s \<in> gamma (aval_int_dom_fixpoint e \<sigma>)" using aval_int_dom_sound by simp
qed

text \<open>
  Only the consumer-facing aliases get a short Int-prefixed name, the same choice
  \<open>Sign_Checks\<close>/\<open>Interval_Checks\<close> make: \<open>classify_check\<close>'s
  two directions and the \<open>checks_proven\<close> bridge. The lower-level
  \<open>check_true_sound\<close>/\<open>check_false_sound\<close>/\<open>check_true_false_vacuous\<close> facts \<open>classify_check\<close>'s own
  soundness is built from stay reachable under the qualified \<open>int_check_domain.\<close> name instead of
  a dedicated alias here.
\<close>



text \<open>
  Only the consumer-facing aliases get a short Int-prefixed name, the same choice
  \<open>Sign_Checks\<close>/\<open>Interval_Checks\<close> make: \<open>classify_check\<close>'s
  two directions and the \<open>checks_proven\<close> bridge. The lower-level
  \<open>check_true_sound\<close>/\<open>check_false_sound\<close>/\<open>check_true_false_vacuous\<close> facts \<open>classify_check\<close>'s own
  soundness is built from stay reachable under the qualified \<open>int_check_domain.\<close> name instead of
  a dedicated alias here.
\<close>

lemmas int_classify_check_proved = int_check_domain.classify_check_proved
lemmas int_classify_check_refuted = int_check_domain.classify_check_refuted
lemmas int_checks_provenI = int_check_domain.abstract_checks_provenI
lemmas int_checks_proven_sound = int_check_domain.abstract_checks_proven_sound

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained (\<open>top\<close>) environment.
  \<open>y\<close>'s exact singleton after the composite backward filter in \<open>Int_Exec_Sound\<close>'s worked example
  (\<open>Exec_Int_DG_Run.dgExI_fixpoint_inspect_y_at_Statement_1\<close>) already exercises the precision the
  refined product buys over any one component alone; the tests below exercise the report layer
  itself on a directly-built environment.\<close>

definition test_env_int_bounded :: "int_dom abs_state" where
  "test_env_int_bounded = (\<lambda>_. top)((STR ''x'') := int_dom_sipc SPos (Ivl (Fin 4) (Fin 7)) PTop top)"

lemma int_classify_less_proved:
  "int_classify_check (Less (V (STR ''x'')) (N 11)) test_env_int_bounded = Check_Proved"
  unfolding test_env_int_bounded_def by eval

lemma int_classify_less_refuted:
  "int_classify_check (Less (V (STR ''x'')) (N 0)) test_env_int_bounded = Check_Refuted"
  unfolding test_env_int_bounded_def by eval

lemma int_classify_eq_unknown:
  "int_classify_check (Eq (V (STR ''x'')) (N 5)) test_env_int_bounded = Check_Unknown"
  unfolding test_env_int_bounded_def by eval

subsection \<open>Whole-program check report: the native D/G runtime API\<close>

text \<open>
  \<open>analyse_int_report_for\<close> mirrors \<open>analyse_interval_td_report_for\<close> exactly, reading
  through \<^const>\<open>analyse_int_dg_env_for\<close> (the \<open>Refine_Fixpoint\<close>, warrowing-backed native D/G
  pipeline, \<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>) instead of \<open>ivl_exec_prog_at\<close> --- this is
  the report function the exported \<open>analyse\<close> API dispatches to for \<open>Int_Analysis\<close> (see
  \<open>Analyse_Dispatch\<close>, Examples session, downstream), fixed at \<open>prog_main_name\<close> since
  \<^const>\<open>analyse_int_dg_env_for\<close> already is, mirroring
  \<open>analyse_sign_report_for\<close>/\<open>analyse_interval_td_report_for\<close>.
\<close>

definition analyse_int_report_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_for mode gs p =
     classify_checks (prog_cfg prog_main_name p)
       (analyse_int_dg_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
       int_classify_check"

text \<open>
  Same single-solve-per-report fix as \<open>analyse_interval_td_report_for_code\<close>: bind
  \<^term>\<open>snd (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)\<close> once,
  outside \<^const>\<open>classify_checks\<close>'s per-check closure, so the generated OCaml solves the D/G
  equation system exactly once per report rather than once per check.
\<close>

declare analyse_int_report_for_def [code del]

lemma analyse_int_report_for_code [code]:
  "analyse_int_report_for mode gs p =
     (let sol = snd (analyse_int_dg_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
                of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)
           int_classify_check)"
  unfolding analyse_int_report_for_def analyse_int_dg_env_for_def[abs_def] Let_def
  by (rule refl)

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<open>analyse_interval_td_report\<close>'s
  shape. Soundness (\<open>analyse_int_report_sound_proved\<close>/\<open>_refuted\<close>) needs the
  \<open>base_dg_exec_analysis\<close> locale interpretation, one session later than Analysis in the locked
  six-session chain, so it stays downstream in a new \<open>Example_Int_Codegen\<close> (Examples), mirroring
  \<open>Sign_Checks\<close>/\<open>Interval_Checks\<close>.
\<close>

definition analyse_int_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report p = analyse_int_report_for Refine_Fixpoint (declared_global p) p"

subsection \<open>Whole-program check report with state: the native D/G runtime API\<close>

text \<open>
  State-carrying sibling of \<open>analyse_int_report_for\<close>/\<open>analyse_int_report\<close>, via
  \<^const>\<open>classify_checks_with_state\<close>: same native D/G pipeline, same environment, with the
  per-check \<open>int_dom\<close> environment attached to each report entry instead of discarded ---
  mirrors \<open>analyse_interval_td_report_for_with_state\<close>/\<open>analyse_interval_td_report_with_state\<close>,
  needed so \<open>Analyse_Dispatch.analyse_with_state\<close> can stay total once \<open>Int_Analysis\<close> joins
  \<open>analysis_kind\<close>. The \<open>[code]\<close> rewrite mirrors the one above for the same
  single-solve-per-report reason.
\<close>

text \<open>
  Each entry also carries an exact \<open>unreachable\<close> flag,
  \<^const>\<open>resolved_st_q_lifted_is_bot_for\<close> read off the very same local unknown
  \<^const>\<open>analyse_int_dg_env_for\<close> collapses to \<^term>\<open>bot\<close> -- see
  \<open>analyse_sign_report_for_with_state\<close>'s Sign counterpart for the argument
  (solver-level \<open>Bot\<close> and a componentwise-bottom \<open>Lifted\<close> state both set it)
  and \<^theory>\<open>Voblint_Core.Exec_St\<close>'s \<open>resolved_st_q_lifted_is_bot_for_iff\<close> for
  the exactness.
\<close>

definition analyse_int_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> int_dom abs_state) list" where
  "analyse_int_report_for_with_state gs p =
     classify_checks_with_state (prog_cfg prog_main_name p)
       (\<lambda>v. (resolved_st_q_lifted_is_bot_for (declared_global_vars p)
               (locals (snd (analyse_int_dg_for Refine_Fixpoint (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
                          (Inl (v, ())))),
             analyse_int_dg_env_for Refine_Fixpoint (resolved_st_q_is_bot_for (declared_global_vars p)) gs p v))
       (\<lambda>c (_, s). int_classify_check c s)"

declare analyse_int_report_for_with_state_def [code del]

lemma analyse_int_report_for_with_state_code [code]:
  "analyse_int_report_for_with_state gs p =
     (let sol = snd (analyse_int_dg_for Refine_Fixpoint (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
      in classify_checks_with_state (prog_cfg prog_main_name p)
           (\<lambda>v. let st = locals (sol (Inl (v, ())))
                in (resolved_st_q_lifted_is_bot_for (declared_global_vars p) st,
                    case map_lift (fun_of_exec_dg_st_for gs) st of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s))
           (\<lambda>c (_, s). int_classify_check c s))"
  unfolding analyse_int_report_for_with_state_def analyse_int_dg_env_for_def[abs_def] Let_def
  by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_int_report\<close>'s shape.\<close>

definition analyse_int_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> int_dom abs_state) list" where
  "analyse_int_report_with_state p = analyse_int_report_for_with_state (declared_global p) p"

subsection \<open>Solver-choice variants: always-join and per-origin update rules\<close>

text \<open>
  \<open>analyse_int_report_join_for\<close> mirrors \<open>analyse_int_report_for\<close> exactly, reading through
  \<^const>\<open>analyse_int_dg_join_env_for\<close> (the always-join update rule,
  \<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>) instead of \<^const>\<open>analyse_int_dg_env_for\<close>
  (Apinis warrowing) --- this is the report function the exported \<open>analyse_with_solver\<close> API
  dispatches to for \<open>Int_Analysis\<close>/\<open>Solver_Join\<close> (\<open>Analyse_Dispatch\<close>, downstream in Examples),
  not \<open>Int_Analysis\<close>'s production default (\<open>analyse\<close>/\<open>analyse_with_solver Int_Analysis
  Solver_Warrow\<close> both still dispatch to \<open>analyse_int_report\<close>). Reuses
  \<^const>\<open>analyse_int_dg_eqs_for\<close> unchanged (\<open>mode\<close> included), only the solve call differs,
  mirroring \<open>Interval_Checks.analyse_interval_report_for\<close>/\<open>Sign_Checks.analyse_sign_report_for\<close>'s
  own always-join default.
\<close>

definition analyse_int_report_join_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_join_for mode gs p =
     classify_checks (prog_cfg prog_main_name p)
       (analyse_int_dg_join_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
       int_classify_check"

declare analyse_int_report_join_for_def [code del]

lemma analyse_int_report_join_for_code [code]:
  "analyse_int_report_join_for mode gs p =
     (let sol = snd (analyse_int_dg_join_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
                of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)
           int_classify_check)"
  unfolding analyse_int_report_join_for_def analyse_int_dg_join_env_for_def[abs_def] Let_def
  by (rule refl)

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, pinned at \<open>Refine_Fixpoint\<close> like
  \<^const>\<open>analyse_int_report\<close>: this is the report the CLI's solver-choice axis reaches, and
  the CLI does not yet expose refinement mode as a separate axis (that remains
  \<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>'s own production default).
\<close>

definition analyse_int_report_join :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_join p = analyse_int_report_join_for Refine_Fixpoint (declared_global p) p"

text \<open>
  \<open>analyse_int_report_per_origin_for\<close> mirrors \<open>analyse_int_report_join_for\<close> exactly, reading
  through \<^const>\<open>analyse_int_dg_per_origin_env_for\<close> instead of
  \<^const>\<open>analyse_int_dg_join_env_for\<close> --- keeping each write origin's contribution separate
  instead of folding every contribution into one join. Reuses \<^const>\<open>analyse_int_dg_eqs_for\<close>
  unchanged, only the solve call differs.
\<close>

definition analyse_int_report_per_origin_for :: "refine_mode \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_per_origin_for mode gs p =
     classify_checks (prog_cfg prog_main_name p)
       (analyse_int_dg_per_origin_env_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
       int_classify_check"

declare analyse_int_report_per_origin_for_def [code del]

lemma analyse_int_report_per_origin_for_code [code]:
  "analyse_int_report_per_origin_for mode gs p =
     (let sol = snd (analyse_int_dg_per_origin_for mode (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. case map_lift (fun_of_exec_dg_st_for gs) (locals (sol (Inl (v, ()))))
                of Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)
           int_classify_check)"
  unfolding analyse_int_report_per_origin_for_def analyse_int_dg_per_origin_env_for_def[abs_def] Let_def
  by (rule refl)

definition analyse_int_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_int_report_per_origin p =
     analyse_int_report_per_origin_for Refine_Fixpoint (declared_global p) p"

subsection \<open>Solved-result table\<close>

text \<open>
  The same solved D/G system as \<^const>\<open>analyse_int_report_for_with_state\<close>,
  read as a \<^typ>\<open>(unit, int_dom abs_state) analysis_result\<close> instead of as a
  check report, mirroring \<open>Interval_Checks\<close>'s own
  \<open>analyse_interval_td_result_for\<close>: the covered local keys the solver already
  returns as the first component, and \<^const>\<open>normalize_point\<close> applied to
  each local unknown. Monovariant, so the context type is \<^typ>\<open>unit\<close>; only
  \<open>Inl\<close>-shaped local keys are covered, never the solver's own \<open>Inr\<close> global
  unknown. Pinned at \<^const>\<open>Refine_Fixpoint\<close> like
  \<^const>\<open>analyse_int_report_for_with_state\<close>, the production refinement mode.

  The \<open>[code]\<close> rewrite is the same single-solve fix as
  \<open>analyse_int_report_for_code\<close>: binding \<open>sol\<close> once outside the per-key
  closure compiles to a single shared thunk, so a lookup never re-solves.
\<close>

definition analyse_int_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_result_for gs p =
     Analysis_Result
       (fst (analyse_int_dg_for Refine_Fixpoint
               (resolved_st_q_is_bot_for (declared_global_vars p)) gs p))
       (\<lambda>v ctx. normalize_point (declared_global_vars p) gs
                  (locals (snd (analyse_int_dg_for Refine_Fixpoint
                                  (resolved_st_q_is_bot_for (declared_global_vars p)) gs p)
                             (Inl (v, ctx)))))"

declare analyse_int_result_for_def [code del]

lemma analyse_int_result_for_code [code]:
  "analyse_int_result_for gs p =
     (let sol = analyse_int_dg_for Refine_Fixpoint
                  (resolved_st_q_is_bot_for (declared_global_vars p)) gs p
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point (declared_global_vars p) gs
                      (locals (snd sol (Inl (v, ctx))))))"
  unfolding analyse_int_result_for_def Let_def by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_int_report\<close>'s shape.\<close>

definition analyse_int_result ::
    "imp_prog \<Rightarrow> (unit, int_dom abs_state) analysis_result" where
  "analyse_int_result p = analyse_int_result_for (declared_global p) p"

end
