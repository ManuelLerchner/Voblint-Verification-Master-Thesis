theory Sign_Checks
  imports Sign_Numeric_Queries "Voblint_Core.Abstract_Checks" Sign_Exec_Sound
begin

hide_const phase.N

section \<open>Sign instance of the generic check-discharge interface\<close>

text \<open>
  Only composition lives here: the Sign lattice comparison tables
  (\<open>sign_less_true\<close>/\<open>sign_less_false\<close>/\<open>sign_eq_true\<close>/\<open>sign_eq_false\<close>) and their
  \<^theory>\<open>Voblint_Analysis.Sign_Numeric_Queries\<close> interpretation of
  \<open>abstract_numeric_queries\<close> live in that theory. The Sign expression
  evaluator \<open>aval_sign\<close> lives in \<^theory>\<open>Voblint_Analysis.Sign_Arithmetic\<close>. The
  Boolean recursion over \<^typ>\<open>bexp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way
  classification, and the node-indexed bridge to \<^const>\<open>checks_proven\<close> come
  from interpreting \<open>abstract_check_domain\<close> (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>)
  once, below, reusing the numeric-query facts already proved sound in
  \<open>sign_numeric_queries\<close> rather than re-deriving the comparison tables ---
  the same way \<open>sign_backward_domain\<close> in \<open>Sign_Backward.thy\<close> interprets
  \<open>backward_domain\<close> for guard narrowing.
\<close>

global_interpretation sign_check_domain:
  abstract_check_domain gamma_sign sign_less_true sign_less_false sign_eq_true sign_eq_false
    gamma_state aval_sign
  defines
    sign_check_true = sign_check_domain.check_true
    and sign_check_false = sign_check_domain.check_false
    and sign_classify_check = sign_check_domain.classify_check
    and sign_checks_proven = sign_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: aexp and \<sigma> :: "sign abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then have "\<forall>x. s x \<in> gamma_sign (\<sigma> x)" by simp
  then show "aval e s \<in> gamma_sign (aval_sign e \<sigma>)" using aval_sign_sound by blast
qed

text \<open>
  Only the consumer-facing aliases get a short Sign-prefixed name:
  \<open>classify_check\<close>'s two directions and the \<open>checks_proven\<close> bridge, both
  exercised below and by \<open>Example_Checks_Store_Only\<close>.
  \<open>sign_check_domain.check_true_sound\<close>/\<open>check_false_sound\<close>/
  \<open>check_true_false_vacuous\<close> are the lower-level facts \<open>classify_check\<close>'s
  own soundness is built from; no caller needs them directly, so they stay
  reachable under the qualified \<open>sign_check_domain.\<close> name instead of a
  dedicated alias here.
\<close>

lemmas sign_classify_check_proved = sign_check_domain.classify_check_proved
lemmas sign_classify_check_refuted = sign_check_domain.classify_check_refuted
lemmas sign_checks_provenI = sign_check_domain.abstract_checks_provenI
lemmas sign_checks_proven_sound = sign_check_domain.abstract_checks_proven_sound

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>STop\<close>) environment, so each test exercises exactly the comparison it names.\<close>

definition test_env_pos :: "sign abs_state" where
  "test_env_pos = (\<lambda>_. STop)((STR ''x'') := SPos)"

lemma sign_classify_less_proved:
  "sign_classify_check (Less (N 0) (V (STR ''x''))) test_env_pos = Check_Proved"
  unfolding test_env_pos_def by eval

lemma sign_classify_less_refuted:
  "sign_classify_check (Less (V (STR ''x'')) (N 0)) test_env_pos = Check_Refuted"
  unfolding test_env_pos_def by eval

lemma sign_classify_eq_unknown:
  "sign_classify_check (Eq (V (STR ''x'')) (N 1)) test_env_pos = Check_Unknown"
  unfolding test_env_pos_def by eval

text \<open>Negation: \<open>!(x < 0)\<close> is provable under \<open>SNonNeg\<close>, going through
  \<open>check_false\<close> on the un-negated \<open>x < 0\<close> rather than a one-sided
  negation of \<open>check_true\<close>.\<close>

definition test_env_nonneg :: "sign abs_state" where
  "test_env_nonneg = (\<lambda>_. STop)((STR ''x'') := SNonNeg)"

lemma sign_classify_not_proved:
  "sign_classify_check (Not (Less (V (STR ''x'')) (N 0))) test_env_nonneg = Check_Proved"
  unfolding test_env_nonneg_def by eval

text \<open>Nested \<open>And\<close>/\<open>Or\<close>: proved through the \<open>And\<close> branch alone, and unknown
  when neither branch resolves.\<close>

definition test_env_nested_proved :: "sign abs_state" where
  "test_env_nested_proved = (\<lambda>_. STop)((STR ''x'') := SPos, (STR ''y'') := SPos)"

lemma sign_classify_nested_proved:
  "sign_classify_check
     (Or (And (Less (N 0) (V (STR ''x''))) (Less (N 0) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_proved = Check_Proved"
  unfolding test_env_nested_proved_def by eval

definition test_env_nested_unknown :: "sign abs_state" where
  "test_env_nested_unknown = (\<lambda>_. STop)((STR ''x'') := SNonNeg, (STR ''y'') := SPos)"

lemma sign_classify_nested_unknown:
  "sign_classify_check
     (Or (And (Less (N 0) (V (STR ''x''))) (Less (N 0) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_unknown = Check_Unknown"
  unfolding test_env_nested_unknown_def by eval

subsection \<open>Whole-program check report\<close>

text \<open>
  Thin composition, not a restatement: \<^const>\<open>classify_checks\<close> already owns
  the executable traversal and ordering, \<^const>\<open>sign_exec_prog_at\<close> already
  owns the node-indexed Sign environment, and \<open>sign_classify_check\<close> above
  already owns the per-check classification. This wrapper only feeds a
  compiled program's own three projections through them, the same way
  \<^const>\<open>sign_exec_prog\<close> feeds them through \<^const>\<open>sign_exec_at\<close>.
\<close>

definition sign_check_report ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "sign_check_report gs mnm p =
     classify_checks (prog_cfg mnm p) (sign_exec_prog_at gs mnm p) sign_classify_check"

subsection \<open>Whole-program check report: the native D/G runtime API\<close>

text \<open>
  \<open>analyse_sign_report_for\<close> mirrors \<open>sign_check_report\<close> exactly, reading through
  \<^const>\<open>analyse_sign_env_for\<close> (the native D/G pipeline \<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close>
  computes) instead of \<^const>\<open>sign_exec_prog_at\<close> (the older \<open>side_cfg_T_eff_st\<close> pipeline) ---
  this is the report function the exported \<open>analyse\<close> API actually dispatches to (see
  \<open>Example_Analysis_Dispatch\<close>, downstream in Examples), fixed at \<open>prog_main_name\<close> rather than
  an arbitrary \<open>mnm\<close> since \<open>analyse_sign_env_for\<close> already is.
\<close>

definition analyse_sign_report_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report_for gs p =
     classify_checks (prog_cfg prog_main_name p) (analyse_sign_env_for gs p) sign_classify_check"

text \<open>
  The definitional equation above unfolds \<^const>\<open>analyse_sign_env_for\<close> at every check node, and
  that unfolding mentions \<^const>\<open>analyse_sign_for\<close> twice (once for \<open>locals\<close>, once for \<open>globs\<close>)
  --- so naive code generation from it would re-run the whole D/G solver twice per check, for an
  \<open>N\<close>-check program, \<open>2N\<close> solver runs instead of one. The \<open>[code]\<close> equation below is provably
  equal (a direct \<open>Let\<close>-unfold of the same definitions) but binds \<^term>\<open>snd (analyse_sign_for gs
  p)\<close> once, outside the per-check closure \<^const>\<open>classify_checks\<close> applies; the target language
  compiles that \<open>let\<close> to a single shared thunk, so the generated Haskell/OCaml computes the
  solved system exactly once per report, regardless of how many checks the program has.
\<close>

declare analyse_sign_report_for_def [code del]

lemma analyse_sign_report_for_code [code]:
  "analyse_sign_report_for gs p =
     (let sol = snd (analyse_sign_for gs p)
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. fun_of_exec_dg_st_for gs (locals (sol (Inl (v, ()))))
                \<squnion> fun_of_exec_dg_st_for gs (globs (sol (Inr ()))))
           sign_classify_check)"
  unfolding analyse_sign_report_for_def analyse_sign_env_for_def[abs_def] Let_def
  by (rule refl)

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching \<^const>\<open>analyse_sign\<close>'s shape.
\<close>

definition analyse_sign_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report p = analyse_sign_report_for (declared_global p) p"

subsection \<open>Whole-program check report with state\<close>

text \<open>
  State-carrying sibling of \<open>analyse_sign_report_for\<close>/\<open>analyse_sign_report\<close>,
  via \<^const>\<open>classify_checks_with_state\<close>: same D/G pipeline, same environment,
  with the per-check Sign environment attached to each report entry instead
  of discarded. The \<open>[code]\<close> rewrite mirrors the one above for the same
  reason: naive definitional unfolding would re-run the solver twice per
  check.
\<close>

definition analyse_sign_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> bexp \<times> check_result \<times> (vname \<Rightarrow> sign)) list" where
  "analyse_sign_report_for_with_state gs p =
     classify_checks_with_state (prog_cfg prog_main_name p) (analyse_sign_env_for gs p)
       sign_classify_check"

declare analyse_sign_report_for_with_state_def [code del]

lemma analyse_sign_report_for_with_state_code [code]:
  "analyse_sign_report_for_with_state gs p =
     (let sol = snd (analyse_sign_for gs p)
      in classify_checks_with_state (prog_cfg prog_main_name p)
           (\<lambda>v. fun_of_exec_dg_st_for gs (locals (sol (Inl (v, ()))))
                \<squnion> fun_of_exec_dg_st_for gs (globs (sol (Inr ()))))
           sign_classify_check)"
  unfolding analyse_sign_report_for_with_state_def analyse_sign_env_for_def[abs_def] Let_def
  by (rule refl)

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_sign_report\<close>'s shape.\<close>

definition analyse_sign_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> bexp \<times> check_result \<times> (vname \<Rightarrow> sign)) list" where
  "analyse_sign_report_with_state p = analyse_sign_report_for_with_state (declared_global p) p"

end

