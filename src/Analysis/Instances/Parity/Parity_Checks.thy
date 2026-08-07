theory Parity_Checks
  imports Parity_Numeric_Queries "Voblint_Core.Abstract_Checks" Parity_Exec_Sound
begin

hide_const phase.N

section \<open>Parity instance of the generic check-discharge interface\<close>

text \<open>
  Only composition lives here, exactly as Voblint_Analysis.Sign_Checks
  and Voblint_Analysis.Interval_Checks: the Parity lattice comparison
  tables (\<open>parity_less_true\<close>/\<open>parity_less_false\<close>/\<open>parity_eq_true\<close>/
  \<open>parity_eq_false\<close>) and their
  \<^theory>\<open>Voblint_Analysis.Parity_Numeric_Queries\<close> interpretation of
  \<open>abstract_numeric_queries\<close> live in that theory. The Parity expression
  evaluator \<open>aval_parity\<close> lives in \<^theory>\<open>Voblint_Analysis.Parity_Domain\<close>. The
  Boolean recursion over \<^typ>\<open>bexp\<close>, the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from interpreting
  \<open>abstract_check_domain\<close> (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>) once, below,
  reusing the numeric-query facts already proved sound in
  \<open>parity_numeric_queries\<close> --- no Boolean recursion or classification logic
  is restated.
\<close>

global_interpretation parity_check_domain:
  abstract_check_domain gamma_parity parity_less_true parity_less_false
    parity_eq_true parity_eq_false gamma_state aval_parity
  defines
    parity_check_true = parity_check_domain.check_true
    and parity_check_false = parity_check_domain.check_false
    and parity_classify_check = parity_check_domain.classify_check
    and parity_checks_proven = parity_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: aexp and \<sigma> :: "parity abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then have "\<forall>x. s x \<in> gamma_parity (\<sigma> x)" by simp
  then show "aval e s \<in> gamma_parity (aval_parity e \<sigma>)" using aval_parity_sound by blast
qed

text \<open>
  Only the consumer-facing aliases get a short Parity-prefixed name, matching
  Voblint_Analysis.Sign_Checks naming convention:
  \<open>classify_check\<close>'s two directions and the \<open>checks_proven\<close> bridge, both
  exercised below and by the worked check-discharge example. The lower-level
  facts \<open>classify_check\<close>'s own soundness is built from stay reachable under
  the qualified \<open>parity_check_domain.\<close> name.
\<close>

lemmas parity_classify_check_proved = parity_check_domain.classify_check_proved
lemmas parity_classify_check_refuted = parity_check_domain.classify_check_refuted
lemmas parity_checks_provenI = parity_check_domain.abstract_checks_provenI
lemmas parity_checks_proven_sound = parity_check_domain.abstract_checks_proven_sound

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>PTop\<close>) environment, so each test exercises exactly the comparison it
  names.\<close>

definition test_env_eo :: "parity abs_state" where
  "test_env_eo = (\<lambda>_. PTop)(''x'' := PEven, ''y'' := POdd)"

text \<open>Disjoint parity classes: the direct equality is refuted, and its
  negation is proved --- going through \<open>check_false\<close> on the un-negated
  equality, not a one-sided negation of \<open>check_true\<close>.\<close>

lemma parity_classify_eq_refuted:
  "parity_classify_check (Eq (V ''x'') (V ''y'')) test_env_eo = Check_Refuted"
  unfolding test_env_eo_def by eval

lemma parity_classify_not_eq_proved:
  "parity_classify_check (Not (Eq (V ''x'') (V ''y''))) test_env_eo = Check_Proved"
  unfolding test_env_eo_def by eval

text \<open>Same abstract value on both sides: \<open>x\<close> is \<open>PEven\<close> and the literal \<open>4\<close>
  is also \<open>PEven\<close>, but Parity has no singleton representation, so the
  equality stays unknown rather than falsely proved.\<close>

lemma parity_classify_eq_unknown:
  "parity_classify_check (Eq (V ''x'') (N 4)) test_env_eo = Check_Unknown"
  unfolding test_env_eo_def by eval

text \<open>Nested \<open>Or\<close>: proved through the negated-equality branch alone.\<close>

definition test_env_nested_proved :: "parity abs_state" where
  "test_env_nested_proved = (\<lambda>_. PTop)(''x'' := PEven, ''y'' := POdd)"

lemma parity_classify_nested_proved:
  "parity_classify_check
     (Or (Not (Eq (V ''x'') (V ''y''))) (Eq (V ''z'') (N 1)))
     test_env_nested_proved = Check_Proved"
  unfolding test_env_nested_proved_def by eval

text \<open>Nested \<open>Or\<close>, unknown: neither branch resolves when both sides share a
  parity class.\<close>

definition test_env_nested_unknown :: "parity abs_state" where
  "test_env_nested_unknown = (\<lambda>_. PTop)(''x'' := PEven, ''y'' := PEven)"

lemma parity_classify_nested_unknown:
  "parity_classify_check
     (Or (Not (Eq (V ''x'') (V ''y''))) (Eq (V ''z'') (N 1)))
     test_env_nested_unknown = Check_Unknown"
  unfolding test_env_nested_unknown_def by eval

subsection \<open>Whole-program check report\<close>

text \<open>Thin composition, mirroring \<open>sign_check_report\<close>/\<open>interval_check_report\<close>:
  \<^const>\<open>classify_checks\<close> owns the traversal and ordering,
  \<^const>\<open>parity_exec_prog_at\<close> owns the node-indexed Parity environment, and
  \<open>parity_classify_check\<close> owns the per-check classification.\<close>

definition parity_check_report ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "parity_check_report gs mnm p =
     classify_checks (prog_cfg mnm p) (parity_exec_prog_at gs mnm p) parity_classify_check"

end
