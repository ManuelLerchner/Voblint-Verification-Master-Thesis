theory Interval_Classify
  imports Interval_Numeric_Queries Interval_Backward "Voblint_Core.Abstract_Checks"
    "Voblint_Core.Analysis_Result" Interval_Exec_Sound
    "Voblint_Core.Monovariant_Analysis_Result"
begin

hide_const phase.N

section \<open>Interval instance of the generic check-discharge interface\<close>

text \<open>
  Only composition lives here, mirroring \<open>Sign_Checks\<close>: the Interval bound
  tables (\<open>interval_less_true\<close>/\<open>interval_less_false\<close>/\<open>interval_eq_true\<close>/
  \<open>interval_eq_false\<close>) and their \<open>Interval_Numeric_Queries\<close> interpretation of
  \<open>abstract_numeric_queries\<close> live in that theory. The Interval expression
  evaluator \<open>aval_ivl\<close> lives in \<open>Interval_Backward\<close>. The Boolean recursion over
  \<^typ>\<open>exp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from interpreting
  \<open>abstract_check_domain\<close> once, below, reusing the numeric-query facts
  already proved sound in \<open>interval_numeric_queries\<close> rather than re-deriving
  the comparison tables --- the same way \<open>ivl_backward_domain\<close> in
  \<open>Interval_Backward.thy\<close> interprets \<open>backward_domain\<close> for guard narrowing.

  Split out of \<open>Interval_Checks\<close> as its own theory: the routed-spine
  producer (\<open>Interval_Ctx_None_Routed_Sound\<close>) interprets the generic report
  adapter locale and needs \<open>interval_classify_check\<close>'s soundness directions
  for its \<open>ClProved\<close>/\<open>ClRefuted\<close> obligations, while \<open>Interval_Checks\<close>'s own
  solved-result tables read that producer's routed output -- so this
  classify machinery has to sit below both, not inside either.
\<close>

global_interpretation interval_check_domain:
  abstract_check_domain gamma_ivl interval_less_true interval_less_false interval_eq_true
    interval_eq_false gamma_state aval_ivl
  defines
    interval_check_true = interval_check_domain.check_true
    and interval_check_false = interval_check_domain.check_false
    and interval_classify_check = interval_check_domain.classify_check
    and interval_checks_proven = interval_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: exp and \<sigma> :: "ivl abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then have "\<forall>x. s x \<in> gamma_ivl (\<sigma> x)" by simp
  then show "aval e s \<in> gamma_ivl (aval_ivl e \<sigma>)" using aval_ivl_sound by blast
qed

text \<open>
  Only the consumer-facing aliases get a short Interval-prefixed name, the
  same choice \<open>Sign_Checks\<close> makes: \<open>classify_check\<close>'s two directions and the
  \<open>checks_proven\<close> bridge, both exercised by the worked example. The lower-
  level \<open>check_true_sound\<close>/\<open>check_false_sound\<close>/\<open>check_true_false_vacuous\<close>
  facts \<open>classify_check\<close>'s own soundness is built from stay reachable under
  the qualified \<open>interval_check_domain.\<close> name instead of a dedicated alias
  here.
\<close>

lemmas interval_classify_check_proved = interval_check_domain.classify_check_proved
lemmas interval_classify_check_refuted = interval_check_domain.classify_check_refuted
lemmas interval_checks_provenI = interval_check_domain.abstract_checks_provenI
lemmas interval_checks_proven_sound = interval_check_domain.abstract_checks_proven_sound

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>ivl_top\<close>) environment, so each test exercises exactly the comparison it
  names, and one showing the precision gain over Sign: a bounded range proves
  both a wider upper bound and a tighter lower bound in one classification,
  which Sign's four-value lattice cannot distinguish from \<open>STop\<close>.\<close>

definition test_env_bounded :: "ivl abs_state" where
  "test_env_bounded = (\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 4) (Fin 7))"

lemma interval_classify_less_proved:
  "interval_classify_check (Less (V (STR ''x'')) (N 11)) test_env_bounded = Check_Proved"
  unfolding test_env_bounded_def by eval

lemma interval_classify_less_refuted:
  "interval_classify_check (Less (V (STR ''x'')) (N 0)) test_env_bounded = Check_Refuted"
  unfolding test_env_bounded_def by eval

lemma interval_classify_eq_unknown:
  "interval_classify_check (Eq (V (STR ''x'')) (N 5)) test_env_bounded = Check_Unknown"
  unfolding test_env_bounded_def by eval

text \<open>The precision gain over Sign: \<open>0 < x\<close> and \<open>x < 8\<close> both hold outright
  once \<open>x\<close> is known to lie strictly between \<open>3\<close> and \<open>8\<close> --- a fact only a
  domain that tracks numeric bounds can prove; Sign's \<open>SPos\<close>/\<open>SNonNeg\<close> would
  classify \<open>x < 8\<close> \<^term>\<open>Check_Unknown\<close> on the same information.\<close>

definition test_env_precision :: "ivl abs_state" where
  "test_env_precision = (\<lambda>_. ivl_top)((STR ''x'') := Ivl (Fin 4) (Fin 7))"

lemma interval_classify_precision_lower_proved:
  "interval_classify_check (Less (N 2) (V (STR ''x''))) test_env_precision = Check_Proved"
  unfolding test_env_precision_def by eval

lemma interval_classify_precision_upper_proved:
  "interval_classify_check (Less (V (STR ''x'')) (N 9)) test_env_precision = Check_Proved"
  unfolding test_env_precision_def by eval

end
