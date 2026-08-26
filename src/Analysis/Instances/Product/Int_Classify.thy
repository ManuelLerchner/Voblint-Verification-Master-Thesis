theory Int_Classify
  imports Int_Exec_Sound "Voblint_Core.Abstract_Checks"
    "Voblint_Core.Analysis_Result"
    "Voblint_Core.Monovariant_Analysis_Result"
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
    gamma_state "aval_int_dom_t Refine_Fixpoint"
  defines
    int_check_true = int_check_domain.check_true
    and int_check_false = int_check_domain.check_false
    and int_classify_check = int_check_domain.classify_check
    and int_checks_proven = int_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: texp and \<sigma> :: "int_dom abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then show "teval e s \<in> gamma (aval_int_dom_t Refine_Fixpoint e \<sigma>)"
    using aval_int_dom_t_sound by simp
qed

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
  "int_classify_check (TLess (TVar I32 (STR ''x'')) (TN I32 11)) test_env_int_bounded
     = Check_Proved"
  unfolding test_env_int_bounded_def by eval

lemma int_classify_less_refuted:
  "int_classify_check (TLess (TVar I32 (STR ''x'')) (TN I32 0)) test_env_int_bounded
     = Check_Refuted"
  unfolding test_env_int_bounded_def by eval

lemma int_classify_eq_unknown:
  "int_classify_check (TEq (TVar I32 (STR ''x'')) (TN I32 5)) test_env_int_bounded
     = Check_Unknown"
  unfolding test_env_int_bounded_def by eval

end
