theory Int_Classify
  imports Int_Exec_Sound "Voblint_Core.Abstract_Checks"
    "Voblint_Core.Analysis_Result"
    "Voblint_Exec.Monovariant_Analysis_Result"
begin

hide_const phase.N

section \<open>Int instance of the generic check-discharge interface\<close>

text \<open>
  \<open>int_dom\<close> already carries a \<open>sound_domain\<close> instance (\<^theory>\<open>Voblint_Analysis.Int_Domain\<close>) and
  three \<^locale>\<open>backward_domain\<close> interpretations, one per refinement mode
  (\<^theory>\<open>Voblint_Analysis.Int_Backward\<close>). Unlike Sign and Interval, which each hand-roll their own
  sharper \<open>less_true\<close>/\<open>less_false\<close>/\<open>eq_true\<close>/\<open>eq_false\<close> comparison tables
  (\<open>Sign_Numeric_Queries\<close>, \<open>Interval_Numeric_Queries\<close>), \<open>int_dom\<close> reuses the generic derivation
  \<^theory>\<open>Voblint_Domain.Abstract_Numeric_Queries\<close> already proves for free off any
  \<^locale>\<open>backward_domain\<close> instance:  \<open>int_dom_backward_fixpoint.less_true\<close>/\<open>less_false\<close> come from
  \<open>inv_less_int_dom_fixpoint\<close>, and \<open>int_dom_backward_fixpoint.eq_true\<close>/
  \<open>eq_false\<close> come from \<open>less_false\<close>/\<open>intersect_int_dom_fixpoint\<close>, both
  defined directly in \<^locale>\<open>backward_domain\<close>'s own context
  (\<^theory>\<open>Voblint_Domain.Abstract_Numeric_Queries\<close>).

  \<open>int_less_true\<close>/\<open>int_less_false\<close>/\<open>int_eq_true\<close>/\<open>int_eq_false\<close> below restate those same four
  formulas as plain top-level \<open>definition\<close>s rather than citing the locale-derived constants
  directly: a \<open>definition\<close> gets a \<open>[code]\<close> equation automatically, while a constant introduced
  defined inside \<^locale>\<open>backward_domain\<close>'s own context (parameterised over an abstract
  \<open>inv_less\<close>) does not, so \<open>int_classify_check\<close> could not code-generate through the CLI directly against
  \<open>int_dom_backward_fixpoint.less_true\<close> \<open>et al.\<close>. Soundness for the four restated definitions is
  not re-derived: each is definitionally the exact same formula as its locale-derived
  counterpart (\<open>int_less_true_eq\<close> \<open>et al.\<close> below), so \<open>int_dom_backward_fixpoint.less_true_sound\<close>
  \<open>et al.\<close> transports over in one line. A sharper, hand-tuned composite table (reduced through
  all four components at once rather than \<open>int_ivl\<close>'s own \<open>inv_less\<close>/\<open>intersect\<close> alone) is
  future precision work, not required for this report route to be sound.
\<close>

definition int_less_true :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_less_true a b =
     (is_empty (fst (inv_less_int_dom Refine_Fixpoint False a b)) \<or> is_empty (snd (inv_less_int_dom Refine_Fixpoint False a b)))"

definition int_less_false :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_less_false a b =
     (is_empty (fst (inv_less_int_dom Refine_Fixpoint True a b)) \<or> is_empty (snd (inv_less_int_dom Refine_Fixpoint True a b)))"

definition int_eq_true :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_eq_true a b = (int_less_false a b \<and> int_less_false b a)"

definition int_eq_false :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool" where
  "int_eq_false a b = is_empty (intersect_int_dom_mode Refine_Fixpoint a b)"

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

definition int_less :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool option" where
  "int_less a b = (if int_less_true a b then Some True
                    else if int_less_false a b then Some False else None)"

definition int_eq :: "int_dom \<Rightarrow> int_dom \<Rightarrow> bool option" where
  "int_eq a b = (if int_eq_true a b then Some True
                  else if int_eq_false a b then Some False else None)"

lemma int_less_sound:
  assumes "int_less a b = Some r" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "(i < j) = r"
  using assms int_less_true_sound int_less_false_sound
  unfolding int_less_def by (auto split: if_splits)

lemma int_eq_sound:
  assumes "int_eq a b = Some r" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "(i = j) = r"
  using assms int_eq_true_sound int_eq_false_sound
  unfolding int_eq_def by (auto split: if_splits)

global_interpretation int_dom_numeric_queries: abstract_numeric_queries int_less int_eq
  by unfold_locales (metis int_less_sound int_eq_sound)+

global_interpretation int_check_domain:
  abstract_check_domain int_less int_eq gamma_state aval_int_dom_fixpoint
  defines
    int_truthy_query = int_check_domain.truthy_query
    and int_check_query = int_check_domain.check_query
    and int_classify_check = int_check_domain.classify_check
    and int_checks_proven = int_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: exp and \<sigma> :: "int_dom abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by blast
  then show "aval e s \<in> gamma (aval_int_dom_fixpoint e \<sigma>)" using aval_int_dom_sound by simp
qed

text \<open>
  Only the consumer-facing aliases get a short Int-prefixed name, the same choice
  \<open>Sign_Checks\<close>/\<open>Interval_Checks\<close> make: \<open>classify_check\<close>'s
  two directions and the \<open>checks_proven\<close> bridge. The lower-level
  \<open>check_query_sound\<close> fact \<open>classify_check\<close>'s own soundness is built from
  stays reachable under the qualified \<open>int_check_domain.\<close> name instead of
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

end
