theory Congruence_Classify
  imports Congruence_Numeric_Queries "Voblint_Framework.Abstract_Checks"
    "Voblint_Framework.Analysis_Result" Congruence_Exec
    "Voblint_Result.DG_Result_Construction"
begin

hide_const phase.N

section \<open>Deciding a check from a map of residue classes\<close>

text \<open>
  Only composition lives here. The comparison tables \<^const>\<open>congruence_lt\<close> and
  \<^const>\<open>congruence_eqb\<close> and their interpretation of \<open>abstract_numeric_queries\<close>
  live in \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Numeric_Queries\<close>; the
  expression evaluator \<^const>\<open>aval_congruence\<close> lives in
  \<^theory>\<open>Voblint_Analysis_Congruence.Congruence_Arithmetic\<close>. The Boolean recursion
  over \<^typ>\<open>exp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from interpreting
  \<open>abstract_check_domain\<close> once, below.
\<close>

global_interpretation congruence_check_domain:
  abstract_check_domain congruence_lt congruence_eqb gamma_state aval_congruence
  defines
    congruence_truthy_query = congruence_check_domain.truthy_query
    and congruence_check_query = congruence_check_domain.check_query
    and congruence_classify_check = congruence_check_domain.classify_check
    and congruence_checks_proven = congruence_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: exp and \<sigma> :: "congruence abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" using gamma_stateD by blast
  then show "aval e s \<in> gamma (aval_congruence e \<sigma>)"
    by (rule congruence_arith.aval_dom_sound)
qed

lemmas congruence_classify_check_proved = congruence_check_domain.classify_check_proved
lemmas congruence_classify_check_refuted = congruence_check_domain.classify_check_refuted
lemmas congruence_checks_provenI = congruence_check_domain.abstract_checks_provenI
lemmas congruence_checks_proven_sound = congruence_check_domain.abstract_checks_proven_sound

subsection \<open>Executable classification tests\<close>

text \<open>
  What Congruence can and cannot decide, pinned as executable witnesses. A
  residue class with modulus \<open>0\<close> is a single integer, so equality against a
  literal is decided in both directions. A class with a larger modulus is not,
  and order is never decided at all --- knowing a value modulo \<open>2\<close> places no
  bound on it.
\<close>

definition test_env_four :: "congruence abs_state" where
  "test_env_four = (\<lambda>_. top)((STR ''x'') := congruence_of_int 4)"

lemma congruence_classify_eq_proved:
  "congruence_classify_check (Eq (V (STR ''x'')) (N 4)) test_env_four = Check_Proved"
  unfolding test_env_four_def by eval

lemma congruence_classify_eq_refuted:
  "congruence_classify_check (Eq (V (STR ''x'')) (N 5)) test_env_four = Check_Refuted"
  unfolding test_env_four_def by eval

text \<open>Order carries no information even at a singleton, because
  \<^const>\<open>congruence_lt\<close> answers \<^const>\<open>None\<close> everywhere.\<close>

lemma congruence_classify_less_unknown:
  "congruence_classify_check (Less (V (STR ''x'')) (N 9)) test_env_four = Check_Unknown"
  unfolding test_env_four_def by eval

text \<open>
  An even value against an odd literal. The two residue classes are disjoint, so
  this is refutable in principle; \<^const>\<open>congruence_eqb\<close> answers only when both
  sides are singletons, so the current table returns \<^const>\<open>Check_Unknown\<close>. The
  witness records the implementation's reach, not the domain's.
\<close>

definition test_env_even :: "congruence abs_state" where
  "test_env_even = (\<lambda>_. top)((STR ''x'') := mk_congruence 0 2)"

lemma congruence_classify_even_vs_odd_unknown:
  "congruence_classify_check (Eq (V (STR ''x'')) (N 3)) test_env_even = Check_Unknown"
  unfolding test_env_even_def by eval

text \<open>Negation and the Boolean connectives go through \<open>check_query\<close>'s own
  recursion, not through a one-sided reading of the positive answer.\<close>

lemma congruence_classify_not_proved:
  "congruence_classify_check (Not (Eq (V (STR ''x'')) (N 5))) test_env_four = Check_Proved"
  unfolding test_env_four_def by eval

lemma congruence_classify_and_proved:
  "congruence_classify_check
     (And (Eq (V (STR ''x'')) (N 4)) (Not (Eq (V (STR ''x'')) (N 5)))) test_env_four
   = Check_Proved"
  unfolding test_env_four_def by eval

end
