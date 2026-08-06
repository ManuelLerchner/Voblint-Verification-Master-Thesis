theory Abstract_Checks
  imports Checks
begin

datatype check_result = Check_Proved | Check_Refuted | Check_Unknown

section \<open>Generic numeric relational queries\<close>

text \<open>
  Entailment/refutation of \<open><\<close>/\<open>=\<close> over an abstract numeric value is not
  check-specific: it is the same question a backward/guard domain answers,
  phrased as a query instead of a narrowing. Kept as its own locale, separate
  from expression abstraction and separate from the Boolean layer, so a
  domain that only has these four operations (no \<open>aexp\<close>/\<open>store\<close> concept at
  all) could still interpret it.
\<close>

locale abstract_numeric_queries =
  fixes gamma_num :: "'a \<Rightarrow> int set"
    and less_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and eq_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and eq_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes less_true_sound:
      "less_true a b \<Longrightarrow> i \<in> gamma_num a \<Longrightarrow> j \<in> gamma_num b \<Longrightarrow> i < j"
    and less_false_sound:
      "less_false a b \<Longrightarrow> i \<in> gamma_num a \<Longrightarrow> j \<in> gamma_num b \<Longrightarrow> \<not> i < j"
    and eq_true_sound:
      "eq_true a b \<Longrightarrow> i \<in> gamma_num a \<Longrightarrow> j \<in> gamma_num b \<Longrightarrow> i = j"
    and eq_false_sound:
      "eq_false a b \<Longrightarrow> i \<in> gamma_num a \<Longrightarrow> j \<in> gamma_num b \<Longrightarrow> i \<noteq> j"

section \<open>Expression abstraction over a state, given numeric queries\<close>

text \<open>
  Adds the one capability every domain with an \<open>aexp\<close> evaluator already has:
  \<open>aval_abs_sound\<close>-shaped soundness, the same reuse point
  \<^theory>\<open>Voblint_Core.Abstract_Domain\<close>'s \<open>backward_domain\<close> locale takes for its own
  \<open>aval_abs\<close> parameter.
\<close>

locale abstract_expression_domain =
  abstract_numeric_queries gamma_num less_true less_false eq_true eq_false
  for gamma_num :: "'a \<Rightarrow> int set"
    and less_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and eq_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and eq_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  + fixes gamma_state :: "'d \<Rightarrow> store set"
    and aval_abs :: "aexp \<Rightarrow> 'd \<Rightarrow> 'a"
  assumes aval_abs_sound:
      "s \<in> gamma_state d \<Longrightarrow> aval e s \<in> gamma_num (aval_abs e d)"

section \<open>A domain-generic sound decision procedure for compiled checks\<close>

text \<open>
  Reusing the existing per-domain guard/assume machinery
  (\<^theory>\<open>Voblint_Core.Abstract_Domain\<close>'s \<open>backward_domain\<close> locale, its \<open>bfilter\<close>/
  \<open>afilter\<close>, and the Sign instances \<open>assume_sign\<close>/\<open>assume_not_sign\<close>) was
  investigated first: \<open>check_true c \<sigma> \<longleftrightarrow> bfilter c False \<sigma> = bot\<close> is sound
  whenever \<open>gamma bot = {}\<close>, and would give \<open>Not\<close>/\<open>And\<close>/\<open>Or\<close> for free from
  \<open>bfilter\<close>'s own recursion. It is not usable as an executable decision
  procedure in this codebase, though: an \<open>'a abs_state\<close> is a raw function
  \<open>vname \<Rightarrow> 'a\<close> over the infinite type \<open>vname\<close>, so \<open>= bot\<close> at that level is not
  code-generable; the finite executable mirror \<open>'a resolved_st_q\<close>
  (\<open>Voblint_Core.Exec_St\<close>) is a \<open>quotient_type\<close> whose \<open>\<le>\<close>/\<open>=\<close> instance is a
  \<open>lift_definition\<close> quantifying over \<open>location\<close>, with no \<open>[code]\<close> equation ---
  confirmed empirically: \<open>value "cinit_sign_st = bot"\<close> does not reduce, echoing
  the unevaluated term instead of \<open>True\<close>/\<open>False\<close>.

  A second, narrower reuse route also exists at the atomic-value level: e.g.
  Sign's own \<open>inv_less_sign\<close> (backward inversion of \<open><\<close>, already sound-proven,
  \<open>Voblint_Analysis.Sign_Backward\<close>) could derive \<open>less_true a b\<close> as
  \<open>fst (inv_less_sign False a b) = SBot \<or> snd (inv_less_sign False a b) = SBot\<close>
  --- unlike the state-level route, individual atoms have decidable equality,
  so this stays executable. There is no comparable existing operator for
  \<open>eq_true\<close>/\<open>eq_false\<close> (\<open>bfilter\<close>'s \<open>Eq\<close> case only ever narrows the \<open>True\<close>
  branch, via \<open>meet\<close>, never tests definite inequality), so the four query
  functions are defined directly per domain rather than partially reused.

  This layer decides entailment directly off \<open>aval_abs\<close> results via
  \<open>less_true\<close>/\<open>less_false\<close>/\<open>eq_true\<close>/\<open>eq_false\<close>. The
  judgments are sound but intentionally incomplete: two atomic values with
  overlapping concretizations are neither provably related nor provably
  unrelated, and are reported \<open>Check_Unknown\<close>, never misclassified as
  refuted.
\<close>

locale abstract_check_domain =
  abstract_expression_domain gamma_num less_true less_false eq_true eq_false gamma_state aval_abs
  for gamma_num :: "'a \<Rightarrow> int set"
    and less_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and less_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and eq_true :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and eq_false :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and gamma_state :: "'d \<Rightarrow> store set"
    and aval_abs :: "aexp \<Rightarrow> 'd \<Rightarrow> 'a"
begin

subsection \<open>Mutual truth/falsity judgments over \<^typ>\<open>bexp\<close>\<close>

text \<open>
  \<open>check_true\<close>/\<open>check_false\<close> are mutually recursive so \<open>Not\<close> can go through
  definitely-false reasoning on its argument rather than a one-sided negation
  of \<open>check_true\<close> (which would be unsound: "not provably true" is not
  "provably false"). Both may be \<^const>\<open>False\<close> on the same \<open>bexp\<close>/state pair;
  that combination means unknown, not refuted.
\<close>

fun check_true :: "bexp \<Rightarrow> 'd \<Rightarrow> bool"
  and check_false :: "bexp \<Rightarrow> 'd \<Rightarrow> bool" where
    "check_true (Bc v) d = v"
  | "check_false (Bc v) d = (\<not> v)"
  | "check_true (Not b) d = check_false b d"
  | "check_false (Not b) d = check_true b d"
  | "check_true (And b1 b2) d = (check_true b1 d \<and> check_true b2 d)"
  | "check_false (And b1 b2) d = (check_false b1 d \<or> check_false b2 d)"
  | "check_true (Or b1 b2) d = (check_true b1 d \<or> check_true b2 d)"
  | "check_false (Or b1 b2) d = (check_false b1 d \<and> check_false b2 d)"
  | "check_true (Less a b) d = less_true (aval_abs a d) (aval_abs b d)"
  | "check_false (Less a b) d = less_false (aval_abs a d) (aval_abs b d)"
  | "check_true (Eq a b) d = eq_true (aval_abs a d) (aval_abs b d)"
  | "check_false (Eq a b) d = eq_false (aval_abs a d) (aval_abs b d)"

lemma check_true_check_false_sound:
  "(\<forall>d s. check_true c d \<longrightarrow> s \<in> gamma_state d \<longrightarrow> bval c s) \<and>
   (\<forall>d s. check_false c d \<longrightarrow> s \<in> gamma_state d \<longrightarrow> \<not> bval c s)"
proof (induction c)
  case (Bc x) then show ?case by simp
next
  case (Not c) then show ?case by auto
next
  case (And c1 c2) then show ?case by auto
next
  case (Or c1 c2) then show ?case by auto
next
  case (Less a b) then show ?case
    using aval_abs_sound less_true_sound less_false_sound by fastforce
next
  case (Eq a b) then show ?case
    using aval_abs_sound eq_true_sound eq_false_sound by fastforce
qed

lemma check_true_sound:
  "check_true c d \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> bval c s"
  using check_true_check_false_sound by blast

lemma check_false_sound:
  "check_false c d \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> \<not> bval c s"
  using check_true_check_false_sound by blast

text \<open>Both judgments holding at once is consistent only if the state itself is
  vacuous --- e.g. every comparison against a bottom atom is both \<open>check_true\<close>
  and \<open>check_false\<close>, vacuously, since \<open>gamma_num\<close> of a bottom atom is
  empty. This does not weaken soundness: a vacuous \<open>gamma_state d\<close> makes both
  \<open>check_true_sound\<close> and \<open>check_false_sound\<close> vacuously true too.\<close>
lemma check_true_false_vacuous:
  assumes "check_true c d" and "check_false c d"
  shows "gamma_state d = {}"
proof (rule ccontr)
  assume "gamma_state d \<noteq> {}"
  then obtain s where s: "s \<in> gamma_state d" by blast
  have "bval c s" using check_true_sound[OF assms(1) s] .
  moreover have "\<not> bval c s" using check_false_sound[OF assms(2) s] .
  ultimately show False by blast
qed

subsection \<open>Executable three-way classification\<close>

definition classify_check :: "bexp \<Rightarrow> 'd \<Rightarrow> check_result" where
  "classify_check c d =
     (if check_true c d then Check_Proved
      else if check_false c d then Check_Refuted
      else Check_Unknown)"

lemma classify_check_proved:
  assumes "classify_check c d = Check_Proved" and "s \<in> gamma_state d"
  shows "bval c s"
proof -
  have "check_true c d" using assms(1) unfolding classify_check_def by (auto split: if_splits)
  then show ?thesis using assms(2) check_true_sound by blast
qed

lemma classify_check_refuted:
  assumes "classify_check c d = Check_Refuted" and "s \<in> gamma_state d"
  shows "\<not> bval c s"
proof -
  have "check_false c d" using assms(1) unfolding classify_check_def by (auto split: if_splits)
  then show ?thesis using assms(2) check_false_sound by blast
qed

text \<open>\<open>Check_Unknown\<close> carries no semantic claim: no lemma concludes \<open>bval c s\<close>
  or its negation from it, by design.\<close>

subsection \<open>Node-indexed bridge to \<^const>\<open>checks_proven\<close>\<close>

definition abstract_checks_proven :: "checks \<Rightarrow> (pp \<Rightarrow> 'd) \<Rightarrow> bool" where
  "abstract_checks_proven ck env \<longleftrightarrow> (\<forall>v c. (v, c) \<in> ck \<longrightarrow> check_true c (env v))"

lemma abstract_checks_provenI [intro]:
  "(\<And>v c. (v, c) \<in> ck \<Longrightarrow> check_true c (env v)) \<Longrightarrow> abstract_checks_proven ck env"
  unfolding abstract_checks_proven_def by blast

theorem abstract_checks_proven_sound:
  assumes node_sound: "\<And>v c. (v, c) \<in> ck \<Longrightarrow> reach v \<le> gamma_state (env v)"
    and checked: "abstract_checks_proven ck env"
  shows "checks_proven ck reach"
proof (rule checks_provenI)
  fix v c s
  assume ck': "(v, c) \<in> ck" and mem: "s \<in> reach v"
  have proven: "check_true c (env v)"
    using checked ck' unfolding abstract_checks_proven_def by blast
  have in_gamma: "s \<in> gamma_state (env v)"
    using node_sound[OF ck'] mem by blast
  show "bval c s"
    using check_true_sound[OF proven in_gamma] .
qed

end

end

