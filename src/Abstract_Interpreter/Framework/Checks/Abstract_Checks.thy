theory Abstract_Checks
  imports Check_Result Checks "Voblint_Domain.Abstract_Numeric_Queries"
    "Voblint_Domain.Forward_Domain" "Voblint_Domain.Three_Valued"
begin

section \<open>A domain-generic sound decision procedure for compiled checks\<close>

text \<open>
  A check needs two capabilities every domain with an \<open>exp\<close> evaluator already
  has: \<open>aval_abs_sound\<close>-shaped soundness (\<^locale>\<open>sound_evaluator\<close>, the same
  reuse point the \<open>backward_domain\<close> locale takes for its own \<open>aval_abs\<close>) and the
  relational queries of \<^locale>\<open>abstract_numeric_queries\<close>
  (\<^theory>\<open>Voblint_Domain.Abstract_Numeric_Queries\<close>). Extending
  \<open>abstract_numeric_queries\<close> directly, rather than fixing four raw
  entailment/refutation predicates here, means there is exactly one relational
  query interface in this codebase -- \<open>less\<close>/\<open>eq\<close> -- and every check-discharge
  consumer of it inherits whatever a domain already proved for
  \<^locale>\<open>abstract_numeric_queries\<close> instead of restating it.

  The per-domain guard machinery (the \<open>backward_domain\<close> locale's
  \<open>bfilter\<close>/\<open>afilter\<close>) would also decide a check: if \<open>bfilter c False \<sigma>\<close>
  represents no states, \<open>c\<close> is soundly established on \<open>\<sigma>\<close>, whenever
  \<open>gamma bot = {}\<close> --- a sound sufficient condition, not an iff, since no
  completeness result for \<open>bfilter\<close> is proved here. It is not usable as an
  executable decision procedure over \<open>'a abs_state\<close>, though: that is a raw
  function \<open>vname \<Rightarrow> 'a\<close> over the infinite type \<open>vname\<close>, so its emptiness test
  is not code-generable.

  This layer decides entailment directly off \<open>aval_abs\<close> results via \<open>less\<close>/
  \<open>eq\<close>. The judgments are sound but intentionally incomplete: two atomic
  values with overlapping concretizations are neither provably related nor
  provably unrelated, and are reported \<open>None\<close>/\<open>Check_Unknown\<close>, never
  misclassified.
\<close>

locale abstract_check_domain =
  abstract_numeric_queries less eq + sound_evaluator \<gamma>\<^sub>S aval_abs
  for less :: "'a::numeric_domain \<Rightarrow> 'a \<Rightarrow> bool option"
    and eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and \<gamma>\<^sub>S :: "'d \<Rightarrow> store set"
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a"
begin

subsection \<open>A single three-valued decision procedure over \<^typ>\<open>exp\<close>\<close>

text \<open>
  \<open>check_query\<close> replaces a mutually recursive true/false judgment pair with
  one function into \<^typ>\<open>bool option\<close>, matching the shape
  \<^locale>\<open>abstract_numeric_queries\<close> already gives its two atomic queries:
  \<open>Some True\<close> means definitely true, \<open>Some False\<close> definitely false, \<open>None\<close>
  undecided. \<open>Not\<close> negates through @{const map_option}; \<open>And\<close>/\<open>Or\<close> combine
  through @{const and_opt}/@{const or_opt}; \<open>Less\<close>/\<open>Eq\<close> read \<open>less\<close>/\<open>eq\<close>
  directly; every other expression falls back to testing it against zero
  through \<open>eq\<close>, negated -- \<^const>\<open>truthy\<close> is C's non-zero test, so an
  expression is true exactly when it is not equal to zero.
\<close>

definition truthy_query :: "exp \<Rightarrow> 'd \<Rightarrow> bool option" where
 [code]: "truthy_query e d = map_option HOL.Not (eq (aval_abs e d) (aval_abs (N 0) d))"

lemma truthy_query_sound:
  assumes mem: "s \<in> \<gamma>\<^sub>S d"
    and query: "truthy_query e d = Some r"
  shows "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = r"
  using assms aval_abs_sound eq_sound truthy_query_def
  by fastforce

fun check_query :: "exp \<Rightarrow> 'd \<Rightarrow> bool option" where
    "check_query (Not b) d = map_option HOL.Not (check_query b d)"
  | "check_query (And b1 b2) d = and_opt (check_query b1 d) (check_query b2 d)"
  | "check_query (Or b1 b2) d = or_opt (check_query b1 d) (check_query b2 d)"
  | "check_query (Less a b) d = less (aval_abs a d) (aval_abs b d)"
  | "check_query (LessEq a b) d = map_option HOL.Not (less (aval_abs b d) (aval_abs a d))"
  | "check_query (Greater a b) d = less (aval_abs b d) (aval_abs a d)"
  | "check_query (GreaterEq a b) d = map_option HOL.Not (less (aval_abs a d) (aval_abs b d))"
  | "check_query (Eq a b) d = eq (aval_abs a d) (aval_abs b d)"
  | "check_query (NotEq a b) d = map_option HOL.Not (eq (aval_abs a d) (aval_abs b d))"
  | "check_query e d = truthy_query e d"

text \<open>Soundness of the arithmetic fallback, proved once and cited by every
  induction case it covers (\<open>N\<close>/\<open>V\<close>/\<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close>). Naming the
  fallback \<open>truthy_query\<close> rather than inlining the \<open>map_option\<close> expression
  keeps \<open>check_query.simps\<close> a plain one-step rewrite for these five cases, so
  \<open>auto\<close> can chain straight into this lemma instead of first landing on
  \<open>map_option\<close>'s own case split.\<close>

theorem check_query_sound:
  assumes mem: "s \<in> \<gamma>\<^sub>S d"
  shows "check_query c d = Some r \<Longrightarrow> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s) = r"
using truthy_query_sound[OF mem] proof (induction c arbitrary: r)
  case (And b1 b2)
  then show ?case
    using and_opt_sound by auto
next
  case (Or b1 b2)
  text \<open>Unlike \<open>And\<close>, this case names the two concrete disjuncts: \<open>or_opt_sound\<close>
    quantifies over the propositions its two options stand for, and nothing in
    the goal determines them by unification.\<close>
  then show ?case
    using or_opt_sound[of "check_query b1 d" "check_query b2 d" r
        "truthy (\<lbrakk>b1\<rbrakk>\<^sub>e s)" "truthy (\<lbrakk>b2\<rbrakk>\<^sub>e s)"]
    by auto
next
  case (Less a b)
  then show ?case using aval_abs_sound mem less_sound by auto
next
  case (Eq a b)
  then show ?case using aval_abs_sound mem eq_sound by auto
next
  case (LessEq a b)
  have query: "less (aval_abs b d) (aval_abs a d) = Some (\<not> r)"
    using LessEq.prems by (auto split: option.splits)
  have relation: "(\<lbrakk>b\<rbrakk>\<^sub>e s < \<lbrakk>a\<rbrakk>\<^sub>e s) = (\<not> r)"
    by (rule less_sound[OF query aval_abs_sound[OF mem] aval_abs_sound[OF mem]])
  show ?case using relation by auto
next
  case (Greater a b)
  have query: "less (aval_abs b d) (aval_abs a d) = Some r"
    using Greater.prems by simp
  have relation: "(\<lbrakk>b\<rbrakk>\<^sub>e s < \<lbrakk>a\<rbrakk>\<^sub>e s) = r"
    by (rule less_sound[OF query aval_abs_sound[OF mem] aval_abs_sound[OF mem]])
  show ?case using relation by simp
next
  case (GreaterEq a b)
  have query: "less (aval_abs a d) (aval_abs b d) = Some (\<not> r)"
    using GreaterEq.prems by (auto split: option.splits)
  have relation: "(\<lbrakk>a\<rbrakk>\<^sub>e s < \<lbrakk>b\<rbrakk>\<^sub>e s) = (\<not> r)"
    by (rule less_sound[OF query aval_abs_sound[OF mem] aval_abs_sound[OF mem]])
  show ?case using relation by auto
next
  case (NotEq a b)
  have query: "eq (aval_abs a d) (aval_abs b d) = Some (\<not> r)"
    using NotEq.prems by (auto split: option.splits)
  have relation: "(\<lbrakk>a\<rbrakk>\<^sub>e s = \<lbrakk>b\<rbrakk>\<^sub>e s) = (\<not> r)"
    by (rule eq_sound[OF query aval_abs_sound[OF mem] aval_abs_sound[OF mem]])
  show ?case using relation by auto
qed (fastforce+)


subsection \<open>Executable three-way classification\<close>

definition classify_check :: "exp \<Rightarrow> 'd \<Rightarrow> check_result" where
  "classify_check c d =
     (case check_query c d of
        Some True \<Rightarrow> Check_Proved
      | Some False \<Rightarrow> Check_Refuted
      | None \<Rightarrow> Check_Unknown)"

lemma classify_check_proved:
  assumes "classify_check c d = Check_Proved" and "s \<in> \<gamma>\<^sub>S d"
  shows "truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
  using assms check_query_sound
  unfolding classify_check_def
  by (fastforce split: option.splits bool.splits)

lemma classify_check_refuted:
  assumes "classify_check c d = Check_Refuted" and "s \<in> \<gamma>\<^sub>S d"
  shows "\<not> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
  using assms check_query_sound
  unfolding classify_check_def
  by (fastforce split: option.splits bool.splits)

text \<open>\<open>Check_Unknown\<close> carries no semantic claim: no lemma concludes \<open>truthy
  (\<lbrakk>c\<rbrakk>\<^sub>e s)\<close> or its negation from it, by design.\<close>

subsection \<open>Node-indexed bridge to \<^const>\<open>checks_proven\<close>\<close>

definition abstract_checks_proven :: "checks \<Rightarrow> (pp \<Rightarrow> 'd) \<Rightarrow> bool" where
  "abstract_checks_proven ck env \<longleftrightarrow> (\<forall>v c. (v, c) \<in> ck \<longrightarrow> check_query c (env v) = Some True)"

lemma abstract_checks_provenI [intro]:
  "(\<And>v c. (v, c) \<in> ck \<Longrightarrow> check_query c (env v) = Some True) \<Longrightarrow> abstract_checks_proven ck env"
  unfolding abstract_checks_proven_def by blast

lemma abstract_checks_provenD [dest]:
  "abstract_checks_proven ck env \<Longrightarrow> (v, c) \<in> ck \<Longrightarrow> check_query c (env v) = Some True"
  unfolding abstract_checks_proven_def by blast

theorem abstract_checks_proven_sound:
  assumes node_sound: "\<And>v c. (v, c) \<in> ck \<Longrightarrow> reach v \<le> \<gamma>\<^sub>S (env v)"
    and checked: "abstract_checks_proven ck env"
  shows "checks_proven ck reach"
proof (rule checks_provenI)
  fix v c s
  assume ck': "(v, c) \<in> ck" and mem: "s \<in> reach v"
  have proven: "check_query c (env v) = Some True"
    using checked ck' by blast
  have in_gamma: "s \<in> \<gamma>\<^sub>S (env v)"
    using node_sound[OF ck'] mem by blast
  show "truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
    using check_query_sound[OF in_gamma proven] by simp
qed

end


end

