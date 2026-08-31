theory Abstract_Checks
  imports Check_Result Checks "Voblint_Domain.Abstract_Numeric_Queries"
begin


section \<open>Three-valued Boolean combinators\<close>

text \<open>
  \<open>and_opt\<close>/\<open>or_opt\<close> give \<open>bool option\<close> the same short-circuit reading
  \<^const>\<open>truthy\<close>'s own \<open>\<and>\<close>/\<open>\<or>\<close> already have: a definite \<open>False\<close> operand decides
  an \<open>and_opt\<close> regardless of the other side (symmetrically, a definite \<open>True\<close>
  operand decides an \<open>or_opt\<close>), and only two agreeing definite operands decide
  the other direction. Anything else is \<open>None\<close> -- neither operand alone can be
  blamed for the unknown.
\<close>

definition and_opt :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "and_opt x y = (if x = Some False \<or> y = Some False then Some False
                   else if x = Some True \<and> y = Some True then Some True
                   else None)"

definition or_opt :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "or_opt x y = (if x = Some True \<or> y = Some True then Some True
                  else if x = Some False \<and> y = Some False then Some False
                  else None)"

text \<open>
  The semantic reading a caller actually wants: given what \<open>x\<close>/\<open>y\<close> mean
  (\<open>px\<close>/\<open>py\<close>, via the same Horn-clause shape an induction hypothesis already
  has), \<open>and_opt\<close>/\<open>or_opt\<close>'s answer agrees with plain Boolean \<open>\<and>\<close>/\<open>\<or>\<close> on those
  meanings. Stated this way, a consumer never has to know \<open>and_opt\<close>/\<open>or_opt\<close>'s
  own three-way case split.
\<close>

lemma and_opt_sound:
  assumes "and_opt x y = Some r"
    and "\<And>b. x = Some b \<Longrightarrow> px = b"
    and "\<And>b. y = Some b \<Longrightarrow> py = b"
  shows "(px \<and> py) = r"
  using assms unfolding and_opt_def by (cases r) (auto split: if_splits)

lemma or_opt_sound:
  assumes "or_opt x y = Some r"
    and "\<And>b. x = Some b \<Longrightarrow> px = b"
    and "\<And>b. y = Some b \<Longrightarrow> py = b"
  shows "(px \<or> py) = r"
  using assms unfolding or_opt_def by (cases r) (auto split: if_splits)

section \<open>Expression abstraction over a state, given numeric queries\<close>

text \<open>
  Adds the one capability every domain with an \<open>exp\<close> evaluator already has,
  on top of \<^locale>\<open>abstract_numeric_queries\<close>
  (\<^theory>\<open>Voblint_Domain.Abstract_Numeric_Queries\<close>): \<open>aval_abs_sound\<close>-shaped
  soundness, the same reuse point \<^theory>\<open>Voblint_Domain.Abstract_Domain\<close>'s
  \<open>backward_domain\<close> locale takes for its own \<open>aval_abs\<close> parameter. Extending
  \<open>abstract_numeric_queries\<close> directly, rather than fixing four raw
  entailment/refutation predicates here, means there is exactly one relational
  query interface in this codebase -- \<open>less\<close>/\<open>eq\<close> -- and every check-discharge
  consumer of it inherits whatever a domain already proved for
  \<^locale>\<open>abstract_numeric_queries\<close> instead of restating it.
\<close>

locale abstract_expression_domain =
  abstract_numeric_queries less eq
    for less :: "'a::sound_domain \<Rightarrow> 'a \<Rightarrow> bool option"
      and eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool option" +
  fixes gamma_state :: "'d \<Rightarrow> store set"
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a"
  assumes aval_abs_sound[intro]:
      "s \<in> gamma_state d \<Longrightarrow> aval e s \<in> gamma (aval_abs e d)"

section \<open>A domain-generic sound decision procedure for compiled checks\<close>

text \<open>
  Reusing the existing per-domain guard/branch machinery
  (\<^theory>\<open>Voblint_Domain.Abstract_Domain\<close>'s \<open>backward_domain\<close> locale, its \<open>bfilter\<close>/
  \<open>afilter\<close>, and the Sign instance \<open>bfilter_sign\<close>) was
  investigated first: if \<open>bfilter c False \<sigma>\<close> represents no states, \<open>c\<close> is
  soundly established on \<open>\<sigma>\<close>, whenever \<open>gamma bot = {}\<close> --- a sound sufficient
  condition, not an iff, since no completeness result for \<open>bfilter\<close> is proved
  here. This would give \<open>Not\<close>/\<open>And\<close>/\<open>Or\<close> for free from
  \<open>bfilter\<close>'s own recursion. It is not usable as an executable decision
  procedure in this codebase, though: an \<open>'a abs_state\<close> is a raw function
  \<open>vname \<Rightarrow> 'a\<close> over the infinite type \<open>vname\<close>, so \<open>= bot\<close> at that level is not
  code-generable; the finite executable mirror \<open>'a resolved_st_q\<close>
  (\<open>Voblint_Exec.Exec_St\<close>) is a \<open>quotient_type\<close> whose \<open>\<le>\<close>/\<open>=\<close> instance is a
  \<open>lift_definition\<close> quantifying over \<open>location\<close>, with no \<open>[code]\<close> equation ---
  confirmed empirically: \<open>value \"cinit_sign_st = bot\"\<close> does not reduce, echoing
  the unevaluated term instead of \<open>True\<close>/\<open>False\<close>.

  This layer decides entailment directly off \<open>aval_abs\<close> results via \<open>less\<close>/
  \<open>eq\<close>. The judgments are sound but intentionally incomplete: two atomic
  values with overlapping concretizations are neither provably related nor
  provably unrelated, and are reported \<open>None\<close>/\<open>Check_Unknown\<close>, never
  misclassified.
\<close>

locale abstract_check_domain =
  abstract_expression_domain less eq gamma_state aval_abs
  for less :: "'a::sound_domain \<Rightarrow> 'a \<Rightarrow> bool option"
    and eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and gamma_state :: "'d \<Rightarrow> store set"
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
  assumes mem: "s \<in> gamma_state d"
    and query: "truthy_query e d = Some r"
  shows "truthy (aval e s) = r"
  using assms aval_abs_sound eq_sound truthy_query_def
  by fastforce

fun check_query :: "exp \<Rightarrow> 'd \<Rightarrow> bool option" where
    "check_query (Not b) d = map_option HOL.Not (check_query b d)"
  | "check_query (And b1 b2) d = and_opt (check_query b1 d) (check_query b2 d)"
  | "check_query (Or b1 b2) d = or_opt (check_query b1 d) (check_query b2 d)"
  | "check_query (Less a b) d = less (aval_abs a d) (aval_abs b d)"
  | "check_query (Eq a b) d = eq (aval_abs a d) (aval_abs b d)"
  | "check_query e d = truthy_query e d"

text \<open>Soundness of the arithmetic fallback, proved once and cited by every
  induction case it covers (\<open>N\<close>/\<open>V\<close>/\<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close>). Naming the
  fallback \<open>truthy_query\<close> rather than inlining the \<open>map_option\<close> expression
  keeps \<open>check_query.simps\<close> a plain one-step rewrite for these five cases, so
  \<open>auto\<close> can chain straight into this lemma instead of first landing on
  \<open>map_option\<close>'s own case split.\<close>

theorem check_query_sound:
  assumes mem: "s \<in> gamma_state d"
  shows "check_query c d = Some r \<Longrightarrow> truthy (aval c s) = r"
using truthy_query_sound[OF mem] proof (induction c arbitrary: r)
  case (And b1 b2)
  then show ?case
    using and_opt_sound by auto
next
  case (Or b1 b2)
  then show ?case 
  using or_opt_sound[
      of "check_query b1 d" "check_query b2 d" r
         "truthy (aval b1 s)" "truthy (aval b2 s)"]
    by auto
next
  case (Less a b)
  then show ?case using aval_abs_sound mem less_sound by auto
next
  case (Eq a b)
  then show ?case using aval_abs_sound mem eq_sound by auto
qed (fastforce+)


subsection \<open>Executable three-way classification\<close>

definition classify_check :: "exp \<Rightarrow> 'd \<Rightarrow> check_result" where
  "classify_check c d =
     (case check_query c d of
        Some True \<Rightarrow> Check_Proved
      | Some False \<Rightarrow> Check_Refuted
      | None \<Rightarrow> Check_Unknown)"

lemma classify_check_proved:
  assumes "classify_check c d = Check_Proved" and "s \<in> gamma_state d"
  shows "truthy (aval c s)"
  using assms check_query_sound
  unfolding classify_check_def
  by (fastforce split: option.splits bool.splits)

lemma classify_check_refuted:
  assumes "classify_check c d = Check_Refuted" and "s \<in> gamma_state d"
  shows "\<not> truthy (aval c s)"
  using assms check_query_sound
  unfolding classify_check_def
  by (fastforce split: option.splits bool.splits)

text \<open>\<open>Check_Unknown\<close> carries no semantic claim: no lemma concludes \<open>truthy
  (aval c s)\<close> or its negation from it, by design.\<close>

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
  assumes node_sound: "\<And>v c. (v, c) \<in> ck \<Longrightarrow> reach v \<le> gamma_state (env v)"
    and checked: "abstract_checks_proven ck env"
  shows "checks_proven ck reach"
proof (rule checks_provenI)
  fix v c s
  assume ck': "(v, c) \<in> ck" and mem: "s \<in> reach v"
  have proven: "check_query c (env v) = Some True"
    using checked ck' by blast
  have in_gamma: "s \<in> gamma_state (env v)"
    using node_sound[OF ck'] mem by blast
  show "truthy (aval c s)"
    using check_query_sound[OF in_gamma proven] by simp
qed

end


end

