theory Abstract_Checks
  imports Checks CFG_Enumeration Analysis_Result "Voblint_Core.Abstract_Numeric_Queries"
begin

datatype check_result = Check_Proved | Check_Refuted | Check_Unknown

text \<open>
  \<open>check_result\<close> as a flat join-semilattice: \<open>Check_Unknown\<close> is the top element,
  \<open>Check_Proved\<close>/\<open>Check_Refuted\<close> are incomparable, and their join is
  \<open>Check_Unknown\<close>. The canonical use is aggregating a check's verdict across
  several independently-sound sources of evidence (e.g. one abstract state per
  reachable calling context) without joining the underlying abstract states
  first: two sources agreeing stay that verdict, any disagreement collapses to
  \<open>Check_Unknown\<close> rather than asserting a verdict neither source alone
  established.
\<close>

instantiation check_result :: semilattice_sup
begin

definition less_eq_check_result :: "check_result \<Rightarrow> check_result \<Rightarrow> bool" where
  "less_eq_check_result x y \<longleftrightarrow> x = y \<or> y = Check_Unknown"

definition less_check_result :: "check_result \<Rightarrow> check_result \<Rightarrow> bool" where
  "less_check_result x y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

definition sup_check_result :: "check_result \<Rightarrow> check_result \<Rightarrow> check_result" where
  "sup_check_result x y = (if x = y then x else Check_Unknown)"

instance
proof
  fix x y z :: check_result
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (rule less_check_result_def)
  show "x \<le> x" by (simp add: less_eq_check_result_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_check_result_def by auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_check_result_def by auto
  show "x \<le> x \<squnion> y" unfolding less_eq_check_result_def sup_check_result_def by auto
  show "y \<le> x \<squnion> y" unfolding less_eq_check_result_def sup_check_result_def by auto
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x" unfolding less_eq_check_result_def sup_check_result_def by auto
qed

end

lemma sup_check_result_idem [simp]: "(x::check_result) \<squnion> x = x"
  by (simp add: sup_check_result_def)

lemma SPIKE_sup_fin_eval: "Sup_fin {Check_Proved, Check_Proved} = Check_Proved" by eval

section \<open>Expression abstraction over a state, given numeric queries\<close>

text \<open>
  Adds the one capability every domain with an \<open>exp\<close> evaluator already has:
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
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a"
  assumes aval_abs_sound[intro]:
      "s \<in> gamma_state d \<Longrightarrow> aval e s \<in> gamma_num (aval_abs e d)"

section \<open>A domain-generic sound decision procedure for compiled checks\<close>

text \<open>
  Reusing the existing per-domain guard/branch machinery
  (\<^theory>\<open>Voblint_Core.Abstract_Domain\<close>'s \<open>backward_domain\<close> locale, its \<open>bfilter\<close>/
  \<open>afilter\<close>, and the Sign instance \<open>bfilter_sign\<close>) was
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
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a"
begin

subsection \<open>Mutual truth/falsity judgments over \<^typ>\<open>exp\<close>\<close>

text \<open>
  \<open>check_true\<close>/\<open>check_false\<close> are mutually recursive so \<open>Not\<close> can go through
  definitely-false reasoning on its argument rather than a one-sided negation
  of \<open>check_true\<close> (which would be unsound: "not provably true" is not
  "provably false"). Both may be \<^const>\<open>False\<close> on the same \<open>exp\<close>/state pair;
  that combination means unknown, not refuted.
\<close>

fun check_true :: "exp \<Rightarrow> 'd \<Rightarrow> bool"
  and check_false :: "exp \<Rightarrow> 'd \<Rightarrow> bool" where
    "check_true (Not b) d = check_false b d"
  | "check_false (Not b) d = check_true b d"
  | "check_true (And b1 b2) d = (check_true b1 d \<and> check_true b2 d)"
  | "check_false (And b1 b2) d = (check_false b1 d \<or> check_false b2 d)"
  | "check_true (Or b1 b2) d = (check_true b1 d \<or> check_true b2 d)"
  | "check_false (Or b1 b2) d = (check_false b1 d \<and> check_false b2 d)"
  | "check_true (Less a b) d = less_true (aval_abs a d) (aval_abs b d)"
  | "check_false (Less a b) d = less_false (aval_abs a d) (aval_abs b d)"
  | "check_true (Eq a b) d = eq_true (aval_abs a d) (aval_abs b d)"
  | "check_false (Eq a b) d = eq_false (aval_abs a d) (aval_abs b d)"
  | "check_true e d = eq_false (aval_abs e d) (aval_abs (N 0) d)"
  | "check_false e d = eq_true (aval_abs e d) (aval_abs (N 0) d)"

text \<open>Soundness of the arithmetic fallback, proved once and cited by every
  induction case it covers (\<open>N\<close>/\<open>V\<close>/\<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close>).\<close>
lemma check_true_default_sound:
  assumes "s \<in> gamma_state d" "eq_false (aval_abs e d) (aval_abs (N 0) d)"
  shows "truthy (aval e s)"
proof -
  have ec: "aval e s \<in> gamma_num (aval_abs e d)" using aval_abs_sound assms(1) by blast
  have e0: "aval (N 0) s \<in> gamma_num (aval_abs (N 0) d)" using aval_abs_sound assms(1) by blast
  have "aval e s \<noteq> aval (N 0) s" using eq_false_sound[OF assms(2) ec e0] .
  then show ?thesis by simp
qed

lemma check_false_default_sound:
  assumes "s \<in> gamma_state d" "eq_true (aval_abs e d) (aval_abs (N 0) d)"
  shows "\<not> truthy (aval e s)"
proof -
  have ec: "aval e s \<in> gamma_num (aval_abs e d)" using aval_abs_sound assms(1) by blast
  have e0: "aval (N 0) s \<in> gamma_num (aval_abs (N 0) d)" using aval_abs_sound assms(1) by blast
  have "aval e s = aval (N 0) s" using eq_true_sound[OF assms(2) ec e0] .
  then show ?thesis by simp
qed

lemma check_true_check_false_sound:
  "(\<forall>d s. check_true c d \<longrightarrow> s \<in> gamma_state d \<longrightarrow> truthy (aval c s)) \<and>
   (\<forall>d s. check_false c d \<longrightarrow> s \<in> gamma_state d \<longrightarrow> \<not> truthy (aval c s))"
proof (induction c)
  case (N n)
  show ?case
  proof (intro conjI allI impI)
    fix d s assume ct: "check_true (N n) d" and mem: "s \<in> gamma_state d"
    have "eq_false (aval_abs (N n) d) (aval_abs (N 0) d)" using ct by simp
    then show "truthy (aval (N n) s)" using check_true_default_sound[OF mem] by blast
  next
    fix d s assume cf: "check_false (N n) d" and mem: "s \<in> gamma_state d"
    have "eq_true (aval_abs (N n) d) (aval_abs (N 0) d)" using cf by simp
    then show "\<not> truthy (aval (N n) s)" using check_false_default_sound[OF mem] by blast
  qed
next
  case (V x)
  show ?case
  proof (intro conjI allI impI)
    fix d s assume ct: "check_true (V x) d" and mem: "s \<in> gamma_state d"
    have "eq_false (aval_abs (V x) d) (aval_abs (N 0) d)" using ct by simp
    then show "truthy (aval (V x) s)" using check_true_default_sound[OF mem] by blast
  next
    fix d s assume cf: "check_false (V x) d" and mem: "s \<in> gamma_state d"
    have "eq_true (aval_abs (V x) d) (aval_abs (N 0) d)" using cf by simp
    then show "\<not> truthy (aval (V x) s)" using check_false_default_sound[OF mem] by blast
  qed
next
  case (Plus e1 e2)
  show ?case
  proof (intro conjI allI impI)
    fix d s assume ct: "check_true (Plus e1 e2) d" and mem: "s \<in> gamma_state d"
    have "eq_false (aval_abs (Plus e1 e2) d) (aval_abs (N 0) d)" using ct by simp
    then show "truthy (aval (Plus e1 e2) s)" using check_true_default_sound[OF mem] by blast
  next
    fix d s assume cf: "check_false (Plus e1 e2) d" and mem: "s \<in> gamma_state d"
    have "eq_true (aval_abs (Plus e1 e2) d) (aval_abs (N 0) d)" using cf by simp
    then show "\<not> truthy (aval (Plus e1 e2) s)" using check_false_default_sound[OF mem] by blast
  qed
next
  case (Minus e1 e2)
  show ?case
  proof (intro conjI allI impI)
    fix d s assume ct: "check_true (Minus e1 e2) d" and mem: "s \<in> gamma_state d"
    have "eq_false (aval_abs (Minus e1 e2) d) (aval_abs (N 0) d)" using ct by simp
    then show "truthy (aval (Minus e1 e2) s)" using check_true_default_sound[OF mem] by blast
  next
    fix d s assume cf: "check_false (Minus e1 e2) d" and mem: "s \<in> gamma_state d"
    have "eq_true (aval_abs (Minus e1 e2) d) (aval_abs (N 0) d)" using cf by simp
    then show "\<not> truthy (aval (Minus e1 e2) s)" using check_false_default_sound[OF mem] by blast
  qed
next
  case (Times e1 e2)
  show ?case
  proof (intro conjI allI impI)
    fix d s assume ct: "check_true (Times e1 e2) d" and mem: "s \<in> gamma_state d"
    have "eq_false (aval_abs (Times e1 e2) d) (aval_abs (N 0) d)" using ct by simp
    then show "truthy (aval (Times e1 e2) s)" using check_true_default_sound[OF mem] by blast
  next
    fix d s assume cf: "check_false (Times e1 e2) d" and mem: "s \<in> gamma_state d"
    have "eq_true (aval_abs (Times e1 e2) d) (aval_abs (N 0) d)" using cf by simp
    then show "\<not> truthy (aval (Times e1 e2) s)" using check_false_default_sound[OF mem] by blast
  qed
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
  "check_true c d \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> truthy (aval c s)"
  using check_true_check_false_sound by blast

lemma check_false_sound:
  "check_false c d \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> \<not> truthy (aval c s)"
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
  have "truthy (aval c s)" using check_true_sound[OF assms(1) s] .
  moreover have "\<not> truthy (aval c s)" using check_false_sound[OF assms(2) s] .
  ultimately show False by blast
qed

subsection \<open>Executable three-way classification\<close>

definition classify_check :: "exp \<Rightarrow> 'd \<Rightarrow> check_result" where
  "classify_check c d =
     (if check_true c d then Check_Proved
      else if check_false c d then Check_Refuted
      else Check_Unknown)"

lemma classify_check_proved:
  assumes "classify_check c d = Check_Proved" and "s \<in> gamma_state d"
  shows "truthy (aval c s)"
proof -
  have "check_true c d" using assms(1) unfolding classify_check_def by (auto split: if_splits)
  then show ?thesis using assms(2) check_true_sound by blast
qed

lemma classify_check_refuted:
  assumes "classify_check c d = Check_Refuted" and "s \<in> gamma_state d"
  shows "\<not> truthy (aval c s)"
proof -
  have "check_false c d" using assms(1) unfolding classify_check_def by (auto split: if_splits)
  then show ?thesis using assms(2) check_false_sound by blast
qed

text \<open>\<open>Check_Unknown\<close> carries no semantic claim: no lemma concludes \<open>truthy
  (aval c s)\<close> or its negation from it, by design.\<close>

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
  show "truthy (aval c s)"
    using check_true_sound[OF proven in_gamma] .
qed

end

section \<open>Whole-program executable check report\<close>

text \<open>
  A single, domain-generic report over every compiled \<^const>\<open>EA_Check\<close> edge:
  one entry per check, at its own source node, classified by whatever
  \<open>classify\<close> function a domain supplies (\<open>sign_classify_check\<close> and its
  siblings, or \<open>abstract_check_domain.classify_check\<close> generically). Entries
  are read directly off \<^const>\<open>intra\<close> through the same deterministic order
  \<^const>\<open>cfg_intra_list\<close> already gives the TD bridge, rather than sorting
  \<^typ>\<open>pp\<close> or \<^typ>\<open>exp\<close> values by hand: a compiled \<^const>\<open>checks\<close> table has
  exactly the same \<^const>\<open>EA_Check\<close> edges as its source, by construction, so
  this report is a second view of that one representation, not a parallel
  table.
\<close>

type_synonym check_report_entry = "pp \<times> exp \<times> check_result"

definition classify_checks ::
    "cfg \<Rightarrow> (pp \<Rightarrow> 's) \<Rightarrow> (exp \<Rightarrow> 's \<Rightarrow> check_result) \<Rightarrow> check_report_entry list" where
  "classify_checks g env classify =
     map (\<lambda>(u, a, v). (u, ea_check_cond a, classify (ea_check_cond a) (env u)))
       (filter (\<lambda>(u, a, v). is_EA_Check a) (cfg_intra_list g))"

text \<open>Membership unfolds to an \<^const>\<open>EA_Check\<close> edge at the entry's own
  source node, classified there --- the shape every soundness and
  worked-example use of \<^const>\<open>classify_checks\<close> goes through.\<close>

lemma classify_checks_mem_iff:
  assumes "finite (intra g)"
  shows "(v, c, r) \<in> set (classify_checks g env classify)
     \<longleftrightarrow> (\<exists>tgt. (v, EA_Check c, tgt) \<in> intra g) \<and> r = classify c (env v)"
  unfolding classify_checks_def set_map set_filter
  using set_cfg_intra_list[OF assms]
  by (auto simp: image_iff split: edge_action.splits)

text \<open>
  Soundness bridge: a \<^term>\<open>Check_Proved\<close> report entry's condition genuinely
  holds at every reaching store, and a \<^term>\<open>Check_Refuted\<close> entry's condition
  genuinely fails --- given the same two facts every per-domain instance
  already proves once: a \<open>classify_check_proved\<close>/\<open>classify_check_refuted\<close>-
  shaped soundness obligation for the domain's own \<open>classify\<close>, and node-local
  collecting soundness (\<open>reach v \<le> gamma_state (env v)\<close>) for the checked
  node. Neither theorem invents new domain reasoning; both only relocate an
  existing per-node fact to every entry of the whole-program report.
  \<^term>\<open>Check_Unknown\<close> gets no counterpart, matching \<open>classify_check\<close> itself.
\<close>

theorem classify_checks_proved_sound:
  fixes gamma_state :: "'s \<Rightarrow> store set"
  assumes fin: "finite (intra g)"
    and mem: "(v, c, Check_Proved) \<in> set (classify_checks g env classify)"
    and classify_proved: "\<And>d s. classify c d = Check_Proved \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> truthy (aval c s)"
    and node_sound: "reach v \<le> gamma_state (env v)"
  shows "\<forall>s \<in> reach v. truthy (aval c s)"
proof
  fix s assume s: "s \<in> reach v"
  have "classify c (env v) = Check_Proved"
    using mem classify_checks_mem_iff[OF fin, of v c Check_Proved env classify] by auto
  moreover have "s \<in> gamma_state (env v)" using node_sound s by blast
  ultimately show "truthy (aval c s)" using classify_proved by blast
qed

theorem classify_checks_refuted_sound:
  fixes gamma_state :: "'s \<Rightarrow> store set"
  assumes fin: "finite (intra g)"
    and mem: "(v, c, Check_Refuted) \<in> set (classify_checks g env classify)"
    and classify_refuted: "\<And>d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> \<not> truthy (aval c s)"
    and node_sound: "reach v <= gamma_state (env v)"
  shows "ALL s : reach v. ~ truthy (aval c s)"
proof
  fix s assume s: "s : reach v"
  have "classify c (env v) = Check_Refuted"
    using mem classify_checks_mem_iff[OF fin, of v c Check_Refuted env classify] by auto
  moreover have "s : gamma_state (env v)" using node_sound s by blast
  ultimately show "~ truthy (aval c s)" using classify_refuted by blast
qed

text \<open>
  State-carrying sibling of \<^const>\<open>classify_checks\<close>: the same traversal and
  classification, with the node's own abstract state attached to each entry.
  \<^const>\<open>classify_checks\<close> stays the soundness-critical primitive every domain
  cites directly; the projection lemma below shows this report is exactly that
  one with a fourth field added, so \<open>classify_checks_proved_sound\<close> and
  \<open>classify_checks_refuted_sound\<close> reach it through the projection without
  restatement.
\<close>

definition classify_checks_with_state ::
    "cfg \<Rightarrow> (pp \<Rightarrow> 's) \<Rightarrow> (exp \<Rightarrow> 's \<Rightarrow> check_result) \<Rightarrow> (pp \<times> exp \<times> check_result \<times> 's) list" where
  "classify_checks_with_state g env classify =
     map (\<lambda>(u, c, r). (u, c, r, env u)) (classify_checks g env classify)"

lemma classify_checks_with_state_proj [simp]:
  "map (\<lambda>(u, c, r, s). (u, c, r)) (classify_checks_with_state g env classify)
     = classify_checks g env classify"
proof -
  have "map (\<lambda>(u, c, r, s). (u, c, r)) (map (\<lambda>(u, c, r). (u, c, r, env u)) xs) = xs"
    for xs :: "check_report_entry list"
    by (induct xs) (auto split: prod.splits)
  then show ?thesis
    unfolding classify_checks_with_state_def by blast
qed

section \<open>Contextual check verdicts over a solved result table\<close>

text \<open>
  \<^const>\<open>classify_checks\<close> reads exactly one abstract state per checked node.
  A context-sensitive result has one state per \<open>(node, context)\<close> pair
  instead, and some of those pairs represent no concrete execution at all: a
  branch that is dead inside one activation, or an activation a node is never
  reached under. Classifying such a point against its stored state answers
  vacuously --- at an empty concretization every condition is both
  \<open>check_true\<close> and \<open>check_false\<close>, by \<open>check_true_false_vacuous\<close>
  --- so a verdict read there is evidence of nothing, and reporting it as
  \<^const>\<open>Check_Proved\<close> would fabricate a proof about executions that do not
  exist.

  \<open>contextual_verdict\<close> keeps that case outside \<^typ>\<open>check_result\<close> rather
  than folding it into one of its three values. \<open>Dead\<close> means ``no concrete
  execution is represented here''; it is neither \<^const>\<open>Check_Unknown\<close>, which
  does assert that something reaches this point and the abstraction failed to
  decide it, nor \<^const>\<open>Check_Proved\<close>.
\<close>

datatype contextual_verdict = Dead | Decided check_result

text \<open>
  The order mirrors \<^typ>\<open>'a point_state\<close>'s, for the same reason: \<open>Dead\<close> is
  least and neutral for \<^const>\<open>sup\<close>, and two decided verdicts join through
  \<^typ>\<open>check_result\<close>'s own flat join. Aggregating a node's contexts is then
  just \<^const>\<open>sup\<close> over the observations, and every case the source-level
  report needs falls out of that single operation: a node whose contexts are
  all dead stays \<open>Dead\<close>, a dead context beside a live one contributes
  nothing, and two live contexts that disagree collapse to
  \<^term>\<open>Decided Check_Unknown\<close>.
\<close>

instantiation contextual_verdict :: order
begin

fun less_eq_contextual_verdict :: "contextual_verdict \<Rightarrow> contextual_verdict \<Rightarrow> bool" where
  "less_eq_contextual_verdict Dead _ = True"
| "less_eq_contextual_verdict (Decided _) Dead = False"
| "less_eq_contextual_verdict (Decided a) (Decided b) = (a \<le> b)"

definition less_contextual_verdict :: "contextual_verdict \<Rightarrow> contextual_verdict \<Rightarrow> bool" where
  "less_contextual_verdict x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: contextual_verdict
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_contextual_verdict_def by (rule refl)
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) simp_all
qed

end

instantiation contextual_verdict :: bot
begin
definition bot_contextual_verdict :: contextual_verdict where
  "bot_contextual_verdict = Dead"
instance ..
end

lemma bot_contextual_verdict_eq [simp]: "(bot :: contextual_verdict) = Dead"
  unfolding bot_contextual_verdict_def by (rule refl)

instance contextual_verdict :: order_bot
  by standard (simp add: bot_contextual_verdict_def)

instantiation contextual_verdict :: semilattice_sup
begin

fun sup_contextual_verdict ::
  "contextual_verdict \<Rightarrow> contextual_verdict \<Rightarrow> contextual_verdict"
where
  "sup_contextual_verdict Dead y = y"
| "sup_contextual_verdict x Dead = x"
| "sup_contextual_verdict (Decided a) (Decided b) = Decided (a \<squnion> b)"

instance
proof
  fix x y z :: contextual_verdict
  show "x \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x" by (cases x; cases y; cases z) simp_all
qed

end

subsection \<open>Classifying one contextual point\<close>

text \<open>
  The reachability decision is not remade here: it was already made when the
  raw solved local unknown crossed the result boundary, one layer before
  \<^const>\<open>normalize_point\<close>'s own structural relabeling. A witness-bottom
  \<^const>\<open>Lifted\<close> payload is collapsed to \<^const>\<open>Bot\<close> by
  \<^const>\<open>canonicalize_lift\<close>, so by the time a value reaches
  \<^const>\<open>normalize_point\<close> --- as every public result adapter's raw value
  does --- \<^const>\<open>Bot\<close> and \<^const>\<open>Lifted\<close> already agree with concrete
  emptiness and non-emptiness respectively, and \<^const>\<open>Unreachable\<close> at the
  \<open>point_state\<close> level means exactly that. \<open>classify_point\<close> only refuses to
  classify against a state that represents nothing: a covered-but-dead
  activation, whose raw stored state a solver run could otherwise leave as
  a witness-bottom \<^const>\<open>Lifted\<close>, reaches \<open>classify_point\<close> as
  \<^const>\<open>Unreachable\<close> rather than fabricating a vacuous
  \<^const>\<open>Check_Proved\<close> off an empty state.
\<close>

fun classify_point ::
  "(exp \<Rightarrow> 'a \<Rightarrow> check_result) \<Rightarrow> exp \<Rightarrow> 'a point_state \<Rightarrow> contextual_verdict"
where
  "classify_point classify c Unreachable = Dead"
| "classify_point classify c (Reachable st) = Decided (classify c st)"

subsection \<open>Aggregating the contexts observed at one check\<close>

text \<open>
  Folding \<^const>\<open>sup\<close> from \<open>Dead\<close> over a finite set of observations, exactly
  as \<open>join_states_over\<close> folds the state join from \<^const>\<open>Unreachable\<close>. The
  fold's unit is the empty-set answer, so a check with no covered context
  needs no separate guard. The \<open>[code]\<close> equation is the usual
  \<open>comp_fun_idem\<close> transfer to a list fold: over an unordered set the value is
  well defined only because \<^const>\<open>sup\<close> is commutative, associative, and
  idempotent.
\<close>

definition aggregate_verdicts :: "contextual_verdict set \<Rightarrow> contextual_verdict" where
  "aggregate_verdicts vs = Finite_Set.fold sup Dead vs"

declare aggregate_verdicts_def [code del]

lemma aggregate_verdicts_code [code]:
  "aggregate_verdicts (set vs) = List.fold sup vs Dead"
proof -
  interpret ci: comp_fun_idem "sup :: contextual_verdict \<Rightarrow> _"
    by (rule comp_fun_idem_sup)
  show ?thesis unfolding aggregate_verdicts_def by (rule ci.fold_set_fold)
qed

lemma aggregate_verdicts_empty [simp]: "aggregate_verdicts {} = Dead"
  unfolding aggregate_verdicts_def by simp

lemma aggregate_verdicts_insert [simp]:
  "finite vs \<Longrightarrow> aggregate_verdicts (insert v vs) = v \<squnion> aggregate_verdicts vs"
proof -
  assume "finite vs"
  interpret ci: comp_fun_idem "sup :: contextual_verdict \<Rightarrow> _"
    by (rule comp_fun_idem_sup)
  show ?thesis
    unfolding aggregate_verdicts_def using \<open>finite vs\<close> by (simp add: ci.fold_insert_idem)
qed

text \<open>A check is dead exactly when every context observed at it is dead ---
  vacuously so when none is observed. Stated over the observations themselves
  rather than over the aggregate, and then shown to agree with it, so the two
  readings cannot drift.\<close>

lemma sup_contextual_verdict_eq_Dead_iff [simp]:
  "(x \<squnion> y = Dead) \<longleftrightarrow> x = Dead \<and> y = Dead"
  by (cases x; cases y) simp_all

lemma aggregate_verdicts_eq_Dead_iff:
  "finite vs \<Longrightarrow> aggregate_verdicts vs = Dead \<longleftrightarrow> (\<forall>v \<in> vs. v = Dead)"
proof (induct rule: finite_induct)
  case empty then show ?case by simp
next
  case (insert v vs) then show ?case by simp
qed

definition check_dead :: "('ctx \<times> contextual_verdict) set \<Rightarrow> bool" where
  "check_dead vs = (\<forall>(c, v) \<in> vs. v = Dead)"

lemma check_dead_empty [simp]: "check_dead {}"
  unfolding check_dead_def by simp

lemma check_dead_iff_aggregate:
  assumes "finite vs"
  shows "check_dead vs \<longleftrightarrow> aggregate_verdicts (snd ` vs) = Dead"
  unfolding check_dead_def
  using aggregate_verdicts_eq_Dead_iff[OF finite_imageI[OF assms, of snd]]
  by auto

text \<open>The lossy collapse back into \<^typ>\<open>check_result\<close>, for a consumer whose
  report type has no dead case. \<open>Dead\<close> becomes \<^const>\<open>Check_Unknown\<close>: of the
  three values it is the only one asserting nothing about the checked
  condition, so collapsing this way weakens the report rather than
  fabricating a verdict.\<close>

fun verdict_check_result :: "contextual_verdict \<Rightarrow> check_result" where
  "verdict_check_result Dead = Check_Unknown"
| "verdict_check_result (Decided r) = r"

text \<open>The opposite direction, for a report that has only one observation per
  check and therefore no dead case to distinguish: every entry is
  \<open>Decided\<close>. Deadness is not asserted either way --- such a report simply does
  not carry the channel that would express it.\<close>

definition decided_report ::
  "check_report_entry list \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "decided_report = map (\<lambda>(u, cnd, r). (u, cnd, Decided r))"

lemma length_decided_report [simp]: "length (decided_report rs) = length rs"
  unfolding decided_report_def by simp

subsection \<open>Whole-program contextual check report\<close>

text \<open>
  The context-sensitive sibling of \<^const>\<open>classify_checks\<close>: the same
  \<^const>\<open>EA_Check\<close> traversal in the same \<^const>\<open>cfg_intra_list\<close> order, but
  reading a \<^typ>\<open>('ctx, 'a) analysis_result\<close> instead of a single
  \<^typ>\<open>pp \<Rightarrow> 's\<close> environment, and retaining one verdict per context covered
  at the checked node rather than collapsing them at construction time.
  \<open>classify_checks_ctx_positions\<close> below is the load-bearing consequence: the
  node and condition columns coincide with \<^const>\<open>classify_checks\<close>'s, so a
  positional consumer pairing this report with the source's own check list
  stays aligned.

  The per-check observations are a set, not a list. \<^typ>\<open>'ctx\<close> carries no
  ordering constraint --- \<^const>\<open>contexts_at\<close> is a set for precisely that
  reason, and real context types such as interval vectors have no total
  order --- so no canonical list exists to produce. Nothing downstream needs
  one: \<^const>\<open>aggregate_verdicts\<close> is order-independent by construction.
\<close>

definition classify_checks_ctx ::
    "cfg \<Rightarrow> ('ctx, 'a) analysis_result \<Rightarrow> (exp \<Rightarrow> 'a \<Rightarrow> check_result)
       \<Rightarrow> (pp \<times> exp \<times> ('ctx \<times> contextual_verdict) set) list" where
  "classify_checks_ctx g r classify =
     map (\<lambda>(u, a, v). (u, ea_check_cond a,
            (\<lambda>ctx. (ctx, classify_point classify (ea_check_cond a) (lookup_context r u ctx)))
              ` contexts_at r u))
       (filter (\<lambda>(u, a, v). is_EA_Check a) (cfg_intra_list g))"

definition classify_checks_verdicts ::
    "cfg \<Rightarrow> ('ctx, 'a) analysis_result \<Rightarrow> (exp \<Rightarrow> 'a \<Rightarrow> check_result)
       \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "classify_checks_verdicts g r classify =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs))) (classify_checks_ctx g r classify)"

lemma classify_checks_verdicts_proj [simp]:
  "map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs))) (classify_checks_ctx g r classify)
     = classify_checks_verdicts g r classify"
  unfolding classify_checks_verdicts_def by (rule refl)

lemma classify_checks_ctx_positions:
  "map (\<lambda>(u, c, vs). (u, c)) (classify_checks_ctx g r classify)
     = map (\<lambda>(u, c, res). (u, c)) (classify_checks g env classify')"
  unfolding classify_checks_ctx_def classify_checks_def
  by (simp add: comp_def case_prod_beta)

lemma classify_checks_verdicts_positions:
  "map (\<lambda>(u, c, v). (u, c)) (classify_checks_verdicts g r classify)
     = map (\<lambda>(u, c, res). (u, c)) (classify_checks g env classify')"
  unfolding classify_checks_verdicts_def classify_checks_ctx_def classify_checks_def
  by (simp add: comp_def case_prod_beta)

lemma length_classify_checks_ctx:
  "length (classify_checks_ctx g r classify) = length (classify_checks g env classify')"
  unfolding classify_checks_ctx_def classify_checks_def by simp

lemma length_classify_checks_verdicts:
  "length (classify_checks_verdicts g r classify) = length (classify_checks g env classify')"
  unfolding classify_checks_verdicts_def classify_checks_ctx_def classify_checks_def by simp

text \<open>Membership unfolds to an \<^const>\<open>EA_Check\<close> edge at the entry's own source
  node, with that node's whole context fan-out attached --- the same shape
  \<open>classify_checks_mem_iff\<close> gives the context-insensitive report.\<close>

lemma classify_checks_ctx_mem_iff:
  assumes "finite (intra g)"
  shows "(v, c, vs) \<in> set (classify_checks_ctx g r classify)
     \<longleftrightarrow> (\<exists>tgt. (v, EA_Check c, tgt) \<in> intra g)
         \<and> vs = (\<lambda>ctx. (ctx, classify_point classify c (lookup_context r v ctx))) ` contexts_at r v"
  unfolding classify_checks_ctx_def set_map set_filter
  using set_cfg_intra_list[OF assms]
  by (auto simp: image_iff split: edge_action.splits)

subsection \<open>Contextual proved/refuted soundness\<close>

text \<open>
  The \<open>Decided Check_Proved\<close>/\<open>Decided Check_Refuted\<close> analogues of
  \<open>classify_checks_proved_sound\<close>/\<open>classify_checks_refuted_sound\<close>: an
  aggregated verdict of \<^term>\<open>Decided Check_Proved\<close> forces every observation
  folded into it to be \<^const>\<open>Dead\<close> or \<^term>\<open>Decided Check_Proved\<close> --- never
  a disagreeing \<^term>\<open>Decided Check_Refuted\<close> or \<^term>\<open>Decided Check_Unknown\<close>,
  since either would collapse the join to \<^term>\<open>Decided Check_Unknown\<close>
  instead. \<open>Dead\<close> observations contribute nothing and are filtered out at the
  call site, not here.
\<close>

lemma sup_check_result_eq_Check_Proved_iff [simp]:
  "(x \<squnion> y = Check_Proved) \<longleftrightarrow> x = Check_Proved \<and> y = Check_Proved"
  by (cases x; cases y) (simp_all add: sup_check_result_def)

lemma sup_check_result_eq_Check_Refuted_iff [simp]:
  "(x \<squnion> y = Check_Refuted) \<longleftrightarrow> x = Check_Refuted \<and> y = Check_Refuted"
  by (cases x; cases y) (simp_all add: sup_check_result_def)

lemma aggregate_verdicts_proved_dest:
  "finite vs \<Longrightarrow> aggregate_verdicts vs = Decided Check_Proved
     \<Longrightarrow> (\<forall>d \<in> vs. d = Dead \<or> d = Decided Check_Proved)"
proof (induct vs rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have agg_eq: "aggregate_verdicts (insert x F) = x \<squnion> aggregate_verdicts F"
    using insert.hyps(1) by (rule aggregate_verdicts_insert)
  with insert.prems have eq: "x \<squnion> aggregate_verdicts F = Decided Check_Proved" by simp
  consider (xDead) "x = Dead" | (xDec) cr where "x = Decided cr" by (cases x) auto
  then show ?case
  proof cases
    case xDead
    with eq have aggF: "aggregate_verdicts F = Decided Check_Proved" by simp
    show ?thesis
      using aggF insert.hyps(3) xDead by auto
  next
    case xDec
    consider (fDead) "aggregate_verdicts F = Dead"
      | (fDec) cr2 where "aggregate_verdicts F = Decided cr2" by (cases "aggregate_verdicts F") auto
    then show ?thesis
    proof cases
      case fDead
      with eq xDec have "cr = Check_Proved" by simp
      moreover have "\<forall>d \<in> F. d = Dead"
        using fDead insert.hyps(1) aggregate_verdicts_eq_Dead_iff by blast
      ultimately show ?thesis using xDec by auto
    next
      case fDec
      with eq xDec have "cr = Check_Proved \<and> cr2 = Check_Proved" by simp
      hence aggF: "aggregate_verdicts F = Decided Check_Proved" using fDec by simp
      show ?thesis
        using \<open>(cr::check_result) = Check_Proved \<and> (cr2::check_result) = Check_Proved\<close> fDec
          insert.hyps(3) xDec by auto
    qed
  qed
qed

lemma aggregate_verdicts_refuted_dest:
  "finite vs \<Longrightarrow> aggregate_verdicts vs = Decided Check_Refuted
     \<Longrightarrow> (\<forall>d \<in> vs. d = Dead \<or> d = Decided Check_Refuted)"
proof (induct vs rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have agg_eq: "aggregate_verdicts (insert x F) = x \<squnion> aggregate_verdicts F"
    using insert.hyps(1) by (rule aggregate_verdicts_insert)
  with insert.prems have eq: "x \<squnion> aggregate_verdicts F = Decided Check_Refuted" by simp
  consider (xDead) "x = Dead" | (xDec) cr where "x = Decided cr" by (cases x) auto
  then show ?case
  proof cases
    case xDead
    with eq have aggF: "aggregate_verdicts F = Decided Check_Refuted" by simp
    show ?thesis
      using aggF insert.hyps(3) xDead by auto
  next
    case xDec
    consider (fDead) "aggregate_verdicts F = Dead"
      | (fDec) cr2 where "aggregate_verdicts F = Decided cr2" by (cases "aggregate_verdicts F") auto
    then show ?thesis
    proof cases
      case fDead
      with eq xDec have "cr = Check_Refuted" by simp
      moreover have "\<forall>d \<in> F. d = Dead"
        using fDead insert.hyps(1) aggregate_verdicts_eq_Dead_iff by blast
      ultimately show ?thesis using xDec by auto
    next
      case fDec
      with eq xDec have "cr = Check_Refuted \<and> cr2 = Check_Refuted" by simp
      hence aggF: "aggregate_verdicts F = Decided Check_Refuted" using fDec by simp
      show ?thesis
        using \<open>(cr::check_result) = Check_Refuted \<and> (cr2::check_result) = Check_Refuted\<close>
          aggF insert.hyps(3) xDec by auto
    qed
  qed
qed

text \<open>
  The context-indexed report analogue of \<open>classify_checks_proved_sound\<close>/
  \<open>classify_checks_refuted_sound\<close>: an aggregated \<^term>\<open>Decided Check_Proved\<close>/
  \<^term>\<open>Decided Check_Refuted\<close> verdict at a check forces the classifier's own
  reading at every \<^const>\<open>Reachable\<close> context to agree. The image set being
  folded is shown finite from the aggregate equation itself
  (\<open>Finite_Set.fold_infinite\<close>: an infinite carrier folds to the identity
  \<open>Dead\<close>, which a \<^term>\<open>Decided Check_Proved\<close>/\<open>Decided Check_Refuted\<close> result
  already rules out), so no separate finiteness assumption on the covered
  contexts is needed.
\<close>

theorem classify_checks_ctx_proved_sound:
  assumes fin: "finite (intra g)"
    and mem: "(v, c, Decided Check_Proved) \<in> set (classify_checks_verdicts g r classify)"
    and reach: "lookup_context r v ctx = Reachable st"
  shows "classify c st = Check_Proved"
proof -
  obtain vs where mem_ctx: "(v, c, vs) \<in> set (classify_checks_ctx g r classify)"
    and agg0: "aggregate_verdicts (snd ` vs) = Decided Check_Proved"
    using mem unfolding classify_checks_verdicts_def set_map by (force simp: image_iff)
  obtain tgt where vs_eq: "vs = (\<lambda>c'. (c', classify_point classify c (lookup_context r v c'))) ` contexts_at r v"
    using mem_ctx classify_checks_ctx_mem_iff[OF fin] by blast
  have agg: "aggregate_verdicts ((\<lambda>c'. classify_point classify c (lookup_context r v c')) ` contexts_at r v)
               = Decided Check_Proved"
    using agg0 unfolding vs_eq by (simp add: image_comp comp_def)
  have fin_img: "finite ((\<lambda>c'. classify_point classify c (lookup_context r v c')) ` contexts_at r v)"
  proof (rule ccontr)
    assume "\<not> finite ((\<lambda>c'. classify_point classify c (lookup_context r v c')) ` contexts_at r v)"
    hence "aggregate_verdicts
             ((\<lambda>c'. classify_point classify c (lookup_context r v c')) ` contexts_at r v) = Dead"
      unfolding aggregate_verdicts_def by (rule Finite_Set.fold_infinite)
    with agg show False by simp
  qed
  have covctx: "ctx \<in> contexts_at r v"
  proof (rule ccontr)
    assume "ctx \<notin> contexts_at r v"
    then have "(v, ctx) \<notin> result_keys r" by simp
    then have "lookup_context r v ctx = Unreachable" by (rule lookup_context_absent)
    with reach show False
      by fastforce
  qed
  have mem_img: "classify_point classify c (lookup_context r v ctx)
          \<in> (\<lambda>c'. classify_point classify c (lookup_context r v c')) ` contexts_at r v"
    using covctx by blast
  have "classify_point classify c (lookup_context r v ctx) = Dead
          \<or> classify_point classify c (lookup_context r v ctx) = Decided Check_Proved"
    using aggregate_verdicts_proved_dest[OF fin_img agg] mem_img by blast
  with reach show ?thesis by simp
qed

theorem classify_checks_ctx_refuted_sound:
  assumes fin: "finite (intra g)"
    and mem: "(v, c, Decided Check_Refuted) \<in> set (classify_checks_verdicts g r classify)"
    and reach: "lookup_context r v ctx = Reachable st"
  shows "classify c st = Check_Refuted"
proof -
  obtain vs where mem_ctx: "(v, c, vs) \<in> set (classify_checks_ctx g r classify)"
    and agg0: "aggregate_verdicts (snd ` vs) = Decided Check_Refuted"
    using mem unfolding classify_checks_verdicts_def set_map by (force simp: image_iff)
  obtain tgt where vs_eq: "vs = (\<lambda>c'. (c', classify_point classify c (lookup_context r v c'))) ` contexts_at r v"
    using mem_ctx classify_checks_ctx_mem_iff[OF fin] by blast
  have agg: "aggregate_verdicts ((\<lambda>c'. classify_point classify c (lookup_context r v c')) ` contexts_at r v)
               = Decided Check_Refuted"
    using agg0 unfolding vs_eq by (simp add: image_comp comp_def)
  have fin_img: "finite ((\<lambda>c'. classify_point classify c (lookup_context r v c')) ` contexts_at r v)"
  proof (rule ccontr)
    assume "\<not> finite ((\<lambda>c'. classify_point classify c (lookup_context r v c')) ` contexts_at r v)"
    hence "aggregate_verdicts
             ((\<lambda>c'. classify_point classify c (lookup_context r v c')) ` contexts_at r v) = Dead"
      unfolding aggregate_verdicts_def by (rule Finite_Set.fold_infinite)
    with agg show False by simp
  qed
  have covctx: "ctx \<in> contexts_at r v"
  proof (rule ccontr)
    assume "ctx \<notin> contexts_at r v"
    then have "(v, ctx) \<notin> result_keys r" by simp
    then have "lookup_context r v ctx = Unreachable" by (rule lookup_context_absent)
    with reach show False by simp
  qed
  have mem_img: "classify_point classify c (lookup_context r v ctx)
          \<in> (\<lambda>c'. classify_point classify c (lookup_context r v c')) ` contexts_at r v"
    using covctx by blast
  have "classify_point classify c (lookup_context r v ctx) = Dead
          \<or> classify_point classify c (lookup_context r v ctx) = Decided Check_Refuted"
    using aggregate_verdicts_refuted_dest[OF fin_img agg] mem_img by blast
  with reach show ?thesis by simp
qed

end

