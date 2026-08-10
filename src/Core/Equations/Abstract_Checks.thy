theory Abstract_Checks
  imports Checks CFG_Enumeration "Voblint_Core.Abstract_Numeric_Queries"
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
  assumes aval_abs_sound[intro]:
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

section \<open>Whole-program executable check report\<close>

text \<open>
  A single, domain-generic report over every compiled \<^const>\<open>EA_Check\<close> edge:
  one entry per check, at its own source node, classified by whatever
  \<open>classify\<close> function a domain supplies (\<open>sign_classify_check\<close> and its
  siblings, or \<open>abstract_check_domain.classify_check\<close> generically). Entries
  are read directly off \<^const>\<open>intra\<close> through the same deterministic order
  \<^const>\<open>cfg_intra_list\<close> already gives the TD bridge, rather than sorting
  \<^typ>\<open>pp\<close> or \<^typ>\<open>bexp\<close> values by hand: a compiled \<^const>\<open>checks\<close> table has
  exactly the same \<^const>\<open>EA_Check\<close> edges as its source, by construction, so
  this report is a second view of that one representation, not a parallel
  table.
\<close>

type_synonym check_report_entry = "pp \<times> bexp \<times> check_result"

definition classify_checks ::
    "cfg \<Rightarrow> (pp \<Rightarrow> 's) \<Rightarrow> (bexp \<Rightarrow> 's \<Rightarrow> check_result) \<Rightarrow> check_report_entry list" where
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
    and classify_proved: "\<And>d s. classify c d = Check_Proved \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> bval c s"
    and node_sound: "reach v \<le> gamma_state (env v)"
  shows "\<forall>s \<in> reach v. bval c s"
proof
  fix s assume s: "s \<in> reach v"
  have "classify c (env v) = Check_Proved"
    using mem classify_checks_mem_iff[OF fin, of v c Check_Proved env classify] by auto
  moreover have "s \<in> gamma_state (env v)" using node_sound s by blast
  ultimately show "bval c s" using classify_proved by blast
qed

theorem classify_checks_refuted_sound:
  fixes gamma_state :: "'s \<Rightarrow> store set"
  assumes fin: "finite (intra g)"
    and mem: "(v, c, Check_Refuted) \<in> set (classify_checks g env classify)"
    and classify_refuted: "\<And>d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> \<not> bval c s"
    and node_sound: "reach v <= gamma_state (env v)"
  shows "ALL s : reach v. ~ bval c s"
proof
  fix s assume s: "s : reach v"
  have "classify c (env v) = Check_Refuted"
    using mem classify_checks_mem_iff[OF fin, of v c Check_Refuted env classify] by auto
  moreover have "s : gamma_state (env v)" using node_sound s by blast
  ultimately show "~ bval c s" using classify_refuted by blast
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
    "cfg \<Rightarrow> (pp \<Rightarrow> 's) \<Rightarrow> (bexp \<Rightarrow> 's \<Rightarrow> check_result) \<Rightarrow> (pp \<times> bexp \<times> check_result \<times> 's) list" where
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

end

