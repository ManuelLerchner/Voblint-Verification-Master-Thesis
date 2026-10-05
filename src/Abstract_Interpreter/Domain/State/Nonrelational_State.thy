theory Nonrelational_State
  imports Abstract_Domain State_Concretization
begin

section \<open>What a store of one abstract value per variable denotes, and when it denotes nothing\<close>

text \<open>
  A non-relational abstract state, \<open>'a abs_state\<close>, pairs every program
  variable with one abstract value, independently of every other variable
  -- the "non-relational" in the name. \<open>gamma_state\<close> says what that
  pairing denotes: exactly the concrete stores where each variable's value
  lies in its own component's concretization, i.e. the product of the
  per-component concretizations. Because that product is a conjunction over
  every variable, one witness-bottom component -- one variable whose
  abstract value denotes no concrete value at all -- already makes the
  whole state denote nothing, regardless of what every other component
  holds. \<open>is_empty_state\<close> names that witness-bottom condition directly,
  so a generic transfer dispatcher can detect and canonicalize it without
  testing \<open>gamma_state\<close> against the empty set at run time.
\<close>

type_synonym 'a abs_state = "vname => 'a"

(* HOL ships fun :: (type, bounded_lattice) bounded_lattice but not this
   weaker pointwise instance; abs_state needs it for TD_side part_post_solution. *)
instance "fun" :: (type, bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

text \<open>Pointwise join on abstract states is idempotent because the value-domain
  semilattice structure lifts pointwise.  Finite folds can therefore use the
  standard idempotent-join laws without a separate state-level assumption.\<close>
subsection \<open>State concretization\<close>

definition gamma_state :: "('a::numeric_domain) abs_state \<Rightarrow> store set" where
  "gamma_state d = {s. \<forall>x. s x \<in> \<gamma> (d x)}"

adhoc_overloading gamma_S == gamma_state

lemma gamma_stateI [intro]:
  "(\<And>x. s x \<in> \<gamma> (d x)) \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>"
  unfolding gamma_state_def by simp

(* Note: pointwise bot / sup on 'a abs_state come from HOL's
   fun :: bot and fun :: sup instances; no extra definitions needed. *)

subsection \<open>State concretization laws\<close>

text \<open>Every value-level concretization law, lifted to states.  All of them fall out
  pointwise, which is exactly what makes a nonrelational state cheap: order, bottom and join
  are read one variable at a time, and no law here needs a relation between variables.\<close>
lemma gamma_state_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> \<lbrakk>sigma1\<rbrakk> \<subseteq> \<lbrakk>sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::numeric_domain abs_state"
  unfolding gamma_state_def le_fun_def
  using gamma_mono by blast

lemma gamma_state_bot [simp]:
  "\<lbrakk>bot :: 'a::numeric_domain abs_state\<rbrakk> = {}"
  unfolding gamma_state_def bot_fun_def using gamma_bot by auto

lemma gamma_state_sup_ub1 [intro]:
  "\<lbrakk>sigma1\<rbrakk> \<subseteq> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::numeric_domain abs_state"
  unfolding gamma_state_def sup_fun_def
  using gamma_sup_ub1 by blast

lemma gamma_state_sup_ub2 [intro]:
  "\<lbrakk>sigma2\<rbrakk> \<subseteq> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::numeric_domain abs_state"
  unfolding gamma_state_def sup_fun_def
  using gamma_sup_ub2 by blast

text \<open>
  Membership counterparts of \<open>gamma_state_sup_ub1\<close>/\<open>gamma_state_sup_ub2\<close>,
  for citing at a witness \<open>s\<close> directly (\<open>using subsetD[OF gamma_state_sup_ub1 h]\<close>
  otherwise repeats the same \<open>subsetD\<close> wrapper at every call site).
  \<open>[intro]\<close>: their conclusion has the distinctive
  \<open>s \<in> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>\<close> shape a join-injection goal actually has, and a
  witness already in one side's concretization is exactly the natural way to
  discharge it.
\<close>

lemma gamma_state_supI1 [intro]:
  "s \<in> \<lbrakk>sigma1\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::numeric_domain abs_state"
  using gamma_state_sup_ub1 by blast

lemma gamma_state_supI2 [intro]:
  "s \<in> \<lbrakk>sigma2\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::numeric_domain abs_state"
  using gamma_state_sup_ub2 by blast

text \<open>
  Left bare rather than \<open>[dest]\<close>: \<open>x\<close> is unconstrained by the premise, so a
  global destruction rule here would let \<open>auto\<close> pick a schematic variable
  unrelated to the goal at hand (as with the \<open>Voblint_Solver\<close> session's
  \<open>env_indep_depsD\<close>). Cite it explicitly with the variable the goal needs.
\<close>
lemma gamma_stateD:
  "s \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> s x \<in> \<gamma> (d x)"
  for d :: "'a::numeric_domain abs_state"
  unfolding gamma_state_def by simp

subsection \<open>Witness-bottom abstract states\<close>

text \<open>
  Witness-bottom is not "the state has exactly one empty component": any
  number of a state's components can independently denote the empty set of
  concrete integers at once, and \<open>is_empty_state\<close> does not distinguish those
  cases from each other or count them. It only asks whether at least one
  witness exists (\<open>\<exists>x. is_empty (d x)\<close>), because one witness already
  suffices -- \<open>gamma_state\<close>'s product structure means a single empty
  component collapses the whole state's concretization to the empty set of
  stores, so a second, third, or every remaining empty component would only
  reconfirm what the first already decided.

  \<open>is_empty_state\<close> is a logical characterization of that condition, not an
  executable test: \<open>'a abs_state\<close> is a raw function \<open>vname \<Rightarrow> 'a\<close>, and
  \<^typ>\<open>vname\<close> is infinite, so \<open>\<exists>x. is_empty (d x)\<close> has no code equation --
  there is no finite witness search for code generation to compile. The
  finite executable bottom test a real dispatcher runs is \<open>default_st_is_bot_for\<close>,
  defined downstream in the \<open>Voblint_Exec\<close> session, which scans only the
  state's finitely many stored locations and is proved to agree with
  \<open>is_empty_state\<close> on every such state.
\<close>

definition is_empty_state :: "('a::executable_domain) abs_state \<Rightarrow> bool" where
  "is_empty_state d = (\<exists>x. is_empty (d x))"

lemma is_empty_stateI [intro]:
  "is_empty (d x) \<Longrightarrow> is_empty_state d"
  unfolding is_empty_state_def by (rule exI)

lemma is_empty_stateE [elim]:
  assumes "is_empty_state d"
  obtains x where "is_empty (d x)"
  using assms unfolding is_empty_state_def by blast

text \<open>
  Overwriting one variable of a state that is not already empty can only make
  it empty through the written element.  This is what lets an incremental
  emptiness check inspect the freshly computed element alone instead of
  searching the infinite variable space again.
\<close>

lemma is_empty_state_fun_upd_iff:
  assumes "\<not> is_empty_state d"
  shows "is_empty_state (d(x := a)) \<longleftrightarrow> is_empty a"
proof
  assume "is_empty_state (d(x := a))"
  then obtain y where "is_empty ((d(x := a)) y)"
    by (rule is_empty_stateE)
  with assms show "is_empty a"
    by (cases "y = x") auto
next
  assume "is_empty a"
  then have "is_empty ((d(x := a)) x)" by simp
  then show "is_empty_state (d(x := a))"
    by (rule is_empty_stateI)
qed

lemma is_empty_state_gamma_state_empty:
  assumes "is_empty_state d"
  shows "\<lbrakk>d\<rbrakk> = {}"
proof -
  obtain x where "is_empty (d x)" using assms by (rule is_empty_stateE)
  then show ?thesis
    using gamma_stateD[of _ d x] unfolding is_empty_correct by fastforce
qed

lemma gamma_state_empty_is_empty_state:
  assumes "\<lbrakk>d\<rbrakk> = {}"
  shows "is_empty_state d"
proof (rule ccontr)
  assume "\<not> is_empty_state d"
  then have nonempty: "\<And>x. \<exists>v. v \<in> \<gamma> (d x)"
    unfolding is_empty_state_def using is_empty_correct by blast
  define s where "s = (\<lambda>x. SOME v. v \<in> \<gamma> (d x))"
  have s_prop: "s x \<in> \<gamma> (d x)" for x
    unfolding s_def using nonempty[of x] by (rule someI_ex)
  then have "s \<in> \<lbrakk>d\<rbrakk>"
    unfolding gamma_state_def by simp
  with assms show False by simp
qed

lemma is_empty_state_iff_gamma_state_empty:
  "is_empty_state d \<longleftrightarrow> \<lbrakk>d\<rbrakk> = {}"
  using is_empty_state_gamma_state_empty gamma_state_empty_is_empty_state by blast

lemma exact_emptiness_is_empty_state:
  "exact_emptiness is_empty_state (gamma_state :: 'a::numeric_domain abs_state \<Rightarrow> store set)"
  by (rule exact_emptinessI) (rule is_empty_state_iff_gamma_state_empty)

lemma is_empty_state_bot [simp]:
  "is_empty_state (bot :: 'a::numeric_domain abs_state)"
  unfolding is_empty_state_def bot_fun_def
  using is_empty_correct gamma_bot by blast

lemma is_empty_state_antimono:
  "d1 \<le> d2 \<Longrightarrow> is_empty_state d2 \<Longrightarrow> is_empty_state d1"
  for d1 d2 :: "'a::numeric_domain abs_state"
  unfolding is_empty_state_def le_fun_def using is_empty_antimono by blast

end
