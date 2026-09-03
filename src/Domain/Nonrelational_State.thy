theory Nonrelational_State
  imports Abstract_Domain "Voblint_VIMP.VIMP_Syntax"
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
lemma join_state_comp_fun_idem:
  "comp_fun_idem ((\<squnion>) ::
     'a::semilattice_sup abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  by (rule comp_fun_idem_sup)

subsection \<open>State concretization\<close>

definition gamma_state :: "('a::sound_domain) abs_state \<Rightarrow> store set" ("\<lbrakk>_\<rbrakk>") where
  "gamma_state \<sigma> = {s. \<forall>x. s x \<in> gamma (\<sigma> x)}"

lemma gamma_stateI [intro]:
  "(\<And>x. s x \<in> gamma (\<sigma> x)) \<Longrightarrow> s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  unfolding gamma_state_def by simp

(* Note: pointwise bot / sup on 'a abs_state come from HOL's
   fun :: bot and fun :: sup instances; no extra definitions needed. *)

subsection \<open>State concretization laws\<close>

lemma gamma_state_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> \<lbrakk>sigma1\<rbrakk> \<subseteq> \<lbrakk>sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::sound_domain abs_state"
  unfolding gamma_state_def le_fun_def
  using gamma_mono by blast

lemma gamma_state_bot [simp]:
  "\<lbrakk>bot :: 'a::sound_domain abs_state\<rbrakk> = {}"
  unfolding gamma_state_def bot_fun_def using gamma_bot by auto

lemma gamma_state_sup_ub1 [intro]:
  "\<lbrakk>sigma1\<rbrakk> \<subseteq> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::sound_domain abs_state"
  unfolding gamma_state_def sup_fun_def
  using gamma_sup_ub1 by blast

lemma gamma_state_sup_ub2 [intro]:
  "\<lbrakk>sigma2\<rbrakk> \<subseteq> \<lbrakk>sigma1 \<squnion> sigma2\<rbrakk>"
  for sigma1 sigma2 :: "'a::sound_domain abs_state"
  unfolding gamma_state_def sup_fun_def
  using gamma_sup_ub2 by blast

(* The pointwise projection gamma_state_def unfolds to; downstream proofs
   cite this instead of re-unfolding the definition at each site. *)
lemma gamma_stateD [dest]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s x \<in> gamma (\<sigma> x)"
  for \<sigma> :: "'a::sound_domain abs_state"
  unfolding gamma_state_def by simp

subsection \<open>Witness-bottom abstract states\<close>

text \<open>
  Witness-bottom is not "the state has exactly one empty component": any
  number of a state's components can independently denote the empty set of
  concrete integers at once, and \<open>is_empty_state\<close> does not distinguish those
  cases from each other or count them. It only asks whether at least one
  witness exists (\<open>\<exists>x. is_empty (\<sigma> x)\<close>), because one witness already
  suffices -- \<open>gamma_state\<close>'s product structure means a single empty
  component collapses the whole state's concretization to the empty set of
  stores, so a second, third, or every remaining empty component would only
  reconfirm what the first already decided. This is why an executable
  dispatcher can stop scanning at the first witness it finds instead of
  first ruling out, or counting, any others.
\<close>

definition is_empty_state :: "('a::executable_domain) abs_state \<Rightarrow> bool" where
  "is_empty_state \<sigma> = (\<exists>x. is_empty (\<sigma> x))"

lemma is_empty_stateI [intro]:
  "is_empty (\<sigma> x) \<Longrightarrow> is_empty_state \<sigma>"
  unfolding is_empty_state_def by (rule exI)

lemma is_empty_stateE [elim]:
  assumes "is_empty_state \<sigma>"
  obtains x where "is_empty (\<sigma> x)"
  using assms unfolding is_empty_state_def by blast

lemma is_empty_state_gamma_state_empty:
  assumes "is_empty_state \<sigma>"
  shows "\<lbrakk>\<sigma>\<rbrakk> = {}"
  using assms is_empty_correct by fastforce

lemma gamma_state_empty_is_empty_state:
  assumes "\<lbrakk>\<sigma>\<rbrakk> = {}"
  shows "is_empty_state \<sigma>"
proof (rule ccontr)
  assume "\<not> is_empty_state \<sigma>"
  then have nonempty: "\<And>x. \<exists>v. v \<in> gamma (\<sigma> x)"
    unfolding is_empty_state_def using is_empty_correct by blast
  define s where "s = (\<lambda>x. SOME v. v \<in> gamma (\<sigma> x))"
  have s_prop: "s x \<in> gamma (\<sigma> x)" for x
    unfolding s_def using nonempty[of x] by (rule someI_ex)
  then have "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
    unfolding gamma_state_def by simp
  with assms show False by simp
qed

lemma is_empty_state_iff_gamma_state_empty:
  "is_empty_state \<sigma> \<longleftrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
  using is_empty_state_gamma_state_empty gamma_state_empty_is_empty_state by blast

lemma is_empty_state_bot [simp]:
  "is_empty_state (bot :: 'a::sound_domain abs_state)"
  unfolding is_empty_state_def bot_fun_def
  using is_empty_correct gamma_bot by blast

text \<open>
  A concrete witness rules out witness-bottom directly: the generic dispatcher's
  short-circuit condition can never fire on an abstract state some reachable
  concrete store still belongs to.
\<close>
lemma gamma_state_witness_not_bot:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> \<not> is_empty_state \<sigma>"
  using is_empty_state_gamma_state_empty by blast

lemma is_empty_state_antimono:
  "\<sigma>1 \<le> \<sigma>2 \<Longrightarrow> is_empty_state \<sigma>2 \<Longrightarrow> is_empty_state \<sigma>1"
  for \<sigma>1 \<sigma>2 :: "'a::sound_domain abs_state"
  unfolding is_empty_state_def le_fun_def using is_empty_antimono by blast

end
