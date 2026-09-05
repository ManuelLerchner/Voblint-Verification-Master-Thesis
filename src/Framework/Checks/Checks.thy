theory Checks
  imports "Voblint_Domain.Abstract_Domain" "Voblint_VIMP.VIMP_Expr" "Voblint_CFG.CFG_Def"
begin

section \<open>Ordinary assertion checks: store-only, no ghost-domain or
  additional trace-projection dependency\<close>

text \<open>
  A check table relates program points to the boolean conditions placed
  there; several checks may share one point. \<open>checks_proven\<close> states that
  every concrete store the caller's reachable-store function admits at a
  checked point satisfies that point's condition. The reachable-store
  function is left abstract (\<open>pp \<Rightarrow> store set\<close>) so an instance supplies
  whatever collecting semantics its own \<open>sound_dg_spec_core\<close> interpretation
  already proves sound: this theory adds no new soundness anchor, only the
  store-level check layer on top of an existing one.

  The table's shape, \<open>(pp \<times> exp) set\<close>, matches \<^const>\<open>checks\<close> --- the
  \<^type>\<open>cfg\<close> record field the compiler populates from the \<open>EA_Check\<close> edges it
  emits --- directly: a caller instantiates \<open>ck\<close> with
  \<open>checks g\<close> for a compiled \<open>g\<close>, not with a hand-built table.
\<close>

type_synonym checks = "(pp \<times> exp) set"

definition checks_proven :: "checks \<Rightarrow> (pp \<Rightarrow> store set) \<Rightarrow> bool" where
  "checks_proven ck reach \<longleftrightarrow> (\<forall>v c. (v, c) \<in> ck \<longrightarrow> (\<forall>s \<in> reach v. truthy (aval c s)))"

lemma checks_provenI [intro]:
  "(\<And>v c s. (v, c) \<in> ck \<Longrightarrow> s \<in> reach v \<Longrightarrow> truthy (aval c s)) \<Longrightarrow> checks_proven ck reach"
  unfolding checks_proven_def by blast

text \<open>The one-step destruction dual of \<open>checks_provenI\<close>, so a caller with a
  \<open>checks_proven\<close> fact in hand reaches the store-level conclusion without
  unfolding the definition. It carries no soundness content of its own, and is
  named for what it is rather than \<open>_sound\<close>: the real soundness work happens
  where a caller establishes \<open>checks_proven\<close> for a concrete \<open>reach\<close>, by
  composing this theory with an existing \<open>ltr_collect \<le> gamma_state(\<dots>)\<close>-shaped
  corollary; this theory never states or proves that inclusion itself.\<close>

lemma checks_provenD [dest]:
  assumes proven: "checks_proven ck reach"
    and at_v: "(v, c) \<in> ck"
    and mem: "s \<in> reach v"
  shows "truthy (aval c s)"
  using proven at_v mem unfolding checks_proven_def by blast

end
