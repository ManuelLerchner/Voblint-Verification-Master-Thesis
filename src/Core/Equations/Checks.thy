theory Checks
  imports Abstract_Domain "Voblint_VIMP.VIMP_Expr"
begin

section \<open>Ordinary assertion checks: store-only, no ghost-domain or
  additional trace-projection dependency\<close>

text \<open>
  A check table assigns an optional boolean condition to each program point;
  \<open>None\<close> means no assertion is placed there. \<open>checks_proven\<close> states that
  every concrete store the caller's reachable-store function admits at a
  checked point satisfies that point's condition. The reachable-store
  function is left abstract (\<open>pp \<Rightarrow> store set\<close>) so an instance supplies
  whatever collecting semantics its own \<open>sound_dg_spec\<close> or \<open>sound_dg_hooks\<close>
  interpretation already proves sound: this theory adds no new soundness
  anchor, only the store-level check layer on top of an existing one.
\<close>

type_synonym checks = "pp \<Rightarrow> bexp option"

definition checks_proven :: "checks \<Rightarrow> (pp \<Rightarrow> store set) \<Rightarrow> bool" where
  "checks_proven ck reach \<longleftrightarrow> (\<forall>v c. ck v = Some c \<longrightarrow> (\<forall>s \<in> reach v. bval c s))"

lemma checks_provenI [intro]:
  "(\<And>v c s. ck v = Some c \<Longrightarrow> s \<in> reach v \<Longrightarrow> bval c s) \<Longrightarrow> checks_proven ck reach"
  unfolding checks_proven_def by blast

text \<open>\<open>checks_proven_sound\<close> is a thin extraction from \<open>checks_proven\<close> --- named
  and tagged \<open>[dest]\<close> so call sites cite it instead of unfolding the
  definition, not because it carries new soundness content itself. The real
  soundness work happens where a caller establishes \<open>checks_proven\<close> for a
  concrete \<open>reach\<close>, by composing this theory with an existing
  \<open>ltr_collect \<le> gamma_state(\<dots>)\<close>-shaped corollary; this theory never states
  or proves that inclusion itself.\<close>
lemma checks_proven_sound [dest]:
  assumes proven: "checks_proven ck reach"
    and at_v: "ck v = Some c"
    and mem: "s \<in> reach v"
  shows "bval c s"
  using proven at_v mem unfolding checks_proven_def by blast

end
