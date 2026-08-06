theory Checks
  imports Abstract_Domain "Voblint_VIMP.VIMP_Expr"
begin

section \<open>Ordinary assertion checks: store-only, no ghost-domain or
  additional trace-projection dependency\<close>

text \<open>
  A check table relates program points to the boolean conditions placed
  there; several checks may share one point. \<open>checks_proven\<close> states that
  every concrete store the caller's reachable-store function admits at a
  checked point satisfies that point's condition. The reachable-store
  function is left abstract (\<open>pp \<Rightarrow> store set\<close>) so an instance supplies
  whatever collecting semantics its own \<open>sound_dg_spec\<close> or \<open>sound_dg_hooks\<close>
  interpretation already proves sound: this theory adds no new soundness
  anchor, only the store-level check layer on top of an existing one.

  The table's shape, \<open>(pp \<times> bexp) set\<close>, matches \<^const>\<open>checks\<close> --- the
  \<^type>\<open>cfg\<close> record field a real compiler populates (\<open>collect_checks_prog\<close>,
  \<open>VIMP_Proc_to_CFG.thy\<close>) --- directly: a caller instantiates \<open>ck\<close> with
  \<open>checks g\<close> for a compiled \<open>g\<close>, not with a hand-built table.
\<close>

type_synonym checks = "(pp \<times> bexp) set"

definition checks_proven :: "checks \<Rightarrow> (pp \<Rightarrow> store set) \<Rightarrow> bool" where
  "checks_proven ck reach \<longleftrightarrow> (\<forall>v c. (v, c) \<in> ck \<longrightarrow> (\<forall>s \<in> reach v. bval c s))"

lemma checks_provenI [intro]:
  "(\<And>v c s. (v, c) \<in> ck \<Longrightarrow> s \<in> reach v \<Longrightarrow> bval c s) \<Longrightarrow> checks_proven ck reach"
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
    and at_v: "(v, c) \<in> ck"
    and mem: "s \<in> reach v"
  shows "bval c s"
  using proven at_v mem unfolding checks_proven_def by blast

end
