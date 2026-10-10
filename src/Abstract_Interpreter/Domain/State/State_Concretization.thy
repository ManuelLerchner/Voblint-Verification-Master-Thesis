theory State_Concretization
  imports "Voblint_VIMP.VIMP_Syntax" Abstract_Domain
begin

section \<open>The stores an abstract state describes\<close>

text \<open>
  Every kind of abstract state, pointwise or relational, denotes a set of
  stores. \<open>\<gamma> d\<close> is that set for every state type: each state theory
  registers its own concretization under this one constant with
  \<open>adhoc_overloading\<close>, and the type of \<open>d\<close> selects it.
\<close>

text \<open>The class parameter \<^const>\<open>gamma\<close> gives up its own notation here, so that \<open>\<gamma>\<close>
  has exactly one production in every theory that sees this one.\<close>

no_notation gamma ("\<gamma>")

consts gamma_S :: "'s \<Rightarrow> 'v set" ("\<gamma>")

adhoc_overloading gamma_S == gamma

text \<open>
  An executable state is read back as the abstract state it represents, given the
  classifier that tells locals from globals. \<open>readback \<G> x\<close> is that reading for
  every executable representation, registered the same way, so a concretization of an
  executable state is \<open>\<gamma> (readback \<G> x)\<close> whatever its representation. Its notation
  \<open>\<rho>\<^bsub>\<G>\<^esub> x\<close> is opt-in, in the bundle \<open>default_st_syntax\<close>.
\<close>

consts readback :: "(vname \<Rightarrow> bool) \<Rightarrow> 'e \<Rightarrow> 'a"

end
