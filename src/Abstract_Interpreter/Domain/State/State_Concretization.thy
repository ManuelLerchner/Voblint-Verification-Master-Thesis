theory State_Concretization
  imports "Voblint_VIMP.VIMP_Syntax"
begin

section \<open>The stores an abstract state describes\<close>

text \<open>
  Every kind of abstract state, pointwise or relational, denotes a set of
  stores. \<open>\<lbrakk>d\<rbrakk>\<close> is that set for every state type: each state theory
  registers its own concretization under this one constant with
  \<open>adhoc_overloading\<close>, and the type of \<open>d\<close> selects it.
\<close>

consts gamma_S :: "'s \<Rightarrow> store set" ("\<lbrakk>_\<rbrakk>")

text \<open>
  An executable state is read back as the abstract state it represents, given the
  classifier that tells locals from globals. \<open>readback \<G> x\<close> is that reading for
  every executable representation, registered the same way, so a concretization of an
  executable state is \<open>\<lbrakk>readback \<G> x\<rbrakk>\<close> whatever its representation. Its notation
  \<open>\<rho>\<^bsub>\<G>\<^esub> x\<close> is opt-in, in the bundle \<open>default_st_syntax\<close>.
\<close>

consts readback :: "(vname \<Rightarrow> bool) \<Rightarrow> 'e \<Rightarrow> 'a"

end
