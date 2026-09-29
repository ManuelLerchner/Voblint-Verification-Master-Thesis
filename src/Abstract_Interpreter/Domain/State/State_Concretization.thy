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

end
