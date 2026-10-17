(* src/Abstract_Interpreter/Domain/State/Nonrelational_State.thy *)
definition gamma_state :: "('k, 'a::numeric_domain) gabs_state \<Rightarrow> ('k \<Rightarrow> int) set" where
  "gamma_state d = {s. \<forall>x. s x \<in> \<gamma> (d x)}"
