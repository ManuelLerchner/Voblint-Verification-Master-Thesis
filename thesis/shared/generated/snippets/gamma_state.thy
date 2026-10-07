(* src/Abstract_Interpreter/Domain/State/Nonrelational_State.thy *)
definition gamma_state :: "('a::numeric_domain) abs_state \<Rightarrow> store set" where
  "gamma_state d = {s. \<forall>x. s x \<in> \<gamma> (d x)}"
