(* src/Abstract_Interpreter/Domain/Forward_Domain.thy *)
locale sound_evaluator =
  fixes gamma_state :: "'d \<Rightarrow> store set"
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a::sound_domain"
  assumes aval_abs_sound[intro]:
    "s \<in> gamma_state d \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> (aval_abs e d)"
