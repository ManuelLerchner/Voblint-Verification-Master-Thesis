(* src/Abstract_Interpreter/Domain/Forward_Domain.thy *)
locale sound_evaluator =
  fixes \<gamma>\<^sub>S :: "'d \<Rightarrow> store set"
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a::numeric_domain"
  assumes aval_abs_sound[intro]:
    "s \<in> \<gamma>\<^sub>S d \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> (aval_abs e d)"
