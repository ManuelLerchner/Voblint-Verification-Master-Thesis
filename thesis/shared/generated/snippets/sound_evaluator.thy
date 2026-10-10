(* src/Abstract_Interpreter/Domain/Eval/Forward_Domain.thy *)
locale sound_evaluator =
  fixes \<gamma>\<^sub>S :: "'d \<Rightarrow> store set"
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a::numeric_domain" ("\<lbrakk>_\<rbrakk>\<^sup>\<sharp>")
  assumes aval_abs_sound[intro]:
    "s \<in> \<gamma>\<^sub>S d \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> \<gamma> (\<lbrakk>e\<rbrakk>\<^sup>\<sharp> d)"
