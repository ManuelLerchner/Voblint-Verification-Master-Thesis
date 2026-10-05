(* src/Abstract_Interpreter/Domain/Eval/Backward_Domain.thy *)
lemma bfilter_sound [intro]:
  assumes "s \<in> \<lbrakk>d\<rbrakk>" "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = res"
  shows "s \<in> \<lbrakk>bfilter e res d\<rbrakk>"
