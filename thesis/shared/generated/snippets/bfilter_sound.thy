(* src/Abstract_Interpreter/Domain/Backward_Domain.thy *)
lemma bfilter_sound [intro]:
  assumes "s \<in> \<lbrakk>\<sigma>\<rbrakk>" "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = res"
  shows "s \<in> \<lbrakk>bfilter e res \<sigma>\<rbrakk>"
