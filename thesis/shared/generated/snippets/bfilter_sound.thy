(* src/Abstract_Interpreter/Domain/Eval/Backward_Domain.thy *)
lemma bfilter_sound [intro]:
  assumes "s \<in> \<gamma> d" "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = res"
  shows "s \<in> \<gamma> (bfilter e res d)"
