(* src/Analyses/Relational/Rel_Order_Domain.thy *)
lemma branch_step_rel_sound [intro]:
  assumes "s \<in> \<lbrakk>d\<rbrakk>" "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) = pol"
  shows "s \<in> \<lbrakk>branch_step_rel b pol d\<rbrakk>"
