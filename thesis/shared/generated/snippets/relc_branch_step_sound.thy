(* src/Analyses/Relational/Rel_Order_Domain.thy *)
lemma relc_branch_step_sound [intro]:
  assumes "s \<in> \<lbrakk>d\<rbrakk>" "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) = pol"
  shows "s \<in> \<lbrakk>relc_branch_step b pol d\<rbrakk>"
