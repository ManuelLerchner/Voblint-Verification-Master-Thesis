(* src/Analyses/Relational/Rel_Order_Domain.thy *)
lemma relc_branch_step_sound [intro]:
  assumes "s \<in> \<gamma> d" "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) = pol"
  shows "s \<in> \<gamma> (relc_branch_step b pol d)"
