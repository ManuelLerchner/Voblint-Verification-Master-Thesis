(* src/Examples/Capstone/Example_Non_Vacuity.thy *)
theorem return_at_caller_context_unsound:
  "(\<lambda>_. 0)(nv_var (STR ''a'') := 1) \<in> \<C>\<^bsub>ret_\<kappa>,ret_g,init_stores ret_\<kappa>\<^esub> (Statement 3)
   \<and> (\<Union>c. ret_cover (Statement 3) c) = {}"
