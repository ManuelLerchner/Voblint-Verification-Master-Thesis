(* src/Examples/Capstone/Example_Non_Vacuity.thy *)
theorem return_at_caller_context_unsound:
  "(\<lambda>_. 0)(STR ''a'' := 1)
     \<in> \<C>\<^bsub>declared_global ret_prog,prog_cfg ret_prog,
         cinit_stores (declared_global ret_prog)\<^esub> (Statement 3)
   \<and> (\<Union>c. ret_cover (Statement 3) c) = {}"
