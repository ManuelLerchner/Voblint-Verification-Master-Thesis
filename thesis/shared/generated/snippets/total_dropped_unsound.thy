(* src/Examples/Capstone/Example_Non_Vacuity.thy *)
theorem total_dropped_unsound:
  "(\<lambda>_. 0)(STR ''a'' := 1)
     \<in> \<A>\<^bsub>declared_global ret_prog,tot_R,0,prog_cfg ret_prog,
         cinit_stores (declared_global ret_prog)\<^esub> (Statement 3) 0
   \<and> (\<lambda>_. 0)(STR ''a'' := 1) \<notin> tot_cover (Statement 3) 0"
