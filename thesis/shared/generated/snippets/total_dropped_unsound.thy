(* src/Examples/Capstone/Example_Non_Vacuity.thy *)
theorem total_dropped_unsound:
  "(\<lambda>_. 0)(nv_var (STR ''a'') := 1)
     \<in> \<A>\<^bsub>ret_\<kappa>,tot_R,0,ret_g,init_stores ret_\<kappa>\<^esub> (Statement 3) 0
   \<and> (\<lambda>_. 0)(nv_var (STR ''a'') := 1) \<notin> tot_cover (Statement 3) 0"
