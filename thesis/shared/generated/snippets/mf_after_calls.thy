(* src/Examples/Sign/Example_Sign_Mixed_Flow.thy *)
corollary mf_after_calls:
  assumes "s \<in> \<C>\<^bsub>mf_gs,mf_cfg,cinit_stores mf_gs\<^esub> (Statement 7)"
  shows "0 < s (STR ''x'') \<and> 0 \<le> s (STR ''y'')"
