(* src/Examples/Sign/Example_Sign_Mixed_Flow.thy *)
theorem mf_ltr_collect_sound:
  "\<C>\<^bsub>mf_gs,mf_cfg,cinit_stores mf_gs\<^esub> v
     \<subseteq> mf_gammaM (mf_reader (Inl (v, ())))"
