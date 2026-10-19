(* src/Abstract_Interpreter/Exec/Refinement/DG_Local_State_Exec_Refinement.thy *)
theorem exec_local_spec_sound:
  assumes tf_sound: "sound_nonrelational_transfer \<G> sk asn sp br bd rt en ev"
  shows "sound_local_spec \<G> (\<lambda>d. \<gamma> d) (exec_local_spec \<G> empty_pred tf_st enter_st)"
