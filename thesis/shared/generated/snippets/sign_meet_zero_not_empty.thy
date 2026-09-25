(* src/Examples/Sign/Example_Sign_Domain_Ops.thy *)
lemma sign_meet_zero_not_empty:
  "\<not> is_empty (meet_sign SNonNeg SNonPos)"
  by (rule sign_backward_domain.intersect_shared_not_empty[of 0]) simp_all
