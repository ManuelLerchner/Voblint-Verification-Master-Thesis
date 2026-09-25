(* src/Examples/Sign/Example_Sign_Domain_Ops.thy *)
lemma sign_interface_regression:
  "meet_sign SNonNeg SNonPos = SZero"
  "is_empty (meet_sign SPos SNeg)"
  "inv_less_sign True STop SZero = (SNeg, SZero)"
  by eval+
