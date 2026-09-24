(* src/Examples/Sign/Example_Sign_DG_Overlapping_Enter.thy *)
lemma ov_empty_continuation_bot:
  "locals (snd ov_empty_sol (Inl (Statement 4, []))) = Bot"
