(* src/Examples/Capstone/Example_Non_Vacuity.thy *)
theorem unpaired_entry_cover_unsound:
  defines "s \<equiv> (\<lambda>_. 0)(STR ''x'' := 1) :: store"
      and "s' \<equiv> (\<lambda>_. 0)(STR ''a'' := 1) :: store"
  shows "s' = call_enter (\<lambda>_. False) (CallEdge (Some (STR ''y'')) [STR ''a''] [V (STR ''x'')]) s"
    and "(\<exists>(q, e) \<in> set unpaired_answer. s \<in> q)"
    and "(\<exists>(q, e) \<in> set unpaired_answer. s' \<in> e)"
    and "\<not> entry_pairs_cover id s s' unpaired_answer"
    and "\<forall>u \<in> pairwise_contribution unpaired_answer. u (STR ''y'') < 0"
    and "combine_collect (\<lambda>_. False) (Some (STR ''y'')) s (s'(ret_var := s' (STR ''a'')))
           (STR ''y'') = 1"
