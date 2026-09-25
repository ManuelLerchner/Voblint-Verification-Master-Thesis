(* src/Examples/Sign/Example_Sign_Domain_Ops.thy *)
lemma (in semantic_intersection) intersect_shared_not_empty:
  "n \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> \<not> is_empty (intersect a b)"
  using intersect_sound is_empty_correct by blast
