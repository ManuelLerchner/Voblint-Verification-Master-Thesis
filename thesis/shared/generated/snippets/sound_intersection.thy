(* src/Abstract_Interpreter/Domain/Eval/Backward_Domain.thy *)
locale sound_intersection =
  fixes intersect :: "'a::numeric_domain => 'a => 'a"
  assumes intersect_sound[intro]:
    "n \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> n \<in> \<gamma> (intersect a b)"
