(* src/Abstract_Interpreter/Domain/Backward_Domain.thy *)
locale semantic_intersection =
  fixes intersect :: "'a::sound_domain => 'a => 'a"
  assumes intersect_sound[intro]:
    "n \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> n \<in> \<gamma> (intersect a b)"
