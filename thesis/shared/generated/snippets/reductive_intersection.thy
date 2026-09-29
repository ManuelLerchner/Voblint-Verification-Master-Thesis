(* src/Abstract_Interpreter/Domain/Eval/Backward_Domain.thy *)
locale reductive_intersection = sound_intersection +
  assumes intersect_reductive1[intro]: "intersect a b \<le> a"
    and intersect_reductive2[intro]: "intersect a b \<le> b"
