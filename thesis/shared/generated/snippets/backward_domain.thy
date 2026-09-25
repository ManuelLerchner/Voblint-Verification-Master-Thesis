(* src/Abstract_Interpreter/Domain/Backward_Domain.thy *)
locale backward_domain =
  semantic_intersection intersect + sound_evaluator gamma_state aval_abs
    + sound_truth_test tobool
    for intersect :: "'a::sound_domain => 'a => 'a"
    and aval_abs :: "exp => 'a abs_state => 'a"
    and tobool :: "'a => bool option" +
  fixes
    inv_less  :: "bool => 'a => 'a => 'a * 'a"
    and inv_eq    :: "bool => 'a => 'a => 'a * 'a"
    and inv_plus  :: "'a => 'a => 'a => 'a * 'a"
    and inv_minus :: "'a => 'a => 'a => 'a * 'a"
    and inv_times :: "'a => 'a => 'a => 'a * 'a"
  assumes
      inv_less_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> (n1 < n2) = res
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_less res a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_less res a1 a2))"
  and inv_eq_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> (n1 = n2) = res
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_eq res a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_eq res a1 a2))"
  and inv_plus_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> n1 + n2 \<in> \<gamma> r
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_plus r a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_plus r a1 a2))"
  and inv_minus_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> n1 - n2 \<in> \<gamma> r
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_minus r a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_minus r a1 a2))"
  and inv_times_sound:
      "n1 \<in> \<gamma> a1 \<Longrightarrow> n2 \<in> \<gamma> a2 \<Longrightarrow> n1 * n2 \<in> \<gamma> r
       \<Longrightarrow> n1 \<in> \<gamma> (fst (inv_times r a1 a2)) \<and> n2 \<in> \<gamma> (snd (inv_times r a1 a2))"
