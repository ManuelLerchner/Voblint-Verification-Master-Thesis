(* src/Abstract_Interpreter/Domain/Eval/Backward_Domain.thy *)
locale sound_refinement =
  sound_intersection intersect + sound_evaluator gamma_state aval_abs
    + sound_truth_test tobool
    + sound_inverse_ops intersect inv_less inv_eq inv_plus inv_minus inv_times
    for intersect :: "'a::numeric_domain => 'a => 'a"
    and aval_abs :: "exp => 'a abs_state => 'a"
    and tobool :: "'a => bool option"
    and inv_less  :: "bool => 'a => 'a => 'a * 'a"
    and inv_eq    :: "bool => 'a => 'a => 'a * 'a"
    and inv_plus  :: "'a => 'a => 'a => 'a * 'a"
    and inv_minus :: "'a => 'a => 'a => 'a * 'a"
    and inv_times :: "'a => 'a => 'a => 'a * 'a"
