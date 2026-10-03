(* src/Abstract_Interpreter/Framework/Checks/Abstract_Checks.thy *)
locale sound_check_query =
  sound_numeric_queries less eq + sound_evaluator \<gamma>\<^sub>S aval_abs
  for less :: "'a::numeric_domain \<Rightarrow> 'a \<Rightarrow> bool option"
    and eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and \<gamma>\<^sub>S :: "'d \<Rightarrow> store set"
    and aval_abs :: "exp \<Rightarrow> 'd \<Rightarrow> 'a"
