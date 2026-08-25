(* src/Core/Equations/Constraint_System.thy *)
definition combine_env_abs ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
where
  "combine_env_abs gs sc se = (\<lambda>x. if gs x then se x else sc x)"
