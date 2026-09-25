(* src/Abstract_Interpreter/Domain/Forward_Domain.thy *)
locale sound_truth_test =
  fixes tobool :: "'a::sound_domain \<Rightarrow> bool option"
  assumes tobool_sound:
    "tobool p = Some b \<Longrightarrow> i \<in> \<gamma> p \<Longrightarrow> truthy i = b"
