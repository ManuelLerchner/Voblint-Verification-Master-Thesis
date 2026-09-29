(* src/Analyses/Shared/Nonrelational/Special_Ops.thy *)
locale sound_special_ops = sound_evaluator gamma_state ev
  for ops :: "'a::numeric_domain special_ops"
    and ev  :: "exp => 'a abs_state => 'a" +
  assumes special_min_sound[intro]:
    "i \<in> \<gamma> p \<Longrightarrow> j \<in> \<gamma> q \<Longrightarrow> min i j \<in> \<gamma> (special_min ops p q)"
  assumes special_max_sound[intro]:
    "i \<in> \<gamma> p \<Longrightarrow> j \<in> \<gamma> q \<Longrightarrow> max i j \<in> \<gamma> (special_max ops p q)"
