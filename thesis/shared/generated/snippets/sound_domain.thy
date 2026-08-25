(* src/Core/Domain/Abstract_Domain.thy *)
class sound_domain = computable_domain +
  fixes gamma :: "'a \<Rightarrow> int set"
  assumes gamma_bot: "gamma bot = {}"
  assumes gamma_mono: "a \<le> b \<Longrightarrow> gamma a \<subseteq> gamma b"
  assumes is_bot_correct: "is_bot a \<longleftrightarrow> gamma a = {}"
  assumes is_top_correct: "is_top a \<longleftrightarrow> a = top"
