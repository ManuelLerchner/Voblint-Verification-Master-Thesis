theory Demo
  imports Main
begin
definition gamma_sign :: "int \<Rightarrow> int set" where
  "gamma_sign x = {x}"
locale sound_domain =
  fixes step :: "int \<Rightarrow> int"
  assumes sound: "x \<in> gamma_sgn y \<Longrightarrow> step x \<in> gamma_sign (step y)"
end
