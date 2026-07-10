theory Sign_Print
  imports Sign_Lattice
begin

section \<open>Sign printing\<close>

subsection \<open>Printable instance\<close>

fun string_of_sign :: "sign \<Rightarrow> string" where
    "string_of_sign SBot    = ''Bottom''"
  | "string_of_sign SNeg    = ''Negative''"
  | "string_of_sign SNonPos = ''NonPositive''"
  | "string_of_sign SZero   = ''Zero''"
  | "string_of_sign SNonNeg = ''NonNegative''"
  | "string_of_sign SPos    = ''Positive''"
  | "string_of_sign STop    = ''Top''"

instantiation sign :: show_val begin
definition "show_val_sign (s :: sign) = string_of_sign s"
instance ..
end

lemma show_val_sign_eq [simp]: "(show_val :: sign \<Rightarrow> string) = string_of_sign"
  unfolding show_val_sign_def by simp

end
