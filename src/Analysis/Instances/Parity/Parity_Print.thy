theory Parity_Print
  imports Parity_Domain
begin

section \<open>Parity printing\<close>

subsection \<open>Printable instance\<close>

fun string_of_parity :: "parity \<Rightarrow> string" where
    "string_of_parity PBot  = ''Bottom''"
  | "string_of_parity PEven = ''Even''"
  | "string_of_parity POdd  = ''Odd''"
  | "string_of_parity PTop  = ''Top''"

instantiation parity :: show_val begin
definition "show_val_parity (p :: parity) = string_of_parity p"
instance ..
end

lemma show_val_parity_eq [simp]: "(show_val :: parity \<Rightarrow> string) = string_of_parity"
  unfolding show_val_parity_def by simp

end
