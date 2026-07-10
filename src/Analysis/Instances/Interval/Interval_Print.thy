theory Interval_Print
  imports Interval_Transfer
begin

section \<open>Interval printing\<close>

subsection \<open>Printable instance\<close>

fun string_of_eint :: "eint \<Rightarrow> string" where
    "string_of_eint MinInf  = ''-inf''"
  | "string_of_eint PlusInf = ''+inf''"
  | "string_of_eint (Fin n) = show_int n"

fun string_of_ivl :: "ivl \<Rightarrow> string" where
  "string_of_ivl (Ivl l u) = ''['' @ string_of_eint l @ '','' @ string_of_eint u @ '']''"

instantiation ivl :: show_val begin
definition "show_val_ivl (i :: ivl) = string_of_ivl i"
instance ..
end

lemma show_val_ivl_eq [simp]: "(show_val :: ivl \<Rightarrow> string) = string_of_ivl"
  unfolding show_val_ivl_def by simp

end
