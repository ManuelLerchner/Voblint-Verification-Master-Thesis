theory Int_Print
  imports Int_Domain "Voblint_Analysis.Congruence_Print" "Voblint_Analysis.Parity_Print"
    "Voblint_Analysis.Sign_Print" "Voblint_Analysis.Interval_Print"
begin

section \<open>Composite integer domain printing\<close>

subsection \<open>Printable instance\<close>

fun string_of_int_dom :: "int_dom \<Rightarrow> string" where
  "string_of_int_dom d =
     ''sign='' @ string_of_sign (int_sign d)
     @ '', ivl='' @ string_of_ivl (int_ivl d)
     @ '', parity='' @ string_of_parity (int_parity d)
     @ '', congruence='' @ string_of_congruence (int_congruence d)"

instantiation int_dom_ext :: (type) show_val begin
definition "show_val_int_dom_ext (d :: 'a int_dom_scheme) = string_of_int_dom (int_dom.truncate d)"
instance ..
end

end
