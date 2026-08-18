theory Congruence_Print
  imports Congruence_Domain
begin

section \<open>Congruence printing\<close>

subsection \<open>Printable instance\<close>

definition string_of_congruence :: "congruence \<Rightarrow> string" where
  "string_of_congruence c =
     (case Rep_congruence c of
        None \<Rightarrow> ''Top''
      | Some (r, m) \<Rightarrow>
          if m = 0 then ''='' @ show_int r
          else ''='' @ show_int r @ '' (mod '' @ show_int m @ '')'')"

instantiation congruence :: show_val begin
definition "show_val_congruence (c :: congruence) = string_of_congruence c"
instance ..
end

lemma show_val_congruence_eq [simp]: "(show_val :: congruence \<Rightarrow> string) = string_of_congruence"
  unfolding show_val_congruence_def by simp

end
