theory Relational_Regression
  imports "Voblint_Domain.Order_Lattice"
begin

section \<open>Relational carrier regressions\<close>

text \<open>Build-checked regression assertions on concrete \<open>relc\<close> values, moved out of
  \<open>Order_Lattice\<close>.  Nothing cites them; the build failing is the signal.\<close>

subsection \<open>Rendering\<close>

text \<open>\<open>to_string\<close> renders bottom and top by their symbols and a known pair set as a sorted
  conjunction of \<open>\<le>\<close> facts.\<close>

lemma to_string_relc_regression:
  "to_string RelBot = sym_bottom"
  "to_string (RelC {}) = sym_top"
  "to_string (RelC {(STR ''y'', STR ''z''), (STR ''x'', STR ''y'')}) =
     STR ''{x<le>y <and> y<le>z}''"
  by eval+

end
