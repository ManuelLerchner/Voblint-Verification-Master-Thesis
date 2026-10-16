theory Order_Regression
  imports Order_Analysis "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: the typed order analysis, executed\<close>

text \<open>
  Each case runs the certified solver on a typed program inside Isabelle and pins the
  order facts published at the end of \<open>f\<close>. Termination is decided by evaluation.
\<close>

abbreviation f_var :: "vname \<Rightarrow> var_id" where
  "f_var x \<equiv> ScopedId (STR ''f'') x"

abbreviation ord_result :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> var_id order_rel" where
  "ord_result ds p \<equiv> order_analysis.state_at ds Globals_Join is_global p () (FunctionResult (STR ''f''))"

text \<open>The loop exits when \<open>x < y\<close> fails, so \<open>y \<le> x\<close> holds at the exit. The body
  assigns \<open>x\<close>, which forgets every fact about it, so no fact survives into the loop.\<close>

definition loop_prog :: imp_prog where
  "loop_prog = program {
     fun f(x, y) { while (x < y) { x = x + 1; } }
     fun main() { f(0, 5); } }"

lemma loop_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join (order_analysis.equations [] is_global loop_prog)
     (cfg_exit (elab_cfg loop_prog []), ()) \<noteq> None"
  by eval

lemma loop_terminates: "order_analysis.terminates [] Globals_Join is_global loop_prog"
  unfolding order_analysis.terminates_code
  using TD_side_rule_Interp.solve_dom_of_solve_c[OF loop_terminates_c] by simp

lemma loop_facts: "ord_result [] loop_prog = OFacts True {(f_var (STR ''y''), f_var (STR ''x''))}"
  by eval

text \<open>The facts are about stored values, which already lie in their kinds: a \<^const>\<open>U8\<close>
  \<open>x\<close> and an \<^const>\<open>I32\<close> \<open>y\<close> compared through a conversion yield no fact, since
  the comparison does not see the variables' values unconverted.\<close>

definition mixed_prog :: imp_prog where
  "mixed_prog = program {
     fun f(x, y) { while (x < y) { y = y - 1; } }
     fun main() { f(0, 5); } }"

lemma mixed_facts:
  "ord_result [(f_var (STR ''x''), U8)] mixed_prog = OFacts True {}"
  by eval

subsection \<open>Rendering\<close>

text \<open>\<open>to_string\<close> renders bottom and top by their symbols and a set of facts as a sorted
  conjunction of \<open>\<le>\<close> facts, whatever the flag.\<close>

lemma to_string_order_rel_regression:
  "to_string (OBot :: vname order_rel) = sym_bottom"
  "to_string (OFacts True {} :: vname order_rel) = sym_top"
  "to_string (OFacts False {(STR ''y'', STR ''z''), (STR ''x'', STR ''y'')}) =
     STR ''{x<le>y <and> y<le>z}''"
  by eval+

end
