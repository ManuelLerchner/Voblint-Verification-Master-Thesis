theory Typed_Order_Regression
  imports Typed_Order_Analysis "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: the typed order analysis, executed\<close>

abbreviation f_var :: "vname \<Rightarrow> var_id" where
  "f_var x \<equiv> ScopedId (STR ''f'') x"

abbreviation ord_result :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> var_id order_rel" where
  "ord_result ds p \<equiv> typed_order.state_at ds Globals_Join tglobal p () (FunctionResult (STR ''f''))"

text \<open>The loop exits when \<open>x < y\<close> fails, so \<open>y \<le> x\<close> holds at the exit. The body
  assigns \<open>x\<close>, which forgets every fact about it, so no fact survives into the loop.\<close>

definition loop_prog :: imp_prog where
  "loop_prog = program {
     fun f(x, y) { while (x < y) { x = x + 1; } }
     fun main() { f(0, 5); } }"

lemma loop_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join (typed_order.equations [] tglobal loop_prog)
     (cfg_exit (typed_cfg loop_prog []), ()) \<noteq> None"
  by eval

lemma loop_terminates: "typed_order.terminates [] Globals_Join tglobal loop_prog"
  unfolding typed_order.terminates_code
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

end
