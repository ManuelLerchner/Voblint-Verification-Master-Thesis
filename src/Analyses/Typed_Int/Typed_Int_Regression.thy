theory Typed_Int_Regression
  imports Int_Tuple_Kind "Voblint_Typed_Nonrel.Typed_Nonrel_Analysis" "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: the typed Interval-Congruence product, executed\<close>

definition it_at :: "'a tabs toplift \<Rightarrow> var_id \<Rightarrow> 'a kd" where
  "it_at d v = (case d of TTop \<Rightarrow> KTop | TL \<sigma> \<Rightarrow> \<sigma> v)"

abbreviation it_state_at :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> int_tuple tabs toplift" where
  "it_state_at ds p \<equiv> typed_nonrel.state_at ds 0 Globals_Join tglobal p []"

abbreviation it_equations :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<times> cfg_node list \<Rightarrow>
    (cfg_node \<times> cfg_node list, (unit, cfg_node list) global_unknown,
     (int_tuple tst toplift lifted, int_tuple tst toplift lifted) dg_state) strategy_tree" where
  "it_equations ds p \<equiv> typed_nonrel.equations ds 0 tglobal p"

abbreviation f_var :: "vname \<Rightarrow> var_id" where
  "f_var x \<equiv> ScopedId (STR ''f'') x"

abbreviation f_result :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> vname \<Rightarrow> int_tuple kd" where
  "f_result ds p x \<equiv> it_at (it_state_at ds p (FunctionResult (STR ''f''))) (f_var x)"

subsection \<open>No overflow keeps the class\<close>

text \<open>
  The interval bounds \<open>x + 3\<close> by \<open>101\<close>, so the addition cannot overflow
  (Goblint's \<^verbatim>\<open>no_ov\<close>) and the congruence keeps \<open>3\<int>\<close>. The exit guard
  \<open>x \<ge> 99\<close> meets the interval \<open>[99, 101]\<close>, and refining with \<open>3\<int>\<close> leaves \<open>99\<close>.
  The Congruence analysis alone answers top here (\<open>Typed_Congruence_Regression\<close>).
\<close>

definition odd_step_prog :: imp_prog where
  "odd_step_prog = program {
     fun f() { x = 0; while (x < 99) { x = x + 3; } }
     fun main() { f(); } }"

lemma odd_step_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join (it_equations [] odd_step_prog)
     (cfg_exit (typed_cfg odd_step_prog []), []) \<noteq> None"
  by eval

lemma odd_step_terminates:
  "typed_nonrel.terminates TYPE(int_tuple) [] 0 Globals_Join tglobal odd_step_prog"
  unfolding typed_nonrel.terminates_code
  using TD_side_rule_Interp.solve_dom_of_solve_c[OF odd_step_terminates_c] by simp

lemma odd_step_value:
  "f_result [] odd_step_prog (STR ''x'') = KD I32 (IT (Ivl (Fin 99) (Fin 99)) (mk_congruence 99 0))"
  by eval

subsection \<open>A guard the components refute together\<close>

text \<open>\<open>x\<close> is \<open>0\<close> or \<open>10\<close>, so \<open>x \<in> [0, 10] \<inter> 10\<int>\<close>. Neither component alone refutes
  \<open>x == 5\<close>; their meet is empty, so the branch is dead and \<open>y\<close> stays \<open>0\<close>.\<close>

definition guard_prog :: imp_prog where
  "guard_prog = program {
     fun f(x) { y = 0; if (x == 5) { y = 1; } }
     fun main() { f(0); f(10); } }"

lemma guard_value:
  "f_result [] guard_prog (STR ''y'') = KD I32 (IT (Ivl (Fin 0) (Fin 0)) (mk_congruence 0 0))"
  by eval

subsection \<open>Unsigned kinds\<close>

text \<open>
  \<open>x\<close> is a \<^const>\<open>U8\<close> stepping by \<open>10\<close> below \<open>250\<close>. The class \<open>10\<int>\<close> rounds the
  guarded interval to \<open>[0, 240]\<close>, so \<open>x + 10\<close> stays within the kind and the class
  survives the conversion back; the exit is exactly \<open>250\<close>. A constant that leaves the
  kind wraps in both components.
\<close>

definition wrap_loop_prog :: imp_prog where
  "wrap_loop_prog = program {
     fun f() { x = 0; while (x < 250) { x = x + 10; } }
     fun main() { f(); } }"

definition wrap_prog :: imp_prog where
  "wrap_prog = program { fun f() { x = 250; x = x + 10; } fun main() { f(); } }"

lemma unsigned_values:
  "f_result [(f_var (STR ''x''), U8)] wrap_loop_prog (STR ''x'')
     = KD U8 (IT (Ivl (Fin 250) (Fin 250)) (mk_congruence 250 0))"
  "f_result [(f_var (STR ''x''), U8)] wrap_prog (STR ''x'')
     = KD U8 (IT (Ivl (Fin 4) (Fin 4)) (mk_congruence 4 0))"
  by eval+

end
