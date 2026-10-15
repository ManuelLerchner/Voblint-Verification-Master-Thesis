theory Congruence_Regression
  imports Congruence_Kind "Voblint_Nonrelational.Nonrelational_Analysis" "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: the typed Congruence analysis, executed\<close>

abbreviation cong_state_at :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> congruence tabs" where
  "cong_state_at ds p \<equiv> nonrel.state_at default_sem_conf ds 0 Globals_Join is_global p []"

abbreviation f_var :: "vname \<Rightarrow> var_id" where
  "f_var x \<equiv> ScopedId (STR ''f'') x"

abbreviation f_result :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> vname \<Rightarrow> congruence kd" where
  "f_result ds p x \<equiv> cong_state_at ds p (FunctionResult (STR ''f'')) (f_var x)"

abbreviation cong_equations :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<times> cfg_node list \<Rightarrow>
    (cfg_node \<times> cfg_node list, (unit, cfg_node list) global_unknown,
     (congruence tst lifted, congruence tst lifted) dg_state) strategy_tree" where
  "cong_equations ds p \<equiv> nonrel.equations default_sem_conf ds 0 is_global p"

subsection \<open>Constants\<close>

text \<open>
  Under Goblint's default \<^verbatim>\<open>assume_top\<close>, standalone Congruence answers top for signed
  addition and multiplication, constants included; only a difference of constants that
  stays in range is kept. An unsigned kind computes constants modulo its range. A
  \<^const>\<open>U8\<close> operand is promoted to the signed \<^const>\<open>I32\<close> first, so the examples
  use \<^const>\<open>U32\<close>.
\<close>

definition const_prog :: imp_prog where
  "const_prog = program { fun f() { x = 3; x = x * 5; } fun main() { f(); } }"

definition sub_prog :: imp_prog where
  "sub_prog = program { fun f() { x = 3; x = x - 5; } fun main() { f(); } }"

definition u32_x :: kind_decls where
  "u32_x = [(f_var (STR ''x''), U32)]"

lemma const_value:
  "f_result [] const_prog (STR ''x'') = KD I32 top"
  "f_result u32_x const_prog (STR ''x'') = KD U32 (mk_congruence 15 0)"
  "f_result [] sub_prog (STR ''x'') = KD I32 (mk_congruence (-2) 0)"
  by eval+

subsection \<open>Classes through a loop\<close>

text \<open>
  A step of \<open>4\<close> keeps an unsigned \<open>x\<close> in \<open>4\<int>\<close>: wrapping shifts a value by a multiple of
  \<open>2 ^ 32\<close>, which \<open>4\<close> divides (\<^verbatim>\<open>handle_overflow\<close>). A step of \<open>3\<close> loses the class,
  since \<open>3\<close> does not divide \<open>2 ^ 32\<close>. At the signed \<^const>\<open>I32\<close> the step answers top
  under \<^verbatim>\<open>assume_top\<close>; the interval product's \<^verbatim>\<open>no_ov\<close> recovers the class there.
\<close>

definition pow2_prog :: imp_prog where
  "pow2_prog = program {
     fun f() { x = 0; while (x < 100) { x = x + 4; } }
     fun main() { f(); } }"

definition odd_step_prog :: imp_prog where
  "odd_step_prog = program {
     fun f() { x = 0; while (x < 99) { x = x + 3; } }
     fun main() { f(); } }"

lemma pow2_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join (cong_equations [] pow2_prog)
     (cfg_exit (elab_cfg pow2_prog []), []) \<noteq> None"
  by eval

lemma pow2_terminates: "nonrel.terminates TYPE(congruence) default_sem_conf [] 0 Globals_Join is_global pow2_prog"
  unfolding nonrel.terminates_code
  using TD_side_rule_Interp.solve_dom_of_solve_c[OF pow2_terminates_c] by simp

lemma loop_values:
  "f_result u32_x pow2_prog (STR ''x'') = KD U32 (mk_congruence 0 4)"
  "f_result u32_x odd_step_prog (STR ''x'') = KD U32 top"
  "f_result [] pow2_prog (STR ''x'') = KD I32 top"
  by eval+

subsection \<open>Overflow\<close>

text \<open>\<open>-6 + 10\<close> wraps to \<open>4\<close> at \<^const>\<open>U32\<close>, as in Goblint. A signed difference of
  constants that leaves the range answers top, Goblint's signed overflow under
  \<^verbatim>\<open>assume_top\<close>.\<close>

definition wrap_prog :: imp_prog where
  "wrap_prog = program { fun f() { x = 0 - 6; x = x + 10; } fun main() { f(); } }"

definition swrap_prog :: imp_prog where
  "swrap_prog = program { fun f() { x = 0 - 2147483647; x = x - 10; } fun main() { f(); } }"

lemma wrap_values:
  "f_result u32_x wrap_prog (STR ''x'') = KD U32 (mk_congruence 4 0)"
  "f_result [] swrap_prog (STR ''x'') = KD I32 top"
  by eval+

subsection \<open>Conversions\<close>

text \<open>
  \<open>x\<close> is a \<^const>\<open>U32\<close> stepping by \<open>8\<close>. Widening it to the \<^const>\<open>I64\<close> \<open>y\<close> keeps
  its class, as Goblint's \<^verbatim>\<open>cast_to\<close> does for a contained \<^verbatim>\<open>from_ik\<close>. Narrowing the
  class \<open>6\<int>\<close> from \<^const>\<open>I32\<close> to \<^const>\<open>U8\<close> answers top, as \<^verbatim>\<open>cast_to\<close> does for
  a non-constant; narrowing the constant \<open>300\<close> wraps it to \<open>44\<close>.
\<close>

definition conv_prog :: imp_prog where
  "conv_prog = program {
     fun f() { x = 0; while (x < 200) { x = x + 8; } y = x; }
     fun main() { f(); } }"

definition conv_kinds :: kind_decls where
  "conv_kinds = [(f_var (STR ''x''), U32), (f_var (STR ''y''), I64)]"

definition narrow_prog :: imp_prog where
  "narrow_prog = program {
     fun f(c) { y = 0; if (c < 1) { y = 6; } z = y; w = 300; v = w; }
     fun main() { f(0); f(5); } }"

definition narrow_kinds :: kind_decls where
  "narrow_kinds = [(f_var (STR ''z''), U8), (f_var (STR ''v''), U8)]"

lemma conv_values:
  "f_result conv_kinds conv_prog (STR ''x'') = KD U32 (mk_congruence 0 8)"
  "f_result conv_kinds conv_prog (STR ''y'') = KD I64 (mk_congruence 0 8)"
  "f_result narrow_kinds narrow_prog (STR ''y'') = KD I32 (mk_congruence 0 6)"
  "f_result narrow_kinds narrow_prog (STR ''z'') = KD U8 top"
  "f_result narrow_kinds narrow_prog (STR ''v'') = KD U8 (mk_congruence 44 0)"
  by eval+

end
