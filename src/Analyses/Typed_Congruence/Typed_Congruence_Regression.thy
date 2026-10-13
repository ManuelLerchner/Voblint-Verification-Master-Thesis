theory Typed_Congruence_Regression
  imports Congruence_Kind "Voblint_Typed_Nonrel.Typed_Nonrel_Analysis" "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: the typed Congruence analysis, executed\<close>

definition ct_at :: "'a tabs toplift \<Rightarrow> var_id \<Rightarrow> 'a kd" where
  "ct_at d v = (case d of TTop \<Rightarrow> KTop | TL \<sigma> \<Rightarrow> \<sigma> v)"

abbreviation cong_state_at :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> congruence tabs toplift" where
  "cong_state_at ds p \<equiv> typed_nonrel.state_at ds Globals_Join tglobal p ()"

abbreviation f_var :: "vname \<Rightarrow> var_id" where
  "f_var x \<equiv> ScopedId (STR ''f'') x"

abbreviation f_result :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> vname \<Rightarrow> congruence kd" where
  "f_result ds p x \<equiv> ct_at (cong_state_at ds p (FunctionResult (STR ''f''))) (f_var x)"


abbreviation cong_equations :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<times> unit \<Rightarrow>
    (cfg_node \<times> unit, (unit, unit) global_unknown,
     (congruence tst toplift lifted, congruence tst toplift lifted) dg_state) strategy_tree" where
  "cong_equations ds p \<equiv> typed_nonrel.equations ds tglobal p"

subsection \<open>Constants\<close>

text \<open>A product of constants stays a constant.\<close>

definition const_prog :: imp_prog where
  "const_prog = program { fun f() { x = 3; x = x * 5; } fun main() { f(); } }"

lemma const_value: "f_result [] const_prog (STR ''x'') = KD I32 (mk_congruence 15 0)"
  by eval

subsection \<open>Classes through a loop\<close>

text \<open>
  A step of \<open>4\<close> keeps \<open>x\<close> in \<open>4\<int>\<close> at \<^const>\<open>I32\<close>: wrapping shifts a value by a
  multiple of \<open>2 ^ 32\<close>, which \<open>4\<close> divides. Goblint answers top here, since it does not
  wrap signed kinds; the interval product's \<^verbatim>\<open>no_ov\<close> recovers its precision there.
  A step of \<open>3\<close> loses the class: \<open>3\<close> does not divide \<open>2 ^ 32\<close>, so after a wraparound
  \<open>x\<close> need not be a multiple of \<open>3\<close>. The loop bound rules the wraparound out, but
  Congruence alone cannot see the bound. Under mathematical integers the class would
  be \<open>3\<int>\<close>; this is a property that changes under wraparound.
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
     (cfg_exit (typed_cfg pow2_prog []), ()) \<noteq> None"
  by eval

lemma pow2_terminates: "typed_nonrel.terminates TYPE(congruence) [] Globals_Join tglobal pow2_prog"
  unfolding typed_nonrel.terminates_code
  using TD_side_rule_Interp.solve_dom_of_solve_c[OF pow2_terminates_c] by simp

lemma loop_values:
  "f_result [] pow2_prog (STR ''x'') = KD I32 (mk_congruence 0 4)"
  "f_result [] odd_step_prog (STR ''x'') = KD I32 top"
  by eval+

subsection \<open>Overflow\<close>

text \<open>\<open>260\<close> wraps to \<open>4\<close> at \<^const>\<open>U8\<close>, as in Goblint. At \<^const>\<open>I8\<close>, \<open>130\<close> wraps to
  \<open>-126\<close>; Goblint answers top for a signed overflow.\<close>

definition wrap_prog :: imp_prog where
  "wrap_prog = program { fun f() { x = 250; x = x + 10; } fun main() { f(); } }"

definition swrap_prog :: imp_prog where
  "swrap_prog = program { fun f() { x = 120; x = x + 10; } fun main() { f(); } }"

lemma wrap_values:
  "f_result [(f_var (STR ''x''), U8)] wrap_prog (STR ''x'') = KD U8 (mk_congruence 4 0)"
  "f_result [(f_var (STR ''x''), I8)] swrap_prog (STR ''x'') = KD I8 (mk_congruence (-126) 0)"
  by eval+

subsection \<open>Conversions\<close>

text \<open>
  \<open>x\<close> is a \<^const>\<open>U8\<close> stepping by \<open>8\<close>. Widening it to the \<^const>\<open>I32\<close> \<open>y\<close> keeps
  its class, as Goblint's \<^verbatim>\<open>cast_to\<close> does for a contained \<^verbatim>\<open>from_ik\<close>. Narrowing
  \<open>y + 2\<close> back to the \<^const>\<open>U8\<close> \<open>z\<close> keeps \<open>2 + 8\<int>\<close>, since \<open>8\<close> divides \<open>2 ^ 8\<close>;
  narrowing the class \<open>6\<int>\<close> to \<^const>\<open>U8\<close> keeps \<open>2\<int>\<close>. Goblint answers top for both
  narrowing conversions of a non-constant.
\<close>

definition conv_prog :: imp_prog where
  "conv_prog = program {
     fun f() { x = 0; while (x < 200) { x = x + 8; } y = x; z = y + 2; }
     fun main() { f(); } }"

definition conv_kinds :: kind_decls where
  "conv_kinds = [(f_var (STR ''x''), U8), (f_var (STR ''z''), U8)]"

definition narrow_prog :: imp_prog where
  "narrow_prog = program {
     fun f(c) { y = 0; if (c < 1) { y = 6; } z = y; }
     fun main() { f(0); f(5); } }"

lemma conv_values:
  "f_result conv_kinds conv_prog (STR ''x'') = KD U8 (mk_congruence 0 8)"
  "f_result conv_kinds conv_prog (STR ''y'') = KD I32 (mk_congruence 0 8)"
  "f_result conv_kinds conv_prog (STR ''z'') = KD U8 (mk_congruence 2 8)"
  "f_result [(f_var (STR ''z''), U8)] narrow_prog (STR ''y'') = KD I32 (mk_congruence 0 6)"
  "f_result [(f_var (STR ''z''), U8)] narrow_prog (STR ''z'') = KD U8 (mk_congruence 0 2)"
  by eval+

end
