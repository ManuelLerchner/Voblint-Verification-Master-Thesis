theory Typed_Interval_Regression
  imports Interval_Kind "Voblint_Typed_Nonrel.Typed_Nonrel_Analysis" "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: the typed Interval analysis, executed\<close>

text \<open>
  Each case runs the certified solver on a typed program inside Isabelle and pins the
  published value of one variable. Termination is decided by evaluation, so the
  end-to-end theorems of \<open>Typed_Nonrel_Analysis\<close> apply to these runs.
\<close>


abbreviation ivl_equations :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<times> cfg_node list \<Rightarrow>
    (cfg_node \<times> cfg_node list, (unit, cfg_node list) global_unknown,
     (ivl tst lifted, ivl tst lifted) dg_state) strategy_tree" where
  "ivl_equations ds p \<equiv> typed_nonrel.equations default_sem_conf ds 0 tglobal p"

abbreviation ivl_state_at :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> ivl tabs" where
  "ivl_state_at ds p \<equiv> typed_nonrel.state_at default_sem_conf ds 0 Globals_Join tglobal p []"

abbreviation main_var :: "vname \<Rightarrow> var_id" where
  "main_var x \<equiv> ScopedId (STR ''main'') x"

subsection \<open>A counting loop at \<^const>\<open>I32\<close>\<close>

text \<open>The guard bounds the body and the loop exit, as in the untyped flagship.\<close>

definition loop_prog :: imp_prog where
  "loop_prog = program { fun main() { x = 0; while (x < 20) { x = x + 1; } } }"

lemma loop_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join (ivl_equations [] loop_prog)
     (cfg_exit (typed_cfg loop_prog []), []) \<noteq> None"
  by eval

lemma loop_terminates: "typed_nonrel.terminates TYPE(ivl) default_sem_conf [] 0 Globals_Join tglobal loop_prog"
  unfolding typed_nonrel.terminates_code
  using TD_side_rule_Interp.solve_dom_of_solve_c[OF loop_terminates_c] by simp

abbreviation loop_at :: "pp \<Rightarrow> ivl tabs" where
  "loop_at \<equiv> ivl_state_at [] loop_prog"

lemma loop_values:
  "loop_at (Statement 1) (main_var (STR ''x'')) = KD I32 (Ivl (Fin 0) (Fin 20))"
  "loop_at (Statement 2) (main_var (STR ''x'')) = KD I32 (Ivl (Fin 0) (Fin 19))"
  "loop_at (Statement 3) (main_var (STR ''x'')) = KD I32 (Ivl (Fin 20) (Fin 20))"
  by eval+

subsection \<open>An unsigned char that wraps\<close>

text \<open>\<open>x\<close> is a \<^const>\<open>U8\<close>; \<open>x + 10\<close> is computed at \<^const>\<open>I32\<close> and converted back.
  The value \<open>260\<close> leaves the range of \<^const>\<open>U8\<close> and wraps to \<open>4\<close>, as in Goblint.\<close>

definition wrap_prog :: imp_prog where
  "wrap_prog = program { fun main() { x = 250; x = x + 10; } }"

definition wrap_kinds :: kind_decls where
  "wrap_kinds = [(main_var (STR ''x''), U8)]"

lemma wrap_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join (ivl_equations wrap_kinds wrap_prog)
     (cfg_exit (typed_cfg wrap_prog wrap_kinds), []) \<noteq> None"
  by eval

abbreviation wrap_at :: "pp \<Rightarrow> ivl tabs" where
  "wrap_at \<equiv> ivl_state_at wrap_kinds wrap_prog"

lemma wrap_values:
  "wrap_at (Statement 1) (main_var (STR ''x'')) = KD U8 (Ivl (Fin 250) (Fin 250))"
  "wrap_at (Statement 2) (main_var (STR ''x'')) = KD U8 (Ivl (Fin 4) (Fin 4))"
  by eval+


subsection \<open>A signed char that overflows\<close>

text \<open>A signed kind does not wrap under Goblint's default overflow policy: converting
  \<open>130\<close> to \<^const>\<open>I8\<close> answers the whole range.\<close>

definition swrap_prog :: imp_prog where
  "swrap_prog = program { fun main() { x = 120; x = x + 10; } }"

definition swrap_kinds :: kind_decls where
  "swrap_kinds = [(main_var (STR ''x''), I8)]"

abbreviation swrap_at :: "pp \<Rightarrow> ivl tabs" where
  "swrap_at \<equiv> ivl_state_at swrap_kinds swrap_prog"

lemma swrap_values:
  "swrap_at (Statement 2) (main_var (STR ''x'')) = KD I8 (Ivl (Fin (-128)) (Fin 127))"
  by eval


subsection \<open>Backward refinement through arithmetic and conversions\<close>

text \<open>Two calls give \<open>f\<close>'s formal \<open>x\<close> the range \<open>[0,99]\<close>. Then \<open>x + 1\<close> cannot
  overflow, so \<open>x + 1 < 10\<close> bounds \<open>x\<close> by \<open>8\<close>; without the inversion \<open>y\<close> would be
  \<open>[0,99]\<close> when \<open>f\<close> returns.\<close>

abbreviation f_var :: "vname \<Rightarrow> var_id" where
  "f_var x \<equiv> ScopedId (STR ''f'') x"

definition arith_prog :: imp_prog where
  "arith_prog = program {
     fun f(x) { y = 0; if (x + 1 < 10) { y = x; } }
     fun main() { f(0); f(99); } }"

lemma arith_refined:
  "ivl_state_at [] arith_prog
            (FunctionResult (STR ''f'')) (f_var (STR ''y''))
     = KD I32 (Ivl (Fin 0) (Fin 8))"
  by eval

text \<open>Comparing a signed \<open>x\<close> with an unsigned \<open>y\<close> converts \<open>x\<close> to unsigned. When
  \<open>x\<close> is known non-negative the conversion keeps its value, so \<open>x < y\<close> bounds \<open>x\<close>; when
  \<open>x\<close> may be negative the conversion is not injective on its values and refines
  nothing.\<close>

definition mixed_kinds :: kind_decls where
  "mixed_kinds = [(f_var (STR ''y''), U32)]"

definition mixed_prog :: imp_prog where
  "mixed_prog = program {
     fun f(x) { y = 5; z = 0; if (x < y) { z = x; } }
     fun main() { f(0); f(9); } }"

definition mixed_neg_prog :: imp_prog where
  "mixed_neg_prog = program {
     fun f(x) { y = 5; z = 0; if (x < y) { z = x; } }
     fun main() { f(0 - 10); f(9); } }"

lemma mixed_refined:
  "ivl_state_at mixed_kinds mixed_prog
            (FunctionResult (STR ''f'')) (f_var (STR ''z''))
     = KD I32 (Ivl (Fin 0) (Fin 4))"
  "ivl_state_at mixed_kinds mixed_neg_prog
            (FunctionResult (STR ''f'')) (f_var (STR ''z''))
     = KD I32 (Ivl (Fin (-10)) (Fin 9))"
  by eval+

end
