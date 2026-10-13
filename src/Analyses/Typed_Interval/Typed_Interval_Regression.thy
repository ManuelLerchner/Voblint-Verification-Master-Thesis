theory Typed_Interval_Regression
  imports Typed_Interval_Analysis "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: the typed Interval analysis, executed\<close>

text \<open>
  Each case runs the certified solver on a typed program inside Isabelle and pins the
  published value of one variable. Termination is decided by evaluation, so the
  end-to-end theorems of \<open>Typed_Interval_Analysis\<close> apply to these runs.
\<close>

definition tt_at :: "'a tabs toplift \<Rightarrow> var_id \<Rightarrow> 'a kd" where
  "tt_at d v = (case d of TTop \<Rightarrow> KTop | TL \<sigma> \<Rightarrow> \<sigma> v)"

abbreviation main_var :: "vname \<Rightarrow> var_id" where
  "main_var x \<equiv> ScopedId (STR ''main'') x"

subsection \<open>A counting loop at \<^const>\<open>I32\<close>\<close>

text \<open>The guard bounds the body and the loop exit, as in the untyped flagship.\<close>

definition loop_prog :: imp_prog where
  "loop_prog = program { fun main() { x = 0; while (x < 20) { x = x + 1; } } }"

lemma loop_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join (typed_interval.equations [] tglobal loop_prog)
     (cfg_exit (typed_cfg loop_prog []), ()) \<noteq> None"
  by eval

lemma loop_terminates: "typed_interval.terminates [] Globals_Join tglobal loop_prog"
  unfolding typed_interval.terminates_code
  using TD_side_rule_Interp.solve_dom_of_solve_c[OF loop_terminates_c] by simp

abbreviation loop_at :: "pp \<Rightarrow> ivl tabs toplift" where
  "loop_at \<equiv> typed_interval.state_at [] Globals_Join tglobal loop_prog ()"

lemma loop_values:
  "tt_at (loop_at (Statement 1)) (main_var (STR ''x'')) = KD I32 (Ivl (Fin 0) (Fin 20))"
  "tt_at (loop_at (Statement 2)) (main_var (STR ''x'')) = KD I32 (Ivl (Fin 0) (Fin 19))"
  "tt_at (loop_at (Statement 3)) (main_var (STR ''x'')) = KD I32 (Ivl (Fin 20) (Fin 20))"
  by eval+

subsection \<open>An unsigned char that wraps\<close>

text \<open>\<open>x\<close> is a \<^const>\<open>U8\<close>; \<open>x + 10\<close> is computed at \<^const>\<open>I32\<close> and converted back.
  The value \<open>260\<close> leaves the range of \<^const>\<open>U8\<close> and wraps to \<open>4\<close>, as in Goblint.\<close>

definition wrap_prog :: imp_prog where
  "wrap_prog = program { fun main() { x = 250; x = x + 10; } }"

definition wrap_kinds :: kind_decls where
  "wrap_kinds = [(main_var (STR ''x''), U8)]"

lemma wrap_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join (typed_interval.equations wrap_kinds tglobal wrap_prog)
     (cfg_exit (typed_cfg wrap_prog wrap_kinds), ()) \<noteq> None"
  by eval

abbreviation wrap_at :: "pp \<Rightarrow> ivl tabs toplift" where
  "wrap_at \<equiv> typed_interval.state_at wrap_kinds Globals_Join tglobal wrap_prog ()"

lemma wrap_values:
  "tt_at (wrap_at (Statement 1)) (main_var (STR ''x'')) = KD U8 (Ivl (Fin 250) (Fin 250))"
  "tt_at (wrap_at (Statement 2)) (main_var (STR ''x'')) = KD U8 (Ivl (Fin 4) (Fin 4))"
  by eval+


subsection \<open>A signed char that overflows\<close>

text \<open>A signed kind does not wrap under Goblint's default overflow policy: converting
  \<open>130\<close> to \<^const>\<open>I8\<close> answers the whole range.\<close>

definition swrap_prog :: imp_prog where
  "swrap_prog = program { fun main() { x = 120; x = x + 10; } }"

definition swrap_kinds :: kind_decls where
  "swrap_kinds = [(main_var (STR ''x''), I8)]"

abbreviation swrap_at :: "pp \<Rightarrow> ivl tabs toplift" where
  "swrap_at \<equiv> typed_interval.state_at swrap_kinds Globals_Join tglobal swrap_prog ()"

lemma swrap_values:
  "tt_at (swrap_at (Statement 2)) (main_var (STR ''x'')) = KD I8 (Ivl (Fin (-128)) (Fin 127))"
  by eval

end
