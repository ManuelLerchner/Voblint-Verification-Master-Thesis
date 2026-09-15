theory Example_Arithmetic_Diagnostics_Regression
  imports "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.Analysis_Run"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
section \<open>Arithmetic diagnostics through the public CLI operation\<close>

text \<open>
  These executable witnesses inspect the same answer as the text and HTML reports.
  Keeping a malformed program as \<^const>\<open>None\<close> prevents it from passing a silence
  test. These regressions pin concrete output examples;
  they complement the general arithmetic safety theorem.
\<close>

definition arithmetic_example_result where
  "arithmetic_example_result p =
    (case run_voblint Interval_Analysis Globals_Warrow Ctx_EntryState p of
       Analysed res \<Rightarrow> Some
         (map (\<lambda>d. (arithmetic_operation (diagnostic_obligation d),
                      diagnostic_verdict d)) (res_diagnostics res),
          map check_verdict (res_checks res))
     | _ \<Rightarrow> None)"

subsection \<open>One source guard, one finding, and continued total execution\<close>

definition arithmetic_guard_prog :: imp_prog where
  "arithmetic_guard_prog = program {
    fun main() {
      if (10 / 0) { x = 1; } else { x = 2; }
      __voblint_check(x == 2);
    }
  }"

lemma arithmetic_guard_once:
  "arithmetic_example_result arithmetic_guard_prog =
    Some ([(Div (N 10) (N 0), Check_Refuted)], [Lifted Check_Proved])"
  by eval

subsection \<open>Unreachable arithmetic produces no finding\<close>

definition arithmetic_dead_prog :: imp_prog where
  "arithmetic_dead_prog = program {
    fun main() {
      n = 2;
      if (n == 0) {
        x = 10 / 0;
        __voblint_check(x == 0);
      } else {
        __voblint_check(n == 2);
      }
    }
  }"

lemma arithmetic_dead_branch:
  "arithmetic_example_result arithmetic_dead_prog =
    Some ([], [Bot, Lifted Check_Proved])"
  by eval

subsection \<open>Aggregation over live entry-state contexts\<close>

definition arithmetic_mixed_prog :: imp_prog where
  "arithmetic_mixed_prog = program {
    fun f(n) { return 10 / n; }
    fun main() { x = f(0); y = f(2); }
  }"

definition arithmetic_unsafe_prog :: imp_prog where
  "arithmetic_unsafe_prog = program {
    fun f(n) { return 10 / n; }
    fun main() { x = f(0); y = f(0); }
  }"

definition arithmetic_safe_prog :: imp_prog where
  "arithmetic_safe_prog = program {
    fun f(n) { return 10 / n; }
    fun main() { x = f(1); y = f(2); }
  }"

lemma arithmetic_mixed_contexts_warn_once:
  "arithmetic_example_result arithmetic_mixed_prog =
    Some ([(Div (N 10) (V (STR ''n'')), Check_Unknown)], [])"
  by eval

lemma arithmetic_unsafe_contexts_error_once:
  "arithmetic_example_result arithmetic_unsafe_prog =
    Some ([(Div (N 10) (V (STR ''n'')), Check_Refuted)], [])"
  by eval

lemma arithmetic_safe_contexts_silent:
  "arithmetic_example_result arithmetic_safe_prog = Some ([], [])"
  by eval

subsection \<open>Both Boolean operands and remainder are inspected\<close>

definition arithmetic_boolean_prog :: imp_prog where
  "arithmetic_boolean_prog = program {
    fun main() {
      __voblint_check(0 && 1 / 0);
      __voblint_check(1 || 1 % 0);
    }
  }"

lemma arithmetic_boolean_operands:
  "arithmetic_example_result arithmetic_boolean_prog =
    Some ([(Div (N 1) (N 0), Check_Refuted),
           (Mod (N 1) (N 0), Check_Refuted)],
          [Lifted Check_Refuted, Lifted Check_Proved])"
  by eval

end
