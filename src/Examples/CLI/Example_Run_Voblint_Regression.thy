theory Example_Run_Voblint_Regression
  imports "Voblint_CLI.Run_Voblint"
begin

text \<open>
  \<^const>\<open>run_voblint\<close> on the programs the generated OCaml module's regression driver
  runs (\<^verbatim>\<open>codegen/regression/ocaml/codegen_regression.ml\<close>), pinned here by
  evaluation so the driver pins the generated module's agreement with Isabelle. The
  programs declare no kinds, so every variable is an \<^const>\<open>I32\<close>.
\<close>

definition demo_prog :: imp_prog where
  "demo_prog =
     program {
       fun main() {
         y = 1;
         __voblint_check(0 < y);
         y = 0 - 1;
         __voblint_check(0 < y);
       }
     }"

definition demo_conf :: "analysis list \<Rightarrow> voblint_conf" where
  "demo_conf as = \<lparr>conf_analyses = as, conf_context = Call_String 0,
     conf_globals = Globals_Warrow, conf_program_globals = Program_Globals_Flow_Sensitive,
     conf_sem = default_sem_conf\<rparr>"

definition run_checks :: "analysis list \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> contextual_verdict) list option"
  where
  "run_checks as p =
     (case run_voblint (demo_conf as) [] p of
        Analysed res \<Rightarrow> Some (map (\<lambda>c. (check_point c, check_verdict c)) (report_checks res))
      | _ \<Rightarrow> None)"

definition proc_demo_prog :: imp_prog where
  "proc_demo_prog =
     program {
       global total;
       fun inc(n) { total = total + n; }
       fun main() {
         total = 0;
         inc(3);
         inc(4);
         __voblint_check(0 < total);
         __voblint_check(total < 100);
       }
     }"

definition no_call_global_self_ref_prog :: imp_prog where
  "no_call_global_self_ref_prog =
     program {
       global total;
       fun main() {
         total = 0;
         total = total + 3;
         __voblint_check(0 < total);
       }
     }"

definition one_call_prog :: imp_prog where
  "one_call_prog =
     program {
       global total;
       fun inc(n) { total = total + n; }
       fun main() {
         total = 0;
         inc(3);
         __voblint_check(0 < total);
       }
     }"

text \<open>Straight-line code: both domains settle both checks.\<close>

lemma demo_sign: "run_checks [Sign] demo_prog
    = Some [(Statement 1, Decided Check_Proved), (Statement 3, Decided Check_Refuted)]"
  by eval

lemma demo_interval: "run_checks [Interval] demo_prog
    = Some [(Statement 1, Decided Check_Proved), (Statement 3, Decided Check_Refuted)]"
  by eval

text \<open>
  Two calls grow a global. Without contexts the two calls share \<open>inc\<close>'s entry, so
  \<open>total + n\<close> at \<open>i32\<close> may overflow under the default \<^verbatim>\<open>assume_top\<close> and both domains
  lose the bound: neither check is decided.
\<close>

lemma proc_demo_sign: "run_checks [Sign] proc_demo_prog
    = Some [(Statement 5, Decided Check_Unknown), (Statement 6, Decided Check_Unknown)]"
  by eval

lemma proc_demo_interval: "run_checks [Interval] proc_demo_prog
    = Some [(Statement 5, Decided Check_Unknown), (Statement 6, Decided Check_Unknown)]"
  by eval

text \<open>A global written from its own value, with no call and through one call: the
  exact value survives, so the check is proved.\<close>

lemma no_call_global_self_ref_interval: "run_checks [Interval] no_call_global_self_ref_prog
    = Some [(Statement 2, Decided Check_Proved)]"
  by eval

lemma one_call_interval: "run_checks [Interval] one_call_prog
    = Some [(Statement 4, Decided Check_Proved)]"
  by eval

end
