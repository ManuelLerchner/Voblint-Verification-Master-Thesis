theory Example_Run_Voblint_Precision
  imports
    "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.Run_Voblint"
begin

section \<open>Precision of the public run, per analysis and option\<close>

text \<open>
  \<^const>\<open>run_voblint\<close> on small programs whose verdicts change with the activated
  analyses, the context policy or the signed-overflow option, pinned by evaluation.
\<close>

definition prec_conf :: "typed_domain list \<Rightarrow> typed_context \<Rightarrow> sem_conf \<Rightarrow> voblint_conf" where
  "prec_conf as cx sem = \<lparr>conf_analyses = as, conf_context = cx,
     conf_globals = Globals_Join, conf_program_globals = Program_Globals_Flow_Sensitive,
     conf_sem = sem\<rparr>"

definition verdicts :: "voblint_conf \<Rightarrow> imp_prog \<Rightarrow> contextual_verdict list option" where
  "verdicts conf p =
     (case run_voblint conf [] p of
        Analysed res \<Rightarrow> Some (map check_verdict (report_checks res))
      | _ \<Rightarrow> None)"

subsection \<open>One check, six analyses\<close>

text \<open>After the loop, \<open>x == 99\<close> needs both the bound and the class: Interval sees
  \<open>[99, 101]\<close>, Congruence alone loses the class to a possible wraparound, and only
  their reduced product decides the check.\<close>

definition step_prog :: imp_prog where
  "step_prog = program {
     fun main() { x = 0; while (x < 99) { x = x + 3; } __voblint_check(x == 99); } }"

lemma step_verdicts:
  "verdicts (prec_conf [Typed_Interval] (Typed_Call_String 0) default_sem_conf) step_prog
     = Some [Decided Check_Unknown]"
  "verdicts (prec_conf [Typed_Congruence] (Typed_Call_String 0) default_sem_conf) step_prog
     = Some [Decided Check_Unknown]"
  "verdicts (prec_conf [Typed_Int Refine_Fixpoint] (Typed_Call_String 0) default_sem_conf) step_prog
     = Some [Decided Check_Proved]"
  "verdicts (prec_conf [Typed_Order] (Typed_Call_String 0) default_sem_conf) step_prog
     = Some [Decided Check_Unknown]"
  "verdicts (prec_conf [Typed_Sign] (Typed_Call_String 0) default_sem_conf) step_prog
     = Some [Decided Check_Unknown]"
  "verdicts (prec_conf [Typed_Parity] (Typed_Call_String 0) default_sem_conf) step_prog
     = Some [Decided Check_Unknown]"
  by eval+

subsection \<open>Contexts\<close>

text \<open>\<open>inc\<close> is called with \<open>1\<close> and with \<open>10\<close>. Without contexts its two activations
  share one state, so each call's result lies in \<open>[2, 11]\<close> and neither check is decided.
  A call string of length \<open>1\<close> separates the two call sites, and so does the entry state,
  whose context is the value of \<open>x\<close>: both checks are proved either way.\<close>

definition calls_prog :: imp_prog where
  "calls_prog = program {
     fun inc(x) { return x + 1; }
     fun main() { a = inc(1); __voblint_check(a == 2); b = inc(10); __voblint_check(b == 11); } }"

lemma call_string_verdicts:
  "verdicts (prec_conf [Typed_Interval] (Typed_Call_String 0) default_sem_conf) calls_prog
     = Some [Decided Check_Unknown, Decided Check_Unknown]"
  "verdicts (prec_conf [Typed_Interval] (Typed_Call_String 1) default_sem_conf) calls_prog
     = Some [Decided Check_Proved, Decided Check_Proved]"
  "verdicts (prec_conf [Typed_Interval] Typed_Entry_State default_sem_conf) calls_prog
     = Some [Decided Check_Proved, Decided Check_Proved]"
  by eval+

subsection \<open>Signed overflow\<close>

text \<open>
  The concrete semantics wraps \<open>INT_MAX + 1\<close> to \<open>INT_MIN\<close>. Under Goblint's default
  \<^verbatim>\<open>assume_top\<close> the signed overflow gives Interval the kind's top, and the check is
  unknown; under \<^verbatim>\<open>assume_wraparound\<close> Interval wraps as the concrete semantics does and
  proves it.
\<close>

definition overflow_prog :: imp_prog where
  "overflow_prog = program {
     fun main() { x = 2147483647; x = x + 1; __voblint_check(x < 0); } }"

definition wrap_sem :: sem_conf where
  "wrap_sem = \<lparr>sem_int_signed_overflow = Assume_Wraparound\<rparr>"

lemma overflow_verdicts:
  "verdicts (prec_conf [Typed_Interval] (Typed_Call_String 0) default_sem_conf) overflow_prog
     = Some [Decided Check_Unknown]"
  "verdicts (prec_conf [Typed_Interval] (Typed_Call_String 0) wrap_sem) overflow_prog
     = Some [Decided Check_Proved]"
  "verdicts (prec_conf [Typed_Int Refine_Never] (Typed_Call_String 0) default_sem_conf) overflow_prog
     = Some [Decided Check_Unknown]"
  "verdicts (prec_conf [Typed_Int Refine_Never] (Typed_Call_String 0) wrap_sem) overflow_prog
     = Some [Decided Check_Proved]"
  by eval+

end
