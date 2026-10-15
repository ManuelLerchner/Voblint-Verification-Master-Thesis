theory Example_Sign_Mixed_Flow
  imports
    "Voblint_VIMP.VIMP_Notation" "Voblint_CLI.Run_Voblint"
begin

section \<open>A mixed flow-sensitive analysis, sound end to end for one program\<close>

text \<open>
  One procedure writes a program global and another reads it, so its value crosses
  the calls only through the global. With flow-insensitive program globals the
  analyzer keeps \<open>Gx\<close> in one value at its own unknown: the initial \<open>0\<close> and the write
  \<open>1\<close> join to non-negative, while \<open>x\<close> stays a flow-sensitive local. The run is the
  public \<^const>\<open>run_voblint\<close>, so its soundness is the published theorem and nothing
  here is proved about the placement itself.
\<close>

definition mf_program :: imp_prog where
  "mf_program = program {
     global Gx;
     fun set() { Gx = 1; }
     fun get() { return Gx; }
     fun main() {
       x = 1;
       set();
       y = get();
       __voblint_check(0 < x);
       __voblint_check(0 <= y);
     }
   }"

definition mf_conf :: voblint_conf where
  "mf_conf = \<lparr>conf_analyses = [Sign], conf_context = Call_String 0,
     conf_globals = Globals_Join, conf_program_globals = Program_Globals_Flow_Insensitive,
     conf_sem = default_sem_conf\<rparr>"

lemma mf_report:
  "(case run_voblint mf_conf [] mf_program of
      Analysed res \<Rightarrow>
        map check_verdict (report_checks res) = [Decided Check_Proved, Decided Check_Proved]
    | _ \<Rightarrow> False)"
  by eval

text \<open>
  Every check a source run reaches holds there. The verdicts are computed; that a
  \<^const>\<open>Check_Proved\<close> verdict holds of the run's store is \<open>run_voblint_check_sound\<close>.
\<close>

theorem mf_checks_hold:
  assumes s0: "s0 \<in> init_stores (kenv_of [])"
    and exec: "star (pstep (kenv_of []) (elab_ptable mf_program []))
                 (main_body (elab_ptable mf_program []), s0, []) (residual, s, frs)"
    and chk: "next_check residual = Some (l, e)"
  shows "truthy (eval e s)"
proof -
  obtain res where ans: "run_voblint mf_conf [] mf_program = Analysed res"
    and verdicts: "map check_verdict (report_checks res)
                     = [Decided Check_Proved, Decided Check_Proved]"
    using mf_report by (cases "run_voblint mf_conf [] mf_program") auto
  from run_voblint_check_sound [OF ans s0 exec chk]
  obtain c where listed: "c \<in> set (report_checks res)"
    and proved: "check_verdict c = Decided Check_Proved \<longrightarrow> truthy (eval e s)"
    by blast
  have "check_verdict c \<in> set (map check_verdict (report_checks res))"
    using listed by simp
  then have "check_verdict c = Decided Check_Proved"
    unfolding verdicts by simp
  with proved show ?thesis by simp
qed

end

