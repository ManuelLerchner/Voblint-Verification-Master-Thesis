theory Example_Congruence_DG_Run
  imports
    "Voblint_Analysis_Congruence.Congruence_Entry"
    "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

section \<open>End-to-end Congruence analysis on the D/G pipeline\<close>

text \<open>
  This straight-line program keeps the witness small while exercising the full
  route: VIMP compilation, D/G equation generation, the verified solver, and
  the published Congruence result table.  Reading both variables through one
  option distinguishes a live exit from \<open>Bot\<close> and pins informative values.
\<close>

definition congruence_dg_program :: imp_prog where
  "congruence_dg_program = program {
     fun main() {
       x = 1;
       y = x + 2;
     }
   }"

definition congruence_dg_exit_xy :: "(congruence \<times> congruence) option" where
  "congruence_dg_exit_xy =
     (case lookup_context (analyse_congruence_result congruence_dg_program)
         (cfg_exit (prog_cfg congruence_dg_program)) () of
        Bot \<Rightarrow> None
      | Lifted st \<Rightarrow> Some (st (STR ''x''), st (STR ''y'')))"

lemma congruence_dg_terminates:
  "congruence_conf_terminates_prog
     (declared_global congruence_dg_program) congruence_dg_program"
  by (rule congruence_conf_terminates_prog_via_solve_c;
      unfold congruence_dg_program_def; eval)

lemma congruence_dg_exit_informative:
  "congruence_dg_exit_xy =
     Some (congruence_of_int 1, congruence_of_int 3)"
  unfolding congruence_dg_exit_xy_def congruence_dg_program_def
  by eval

end
