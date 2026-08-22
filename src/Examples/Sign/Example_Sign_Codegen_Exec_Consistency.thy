theory Example_Sign_Codegen_Exec_Consistency
  imports Exec_Sign_DG_Run "Voblint_CLI.Sign_Entry"
begin

text \<open>
  \<open>gEx\<close>, \<open>dgEx_eqs\<close>, and \<open>dgEx_sol\<close> (\<open>Exec_Sign_DG_Run\<close>, this session) really are the
  \<open>gs = sign_ex_gs\<close>, \<open>p = sign_ex_prog\<close> instance of \<open>Example_Sign_Codegen\<close>'s
  arbitrary-classifier, arbitrary-program chain, not a separate parallel definition.
\<close>

lemma gEx_prog_cfg: "gEx = prog_cfg prog_main_name sign_ex_prog"
  unfolding gEx_def prog_cfg_def sign_ex_pi_def by simp

lemma dgEx_eqs_is_analyse_sign_eqs: "dgEx_eqs = analyse_sign_eqs sign_ex_prog"
  unfolding dgEx_eqs_def analyse_sign_eqs_def analyse_sign_eqs_for_def gEx_prog_cfg by simp

lemma dgEx_sol_is_analyse_sign: "dgEx_sol = analyse_sign sign_ex_prog"
  unfolding dgEx_sol_def analyse_sign_def analyse_sign_for_def dgEx_eqs_is_analyse_sign_eqs
    analyse_sign_eqs_def gEx_prog_cfg by simp

end
