theory Check_Answer
  imports Abstract_Checks Contextual_Check_Report
begin

section \<open>A domain's answer to the value of an expression\<close>

text \<open>
  A domain with a check decision procedure answers \<open>EvalInt e\<close> for every
  comparison or logical operator \<open>e\<close>: such an expression evaluates to \<open>0\<close> or
  \<open>1\<close>, so a decided \<^const>\<open>sound_check_query.check_query\<close> is the
  exact integer, and an undecided one is the interval \<open>[0, 1]\<close>. Other
  expressions it declines with \<open>\<top>\<close>. A check is then classified from this
  answer exactly as the domain's own \<open>classify_check\<close> classified it.
\<close>

definition bool_answer :: "bool option \<Rightarrow> answer" where
  "bool_answer r =
     (case r of
        Some b \<Rightarrow> answer_of_int (if b then 1 else 0)
      | None \<Rightarrow> answer_of_ivl (Ivl (Fin 0) (Fin 1)))"

lemma classify_answer_of_int:
  "classify_answer (answer_of_int 1) = Decided Check_Proved"
  "classify_answer (answer_of_int 0) = Decided Check_Refuted"
  using answer_const_of_int[of 1] answer_const_of_int[of 0]
  by (simp_all add: answer_of_int_def int_dom_of_int_def del: answer_const.simps)

lemma answer_const_bool_range: "answer_const (answer_of_ivl (Ivl (Fin 0) (Fin 1))) = None"
proof -
  have "congruence_constant (\<top> :: congruence) = None"
    by (cases "congruence_constant (\<top> :: congruence)")
       (auto dest!: gamma_congruence_constant simp: set_eq_iff, presburger)
  then show ?thesis
    by (simp add: answer_of_ivl_def int_dom_constant_def top_int_dom_ext_def top_sign_def)
qed

lemma classify_bool_answer:
  "classify_answer (bool_answer r) =
     Decided (case r of Some True \<Rightarrow> Check_Proved | Some False \<Rightarrow> Check_Refuted
                      | None \<Rightarrow> Check_Unknown)"
proof (cases r)
  case None
  then show ?thesis
    using answer_const_bool_range
    by (simp add: bool_answer_def answer_of_ivl_def top_int_dom_ext_def top_sign_def
        top_parity_def less_eint_def less_eq_eint_def)
qed (auto simp: bool_answer_def classify_answer_of_int)

context sound_check_query
begin

fun eval_answer :: "'d \<Rightarrow> query \<Rightarrow> answer" where
  "eval_answer d (EvalInt e) = (if bool_valued e then bool_answer (check_query e d) else \<top>)"

lemma eval_answer_sound:
  assumes mem: "s \<in> \<gamma>\<^sub>S d"
  shows "eval_holds q (eval_answer d q) s"
proof (cases q)
  case (EvalInt e)
  show ?thesis
  proof (cases "bool_valued e")
    case True
    have v: "\<lbrakk>e\<rbrakk>\<^sub>e s = (if truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) then 1 else 0)"
      by (rule aval_bool_valued[OF True])
    show ?thesis
    proof (cases "check_query e d")
      case None
      then show ?thesis
        using EvalInt True v by (simp add: bool_answer_def split: if_splits)
    next
      case (Some b)
      have "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = b"
        by (rule check_query_sound[OF mem Some])
      then show ?thesis
        using EvalInt True v Some by (simp add: bool_answer_def split: if_splits)
    qed
  qed (simp add: EvalInt)
qed

lemma check_query_check_truth_exp: "check_query (check_truth_exp c) d = check_query c d"
  by (cases c) (simp_all add: check_truth_exp_def truthy_query_def)

theorem classify_eval_answer:
  "classify_answer (eval_answer d (check_query_of c)) = Decided (classify_check c d)"
  by (simp add: check_query_check_truth_exp classify_bool_answer classify_check_def
      split: option.splits bool.splits)

end

section \<open>Deciding a check from an answer\<close>

text \<open>
  The one check consumer: ask the state's handler the check's question and read
  the verdict off the answer, as Goblint's \<open>assert\<close> analysis reads
  \<open>Queries.eval_bool\<close>. \<^const>\<open>classify_answer\<close> reads an answer that
  admits no value as \<^const>\<open>Dead\<close>, but the consumer reports it as
  \<^const>\<open>Check_Unknown\<close>: a check is reported dead only where the state
  itself is \<^const>\<open>Bot\<close>, never from the answer to its query.
\<close>

text \<open>
  The question is the check's truth value, which a language spells with its own
  expressions: \<open>tx c\<close> evaluates to \<open>1\<close> where \<open>c\<close> holds and to \<open>0\<close> elsewhere. For the
  untyped language it is \<^const>\<open>check_truth_exp\<close>.
\<close>

definition answer_check ::
    "('e \<Rightarrow> 'e) \<Rightarrow> ('v \<Rightarrow> 'e gquery \<Rightarrow> answer) \<Rightarrow> 'e \<Rightarrow> 'v \<Rightarrow> check_result" where
  "answer_check tx q c v =
     (case classify_answer (q v (EvalInt (tx c))) of Decided r \<Rightarrow> r | _ \<Rightarrow> Check_Unknown)"

lemma answer_check_gsound:
  assumes truth: "ev (tx c) s = (if truthy (ev c s) then 1 else 0)"
    and holds: "geval_holds ev (EvalInt (tx c)) (q v (EvalInt (tx c))) s"
  shows answer_check_gproved: "answer_check tx q c v = Check_Proved \<Longrightarrow> truthy (ev c s)"
    and answer_check_grefuted: "answer_check tx q c v = Check_Refuted \<Longrightarrow> \<not> truthy (ev c s)"
proof -
  let ?a = "q v (EvalInt (tx c))"
  have val: "(if truthy (ev c s) then 1 else 0) \<in> gamma_answer ?a"
    using holds truth by simp
  show "answer_check tx q c v = Check_Proved \<Longrightarrow> truthy (ev c s)"
  proof -
    assume "answer_check tx q c v = Check_Proved"
    then have "answer_const ?a = Some 1 \<or> answer_nonzero ?a"
      by (cases ?a rule: classify_answer.cases)
         (auto simp: answer_check_def split: if_splits
           simp del: answer_const.simps answer_nonzero.simps)
    then show "truthy (ev c s)"
    proof
      assume "answer_const ?a = Some 1"
      with val show ?thesis
        by (cases ?a) (auto split: if_splits dest!: gamma_int_dom_constant_subset)
    next
      assume "answer_nonzero ?a"
      from answer_nonzero_gamma[OF this val] show ?thesis by (simp split: if_splits)
    qed
  qed
  show "answer_check tx q c v = Check_Refuted \<Longrightarrow> \<not> truthy (ev c s)"
    using val
    by (cases ?a rule: classify_answer.cases)
       (auto simp: answer_check_def split: if_splits option.splits
         simp del: answer_nonzero.simps dest!: gamma_int_dom_constant_subset)
qed

lemma answer_check_proved:
  assumes "answer_check check_truth_exp q c v = Check_Proved"
    and "eval_holds (check_query_of c) (q v (check_query_of c)) s"
  shows "truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
  using answer_check_gproved[where ev = aval and tx = check_truth_exp, OF aval_check_truth_exp] assms
  by simp

lemma answer_check_refuted:
  assumes "answer_check check_truth_exp q c v = Check_Refuted"
    and "eval_holds (check_query_of c) (q v (check_query_of c)) s"
  shows "\<not> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
  using answer_check_grefuted[where ev = aval and tx = check_truth_exp, OF aval_check_truth_exp] assms
  by simp

lemma (in sound_check_query) answer_check_eval_answer:
  "answer_check check_truth_exp eval_answer = classify_check"
  by (simp add: fun_eq_iff answer_check_def classify_eval_answer del: eval_answer.simps)

end
