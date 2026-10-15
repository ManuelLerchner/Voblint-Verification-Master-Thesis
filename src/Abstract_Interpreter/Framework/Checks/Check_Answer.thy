theory Check_Answer
  imports Contextual_Check_Report
begin

section \<open>A domain's answer to the value of an expression\<close>

text \<open>
  A domain that decides a comparison or logical operator \<open>e\<close> three-valuedly
  answers \<open>EvalInt e\<close> with \<open>bool_answer\<close>: such an expression evaluates to
  \<open>0\<close> or \<open>1\<close>, so a decided truth value is the exact integer, and an undecided
  one is the interval \<open>[0, 1]\<close>. \<open>classify_bool_answer\<close> reads the verdict back.
\<close>

definition bool_answer :: "bool option \<Rightarrow> answer" where
  "bool_answer r =
     (case r of
        Some b \<Rightarrow> answer_of_int (if b then 1 else 0)
      | None \<Rightarrow> answer_of_ivl (Ivl (Fin 0) (Fin 1)))"

lemma classify_answer_gamma:
  "a \<noteq> QBot \<Longrightarrow> classify_answer a =
     Decided (if 0 \<notin> gamma_answer a then Check_Proved
              else if 1 \<notin> gamma_answer a then Check_Refuted else Check_Unknown)"
  using answer_excludes_iff[of 0 a] answer_excludes_iff[of 1 a]
  by (cases a) (auto simp del: answer_excludes.simps)

lemma classify_answer_of_int:
  "classify_answer (answer_of_int 1) = Decided Check_Proved"
  "classify_answer (answer_of_int 0) = Decided Check_Refuted"
  by (simp_all add: answer_of_int_def is_bottom_int_dom_correct)

lemma classify_bool_answer:
  "classify_answer (bool_answer r) =
     Decided (case r of Some True \<Rightarrow> Check_Proved | Some False \<Rightarrow> Check_Refuted
                      | None \<Rightarrow> Check_Unknown)"
proof (cases r)
  case None
  have "answer_of_ivl (Ivl (Fin 0) (Fin 1)) \<noteq> QBot"
    by (simp add: answer_of_ivl_def)
  with None show ?thesis
    by (simp add: bool_answer_def classify_answer_gamma)
qed (auto simp: bool_answer_def classify_answer_of_int)

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
  expressions: \<open>tx c\<close> evaluates to \<open>1\<close> where \<open>c\<close> holds and to \<open>0\<close> elsewhere.
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
  then have "?a \<noteq> QBot" by auto
  then show "answer_check tx q c v = Check_Proved \<Longrightarrow> truthy (ev c s)"
    and "answer_check tx q c v = Check_Refuted \<Longrightarrow> \<not> truthy (ev c s)"
    using val by (auto simp: answer_check_def classify_answer_gamma split: if_splits)
qed

end
