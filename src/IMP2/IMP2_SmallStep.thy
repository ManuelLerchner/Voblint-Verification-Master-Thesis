theory IMP2_SmallStep
  imports IMP2_BigStep "HOL-IMP.Star"
begin

(*
  IMP2 -- Small-Step Operational Semantics.

  Small-step transitions over our extended IMP. Mirrors HOL-IMP.Small\_Step;
  rules are the standard ones, reusing our `aval`/`bval`.
*)

inductive
  small_step :: "com \<times> store \<Rightarrow> com \<times> store \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
  Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))"
| Seq1:    "(SKIP ;; c2, s) \<rightarrow> (c2, s)"
| Seq2:    "(c1, s) \<rightarrow> (c1', s') \<Longrightarrow> (c1 ;; c2, s) \<rightarrow> (c1' ;; c2, s')"
| IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<rightarrow> (c1, s)"
| IfFalse: "\<not> bval b s \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<rightarrow> (c2, s)"
| While:   "(WHILE b DO c, s) \<rightarrow> (IF b THEN c ;; WHILE b DO c ELSE SKIP, s)"

abbreviation
  small_steps :: "com \<times> store \<Rightarrow> com \<times> store \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y \<equiv> star small_step x y"

lemmas small_step_induct = small_step.induct[split_format(complete)]

declare small_step.intros [simp, intro]

inductive_cases SkipSE[elim!]:   "(SKIP, s) \<rightarrow> ct"
inductive_cases AssignSE[elim!]: "(x ::= a, s) \<rightarrow> ct"
inductive_cases SeqSE[elim]:     "(c1 ;; c2, s) \<rightarrow> ct"
inductive_cases IfSE[elim!]:     "(IF b THEN c1 ELSE c2, s) \<rightarrow> ct"
inductive_cases WhileSE[elim]:   "(WHILE b DO c, s) \<rightarrow> ct"

text \<open>Executable small-step via the predicate compiler.\<close>

code_pred small_step .

subsection \<open>Small-step is deterministic\<close>

lemma small_step_deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
  apply (induction arbitrary: cs'' rule: small_step.induct)
  apply blast+
  done


subsection \<open>Equivalence with big-step\<close>

lemma star_seq2:
  "(c1, s) \<rightarrow>* (c1', s') \<Longrightarrow> (c1 ;; c2, s) \<rightarrow>* (c1' ;; c2, s')"
proof (induction rule: star_induct)
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis Seq2 star.step)
qed

lemma seq_comp:
  "\<lbrakk> (c1, s1) \<rightarrow>* (SKIP, s2); (c2, s2) \<rightarrow>* (SKIP, s3) \<rbrakk>
   \<Longrightarrow> (c1 ;; c2, s1) \<rightarrow>* (SKIP, s3)"
  by (blast intro: star.step star_seq2 star_trans)

lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP, t)"
proof (induction rule: big_step.induct)
  case Skip show ?case by simp
next
  case Assign show ?case by blast
next
  case Seq thus ?case by (blast intro: seq_comp)
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case
    by (metis star.step star_step1 small_step.IfFalse small_step.While)
next
  case WhileTrue thus ?case
    by (metis While seq_comp small_step.IfTrue star.step[of small_step])
qed

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
  apply (induction arbitrary: t rule: small_step.induct)
  apply auto
  done

lemma small_to_big:
  "cs \<rightarrow>* (SKIP, t) \<Longrightarrow> cs \<Rightarrow> t"
  apply (induction cs "(SKIP, t)" rule: star.induct)
  apply (auto intro: small1_big_continue)
  done

theorem small_step_big_step_eq:
  "cs \<Rightarrow> t \<longleftrightarrow> cs \<rightarrow>* (SKIP, t)"
  by (metis big_to_small small_to_big)

end
