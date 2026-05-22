theory IMP2_Semantics
  imports IMP2_Syntax "HOL-IMP.Star"
begin

(*
  IMP2 -- Operational Semantics.

  Expression evaluation and big-step semantics for commands.
  Concrete syntax \<open>(c,s) \<Rightarrow> t\<close> follows HOL-IMP.Big_Step (same command
  constructors; IMP2 only extends aexp/bexp).
*)

(* \<midarrow>\<midarrow> Expression Evaluation \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

fun aval :: "aexp => store => int" where
    "aval (BaseN a)   s  = AExp.aval a s"
  | "aval (Plus  a b) s  = aval a s + aval b s"
  | "aval (Minus a b) s  = aval a s - aval b s"
  | "aval (Times a b) s  = aval a s * aval b s"

fun bval :: "bexp => store => bool" where
    "bval (BaseB b)   s  = BExp.bval b s"
  | "bval (Not b)     s  = (\<not> bval b s)"
  | "bval (And b1 b2) s  = (bval b1 s \<and> bval b2 s)"
  | "bval (Or  b1 b2) s  = (bval b1 s \<or> bval b2 s)"
  | "bval (Less a b)  s  = (aval a s < aval b s)"
  | "bval (Eq   a b)  s  = (aval a s = aval b s)"

(* \<midarrow>\<midarrow> Big-Step Semantics (HOL-IMP style) \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

text \<open>Same rule structure as HOL-IMP.Big\_Step; first parameter is a pair.\<close>

inductive
  big_step :: "com \<times> store \<Rightarrow> store \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
  Skip: "(SKIP,s) \<Rightarrow> s"
| Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)"
| Seq: "\<lbrakk> (c1,s) \<Rightarrow> s'; (c2,s') \<Rightarrow> s'' \<rbrakk> \<Longrightarrow> (c1 ;; c2, s) \<Rightarrow> s''"
| IfTrue: "\<lbrakk> bval b s; (c1,s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> s'"
| IfFalse: "\<lbrakk> \<not> bval b s; (c2,s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> s'"
| WhileFalse: "\<not> bval b s \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> s"
| WhileTrue:
    "\<lbrakk> bval b s; (c,s) \<Rightarrow> s'; (WHILE b DO c, s') \<Rightarrow> s'' \<rbrakk>
     \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> s''"

text \<open>Introduction rules: unsafe \<open>intro\<close> (backtracking on recursive rules).\<close>

declare big_step.intros [intro]

lemmas big_step_induct = big_step.induct[split_format(complete)]

subsection \<open>Rule inversion\<close>

text \<open>
  Elimination rules for \<open>auto\<close>/\<open>blast\<close>.  Eager \<open>elim!\<close> except for \<open>WhileE\<close>:
  \<open>WhileE\<close> is only \<open>elim\<close> because \<open>elim!\<close> would not terminate (HOL-IMP.Big\_Step).
\<close>

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1 ;; c2, s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<Rightarrow> t"

text \<open>Executable big-step via the predicate compiler (HOL-IMP.Big\_Step).\<close>

code_pred big_step .

subsection \<open>Execution is deterministic\<close>

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t1; (c,s) \<Rightarrow> t2 \<rbrakk> \<Longrightarrow> t1 = t2"
   by (induction arbitrary: t2 rule: big_step.induct) blast+


(* -- Small-Step Semantics (HOL-IMP style) ------------------------- *)

text \<open>
  Small-step transitions over our extended IMP. Mirrors HOL-IMP.Small\_Step;
  rules are the standard ones, reusing our \<open>aval\<close>/\<open>bval\<close>.

  Kept alongside \<open>big_step\<close>:
  \<^item> \<open>big_step\<close> is the specification-side predicate (Hoare-friendly, executable).
  \<^item> \<open>small_step\<close> is the operational basis used by the per-program-point
    soundness chain (\<open>pipeline_sound_small_step\<close>, planned).
  \<^item> The bridge \<open>small_step_big_step_eq\<close> below relates the two; consumers
    that need the other view rewrite by it.
\<close>

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
