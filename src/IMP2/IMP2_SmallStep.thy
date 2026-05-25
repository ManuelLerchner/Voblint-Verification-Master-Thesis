theory IMP2_SmallStep
  imports IMP2_Syntax "HOL-IMP.Star"
begin

(*
  IMP2 -- expression evaluation and small-step operational semantics.

  Small-step rules mirror HOL-IMP.Small_Step; aval/bval evaluate the
  IMP2 expression extensions (delegating BaseN/BaseB to Nipkow).
*)

(* -- Expression Evaluation -------------------------------------- *)

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

(* -- Small-Step Semantics --------------------------------------- *)

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
  by (induction arbitrary: cs'' rule: small_step.induct) blast+

subsection \<open>Sequencing and divergence\<close>

lemma star_seq2:
  "(c1, s) \<rightarrow>* (c1', s') \<Longrightarrow> (c1 ;; c2, s) \<rightarrow>* (c1' ;; c2, s')"
proof (induction rule: star_induct)
  case (refl a b)
  show ?case by simp
next
  case (step a1 b1 a2 b2 a3 b3)
  from step.hyps(1) have "(a1 ;; c2, b1) \<rightarrow> (a2 ;; c2, b2)"
    by (rule Seq2)
  with step.IH show ?case
    by (meson star.step)
qed

lemma seq_comp:
  "\<lbrakk> (c1, s1) \<rightarrow>* (SKIP, s2); (c2, s2) \<rightarrow>* (SKIP, s3) \<rbrakk>
   \<Longrightarrow> (c1 ;; c2, s1) \<rightarrow>* (SKIP, s3)"
  by(blast intro: star.step star_seq2 star_trans)

lemma seq_star_finish:
  assumes "(c1 ;; c2, s) \<rightarrow>* (SKIP, t)"
  shows "\<exists>s2. (c1, s) \<rightarrow>* (SKIP, s2) \<and> (c2, s2) \<rightarrow>* (SKIP, t)"
  using assms
proof (induction "(c1 ;; c2, s)" "(SKIP, t)" arbitrary: c1 s rule: star.induct)
  case (step y)
  from step.hyps(1) show ?case
  proof cases
    case Seq1
    with step.hyps(2) show ?thesis by auto
  next
    case (Seq2 c1' s')
    with step.hyps obtain s2 where
      "(c1', s') \<rightarrow>* (SKIP, s2)" "(c2, s2) \<rightarrow>* (SKIP, t)"
      by blast
    with Seq2 show ?thesis by (meson star.step)
  qed
qed
  
subsection \<open>Small-step star inversions by command shape\<close>

text \<open>
  Inversion principles for the small-step reflexive-transitive closure,
  grouped by the shape of the source command.  Used by the
  \<open>small_step \<rightarrow> runs_to\<close> reverse bridge.
\<close>

lemma star_SKIP_eq[dest]:
  assumes "(SKIP, s) \<rightarrow>* (SKIP, t)"
  shows "s = t"
  using assms
proof (induction "(SKIP, s)" "(SKIP, t)" rule: star.induct)
  case refl
  then show ?case by simp
next
  case (step y)
  from step.hyps(1) show ?case by blast
qed

lemma star_Assign_eq[dest]:
  assumes "(x ::= a, s) \<rightarrow>* (SKIP, t)"
  shows "t = s(x := aval a s)"
  using assms
proof (induction "(x ::= a, s)" "(SKIP, t)" rule: star.induct)
  case (step y)
  from step.hyps(1) have "y = (SKIP, s(x := aval a s))" by auto
  with step.hyps(2) show ?case by auto
qed

lemma star_If_cases:
  assumes "(IF b THEN c1 ELSE c2, s) \<rightarrow>* (SKIP, t)"
  shows "(bval b s \<and> (c1, s) \<rightarrow>* (SKIP, t))
       \<or> (\<not> bval b s \<and> (c2, s) \<rightarrow>* (SKIP, t))"
  using assms
proof (induction "(IF b THEN c1 ELSE c2, s)" "(SKIP, t)" rule: star.induct)
  case (step y)
  from step.hyps(1) step.hyps(2) show ?case by auto
qed

lemma star_While_cases:
  assumes "(WHILE b DO c, s) \<rightarrow>* (SKIP, t)"
  shows "(\<not> bval b s \<and> s = t)
       \<or> (\<exists>s'. bval b s \<and> (c, s) \<rightarrow>* (SKIP, s') \<and> (WHILE b DO c, s') \<rightarrow>* (SKIP, t))"
  using assms
proof (induction "(WHILE b DO c, s)" "(SKIP, t)" arbitrary: s rule: star.induct)
  case (step y s)
  from step.hyps(1) have y: "y = (IF b THEN c ;; WHILE b DO c ELSE SKIP, s)"
    by (auto)
  with step.hyps(2) have
    "(IF b THEN c ;; WHILE b DO c ELSE SKIP, s) \<rightarrow>* (SKIP, t)" by simp
  from star_If_cases[OF this] show ?case
  proof
    assume "bval b s \<and> (c ;; WHILE b DO c, s) \<rightarrow>* (SKIP, t)"
    then obtain s' where
      "bval b s" "(c, s) \<rightarrow>* (SKIP, s')" "(WHILE b DO c, s') \<rightarrow>* (SKIP, t)"
      using seq_star_finish by blast
    then show ?case by blast
  next
    assume "\<not> bval b s \<and> (SKIP, s) \<rightarrow>* (SKIP, t)"
    then show ?case using star_SKIP_eq by blast
  qed
qed

end
