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
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis Seq2 star.step)
qed

lemma seq_comp:
  "\<lbrakk> (c1, s1) \<rightarrow>* (SKIP, s2); (c2, s2) \<rightarrow>* (SKIP, s3) \<rbrakk>
   \<Longrightarrow> (c1 ;; c2, s1) \<rightarrow>* (SKIP, s3)"
  by (blast intro: star.step star_seq2 star_trans)

lemma seq_star_finish:
  "(c1 ;; c2, s) \<rightarrow>* (SKIP, t) \<Longrightarrow>
   (\<exists>s2. (c1, s) \<rightarrow>* (SKIP, s2) \<and> (c2, s2) \<rightarrow>* (SKIP, t))"
  by (induction "(c1 ;; c2, s)" "(SKIP, t)" arbitrary: c1 c2 s t rule: star.induct)
     (auto, metis (no_types, lifting) SeqSE prod.inject star.refl star.step)

definition wt_suffix :: "com \<Rightarrow> com \<Rightarrow> bool" where
  "wt_suffix body c \<equiv>
     c = WHILE (Bc True) DO body
   \<or> c = IF (Bc True) THEN body ;; WHILE (Bc True) DO body ELSE SKIP
   \<or> (\<exists> c'. c = c' ;; WHILE (Bc True) DO body)"

lemma wt_suffix_step:
  "wt_suffix body c \<Longrightarrow> (c, s) \<rightarrow> (c', s') \<Longrightarrow> wt_suffix body c'"
  unfolding wt_suffix_def
  by auto

lemma wt_suffix_steps:
  "(c, s) \<rightarrow>* (c', t) \<Longrightarrow> wt_suffix body c \<Longrightarrow> wt_suffix body c'"
  by (induction "(c,s)" "(c',t)" arbitrary: c s rule: star.induct)
     (auto intro: wt_suffix_step)

lemma while_true_skip_no_finish:
  "\<not> ((WHILE (Bc True) DO a, s) \<rightarrow>* (SKIP, t))"
  by (meson com.distinct(3,5,7) wt_suffix_def wt_suffix_steps)
 

corollary while_true_incr_star_not_skip:
  "\<not> (WHILE (Bc True) DO (''x'' ::= Plus (V ''x'') (N 1)), s) \<rightarrow>* (SKIP, t)"
  using while_true_skip_no_finish by blast

corollary while_true_incr_no_finish:
  "\<not> ((WHILE (Bc True) DO (''x'' ::= Plus (V ''x'') (N 1)), s) \<rightarrow>* (SKIP, t))"
  using while_true_incr_star_not_skip by auto


subsection \<open>Small-step star inversions by command shape\<close>

text \<open>
  Inversion principles for the small-step reflexive-transitive closure,
  grouped by the shape of the source command.  Used by the
  \<open>small_step \<rightarrow> runs_to\<close> reverse bridge.
\<close>

lemma star_SKIP_eq:
  "(SKIP, s) \<rightarrow>* (SKIP, t) \<Longrightarrow> s = t"
  by (induction "(SKIP, s)" "(SKIP, t)" rule: star.induct) auto

lemma star_Assign_eq:
  "(x ::= a, s) \<rightarrow>* (SKIP, t) \<Longrightarrow> t = s(x := aval a s)"
  apply (induction "(x ::= a, s)" "(SKIP, t)" rule: star.induct)
  using star_SKIP_eq by blast

lemma star_If_split:
  "(IF b THEN c1 ELSE c2, s) \<rightarrow>* (SKIP, t) \<Longrightarrow>
   (bval b s \<and> (c1, s) \<rightarrow>* (SKIP, t)) \<or> (\<not> bval b s \<and> (c2, s) \<rightarrow>* (SKIP, t))"
  by (induction "(IF b THEN c1 ELSE c2, s)" "(SKIP, t)" rule: star.induct) auto

lemma star_While_split:
  "(WHILE b DO c, s) \<rightarrow>* (SKIP, t) \<Longrightarrow>
   (\<not> bval b s \<and> s = t) \<or>
   (\<exists>s'. bval b s \<and> (c, s) \<rightarrow>* (SKIP, s') \<and> (WHILE b DO c, s') \<rightarrow>* (SKIP, t))"
  by (induction "(WHILE b DO c, s)" "(SKIP, t)" rule: star.induct)
     (auto, metis WhileSE star_If_split star_SKIP_eq,
      metis WhileSE seq_star_finish star_If_split,
      metis WhileSE seq_star_finish star_If_split star_SKIP_eq)
 

end
