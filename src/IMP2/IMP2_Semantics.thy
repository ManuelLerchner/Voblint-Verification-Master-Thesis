theory IMP2_Semantics
  imports IMP2_Syntax
begin

(*
  IMP2 -- Operational Semantics.

  Expression evaluation and big-step semantics for commands.
  Concrete syntax \<open>(c,s) \<Rightarrow> t\<close> follows HOL-IMP.Big_Step (same command
  constructors; IMP2 only extends aexp/bexp).
*)

(* ── Expression Evaluation ────────────────────────────────────── *)

fun aval :: "aexp => store => int" where
    "aval (N n)       _  = n"
  | "aval (V x)       s  = s x"
  | "aval (Plus  a b) s  = aval a s + aval b s"
  | "aval (Minus a b) s  = aval a s - aval b s"
  | "aval (Times a b) s  = aval a s * aval b s"

fun bval :: "bexp => store => bool" where
    "bval (Bc v)      _  = v"
  |     "bval (Not b)     s  = (\<not> bval b s)"
    | "bval (And b1 b2) s  = (bval b1 s \<and> bval b2 s)"
  | "bval (Or  b1 b2) s  = (bval b1 s | bval b2 s)"
  | "bval (Less a b)  s  = (aval a s < aval b s)"
  | "bval (Eq   a b)  s  = (aval a s = aval b s)"

(* ── Big-Step Semantics (HOL-IMP style) ────────────────────────── *)

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

text \<open>Split tuple in the induction schema (HOL-IMP \<open>big_step_induct\<close>).\<close>

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

text \<open>Alias for older proofs that referenced \<open>big_step_SeqE\<close>.\<close>

lemmas big_step_SeqE = SeqE

text \<open>Executable big-step via the predicate compiler (HOL-IMP.Big\_Step).\<close>

code_pred big_step .

subsection \<open>Simplification and structural lemmas\<close>

lemma skip_simp: "(SKIP,s) \<Rightarrow> t \<longleftrightarrow> t = s"
  by auto

lemma assign_simp: "(x ::= a,s) \<Rightarrow> s' \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

lemma Seq_assoc:
  "(c1 ;; c2 ;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1 ;; (c2 ;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1 ;; c2 ;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
      c1: "(c1, s) \<Rightarrow> s1" and
      c2: "(c2, s1) \<Rightarrow> s2" and
      c3: "(c3, s2) \<Rightarrow> s'" by auto
  from c2 c3 have "(c2 ;; c3, s1) \<Rightarrow> s'" by (rule Seq)
  with c1 show "(c1 ;; (c2 ;; c3), s) \<Rightarrow> s'" by (rule Seq)
next
  assume "(c1 ;; (c2 ;; c3), s) \<Rightarrow> s'"
  thus "(c1 ;; c2 ;; c3, s) \<Rightarrow> s'" by auto
qed


subsection \<open>Command equivalence\<close>

text \<open>
  Commands \<open>c\<close> and \<open>c'\<close> are equivalent when, from any start store \<open>s\<close>,
  they have the same terminating outcomes \<open>t\<close> (HOL-IMP.Big\_Step).
\<close>

abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t = (c',s) \<Rightarrow> t)"

text \<open>Notation: \<open>\<sim>\<close> is Isabelle's command-similarity symbol (ASCII \<^verbatim>\<open>\sim\<close>).\<close>

lemma unfold_while:
  "(WHILE b DO c) \<sim> (IF b THEN c ;; WHILE b DO c ELSE SKIP)" (is "?w \<sim> ?iw")
proof -
  have "(?iw, s) \<Rightarrow> t" if assm: "(?w, s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases
      case WhileFalse
      thus ?thesis by blast
    next
      case WhileTrue
      from \<open>bval b s\<close> \<open>(?w, s) \<Rightarrow> t\<close> obtain s' where
          "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      hence "(c ;; ?w, s) \<Rightarrow> t" by (rule Seq)
      with \<open>bval b s\<close> show ?thesis by (rule IfTrue)
    qed
  qed
  moreover
  have "(?w, s) \<Rightarrow> t" if assm: "(?iw, s) \<Rightarrow> t" for s t
  proof -
    from assm show ?thesis
    proof cases
      case IfFalse
      hence "s = t" by blast
      thus ?thesis using \<open>\<not> bval b s\<close> by blast
    next
      case IfTrue
      from \<open>(c ;; ?w, s) \<Rightarrow> t\<close> obtain s' where
          "(c, s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by auto
      with \<open>bval b s\<close> show ?thesis by (rule WhileTrue)
    qed
  qed
  ultimately
  show ?thesis by blast
qed

lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c ;; WHILE b DO c ELSE SKIP)"
  by blast

lemma triv_if: "(IF b THEN c ELSE c) \<sim> c"
  by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2)
   \<sim>
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
  by blast

lemma sim_while_cong_aux:
  "\<lbrakk> (WHILE b DO c, s) \<Rightarrow> t; c \<sim> c' \<rbrakk> \<Longrightarrow> (WHILE b DO c', s) \<Rightarrow> t"
  apply (induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct)
   apply blast
  apply blast
  done

lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
  by (metis sim_while_cong_aux)

lemma sim_refl: "c \<sim> c"
  by simp

lemma sim_sym: "(c \<sim> c') = (c' \<sim> c)"
  by auto

lemma sim_trans: "\<lbrakk> c \<sim> c'; c' \<sim> c'' \<rbrakk> \<Longrightarrow> c \<sim> c''"
  by auto


subsection \<open>Execution is deterministic\<close>

lemma big_step_If_iff:
  "(IF b THEN c1 ELSE c2, s) \<Rightarrow> u \<longleftrightarrow>
   (bval b s \<and> (c1,s) \<Rightarrow> u) \<or> (\<not> bval b s \<and> (c2,s) \<Rightarrow> u)"
proof (intro iffI)
  assume H: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> u"
  show "(bval b s \<and> (c1,s) \<Rightarrow> u) \<or> (\<not> bval b s \<and> (c2,s) \<Rightarrow> u)"
    using H by (cases rule: big_step.cases) auto
next
  assume "(bval b s \<and> (c1,s) \<Rightarrow> u) \<or> (\<not> bval b s \<and> (c2,s) \<Rightarrow> u)"
  then show "(IF b THEN c1 ELSE c2, s) \<Rightarrow> u"
    by (auto intro: IfTrue IfFalse)
qed

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t1; (c,s) \<Rightarrow> t2 \<rbrakk> \<Longrightarrow> t1 = t2"
  by (induction arbitrary: t2 rule: big_step.induct) blast+

end
