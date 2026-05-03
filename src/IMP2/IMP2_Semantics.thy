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

fun aval :: "aexp => state => int" where
    "aval (N n)       _  = n"
  | "aval (V x)       s  = s x"
  | "aval (Plus  a b) s  = aval a s + aval b s"
  | "aval (Minus a b) s  = aval a s - aval b s"
  | "aval (Times a b) s  = aval a s * aval b s"

fun bval :: "bexp => state => bool" where
    "bval (Bc v)      _  = v"
  | "bval (Not b)     s  = (~ bval b s)"
  | "bval (And b1 b2) s  = (bval b1 s & bval b2 s)"
  | "bval (Or  b1 b2) s  = (bval b1 s | bval b2 s)"
  | "bval (Less a b)  s  = (aval a s < aval b s)"
  | "bval (Eq   a b)  s  = (aval a s = aval b s)"

(* ── Big-Step Semantics (HOL-IMP style) ────────────────────────── *)

text \<open>Same rule structure as HOL-IMP.Big\_Step; first parameter is a pair.\<close>

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
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

(* ── Basic Properties ─────────────────────────────────────────── *)

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

lemma big_step_determ:
  "\<lbrakk> (c,s) \<Rightarrow> t1; (c,s) \<Rightarrow> t2 \<rbrakk> \<Longrightarrow> t1 = t2"
  by (induction arbitrary: t2 rule: big_step.induct) blast+

end
