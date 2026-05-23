theory IMP2_BigStep
  imports IMP2_Syntax
begin

(*
  IMP2 -- Big-Step Operational Semantics.

  Expression evaluation and big-step semantics for commands.
  Concrete syntax `(c,s) \<Rightarrow> t` follows HOL-IMP.Big_Step (same command
  constructors; IMP2 only extends aexp/bexp).
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

(* -- Big-Step Semantics (HOL-IMP style) ------------------------- *)

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

text \<open>Introduction rules: unsafe `intro` (backtracking on recursive rules).\<close>

declare big_step.intros [intro]

lemmas big_step_induct = big_step.induct[split_format(complete)]

subsection \<open>Rule inversion\<close>

text \<open>
  Elimination rules for `auto`/`blast`.  Eager `elim!` except for `WhileE`:
  `WhileE` is only `elim` because `elim!` would not terminate (HOL-IMP.Big\_Step).
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

end
