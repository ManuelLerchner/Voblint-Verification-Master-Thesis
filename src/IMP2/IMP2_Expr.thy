theory IMP2_Expr
  imports IMP2_Syntax IMP2_Globals "HOL-IMP.AExp" "HOL-IMP.BExp" "HOL-IMP.Star"
begin

(*
  IMP2 -- expression evaluation.

  aval/bval evaluate the IMP2 expression extensions, delegating
  BaseN/BaseB to Nipkow's HOL-IMP AExp/BExp.

  The actual small-step relation `pstep` lives in IMP2_Proc.thy;
  this module is expression evaluation only.  `HOL-IMP.Star` is
  re-exported here so `pstep`'s `star` closure resolves downstream.
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

subsection \<open>Syntactic global-variable occurrence\<close>

fun aexp_n_mentions_global :: "AExp.aexp \<Rightarrow> bool" where
  "aexp_n_mentions_global (aexp.N _) = False"
| "aexp_n_mentions_global (aexp.V x) = is_global x"
| "aexp_n_mentions_global (AExp.aexp.Plus a b) = (aexp_n_mentions_global a \<or> aexp_n_mentions_global b)"

fun aexp_mentions_global :: "aexp \<Rightarrow> bool" where
  "aexp_mentions_global (BaseN a) = aexp_n_mentions_global a"
| "aexp_mentions_global (Plus a b) = (aexp_mentions_global a \<or> aexp_mentions_global b)"
| "aexp_mentions_global (Minus a b) = (aexp_mentions_global a \<or> aexp_mentions_global b)"
| "aexp_mentions_global (Times a b) = (aexp_mentions_global a \<or> aexp_mentions_global b)"

fun bexp_n_mentions_global :: "BExp.bexp \<Rightarrow> bool" where
  "bexp_n_mentions_global (bexp.Bc _) = False"
| "bexp_n_mentions_global (BExp.bexp.Not b) = bexp_n_mentions_global b"
| "bexp_n_mentions_global (BExp.bexp.And b1 b2) = (bexp_n_mentions_global b1 \<or> bexp_n_mentions_global b2)"
| "bexp_n_mentions_global (BExp.bexp.Less a b) = (aexp_n_mentions_global a \<or> aexp_n_mentions_global b)"

fun bexp_mentions_global :: "bexp \<Rightarrow> bool" where
  "bexp_mentions_global (BaseB b) = bexp_n_mentions_global b"
| "bexp_mentions_global (Not b) = bexp_mentions_global b"
| "bexp_mentions_global (And b1 b2) = (bexp_mentions_global b1 \<or> bexp_mentions_global b2)"
| "bexp_mentions_global (Or b1 b2) = (bexp_mentions_global b1 \<or> bexp_mentions_global b2)"
| "bexp_mentions_global (Less a b) = (aexp_mentions_global a \<or> aexp_mentions_global b)"
| "bexp_mentions_global (Eq a b) = (aexp_mentions_global a \<or> aexp_mentions_global b)"

text \<open>
  @{const aexp_mentions_global} / @{const bexp_mentions_global} classify whether an
  expression may read a global variable.  Effectful edge trees use this to omit the
  unit-global @{term QueryG} when a transfer depends only on the local unknown.
\<close>

lemma aexp_n_aval_eq_on_locals:
  assumes ng: "\<not> aexp_n_mentions_global a"
    and loc: "\<And>x. \<not> is_global x \<Longrightarrow> s1 x = s2 x"
  shows "AExp.aval a s1 = AExp.aval a s2"
  using ng loc
proof (induction a)
  case (V x)
  then show ?case by (cases "is_global x") auto
next
  case (Plus a b)
  then show ?case by auto
next
  case (N n)
  then show ?case by simp
qed

lemma aval_eq_on_locals:
  assumes "\<not> aexp_mentions_global a"
    and "\<And>x. \<not> is_global x \<Longrightarrow> s1 x = s2 x"
  shows "aval a s1 = aval a s2"
  using assms
proof (induction a)
  case (BaseN a)
  then show ?case  using aexp_n_aval_eq_on_locals by fastforce
next
  case (Plus a b)
  then show ?case by auto
next
  case (Minus a b)
  then show ?case by auto
next
  case (Times a b)
  then show ?case by auto
qed

lemma bexp_n_bval_eq_on_locals:
  assumes ng: "\<not> bexp_n_mentions_global b"
    and loc: "\<And>x. \<not> is_global x \<Longrightarrow> s1 x = s2 x"
  shows "BExp.bval b s1 = BExp.bval b s2"
  using ng loc
proof (induction b)
  case (Bc v)
  then show ?case by simp
next
  case (Not b)
  then show ?case by auto
next
  case (And b1 b2)
  then show ?case by auto
next
  case (Less a b)
  then show ?case  apply(auto)
    by (metis aexp_n_aval_eq_on_locals)+
   
qed

lemma bval_eq_on_locals:
  assumes "\<not> bexp_mentions_global b"
    and "\<And>x. \<not> is_global x \<Longrightarrow> s1 x = s2 x"
  shows "bval b s1 = bval b s2"
  using assms
proof (induction b)
  case (BaseB a)
  then show ?case apply(auto)
    using bexp_n_bval_eq_on_locals by blast +
next
  case (Not b)
  then show ?case by auto
next
  case (And b1 b2)
  then show ?case by auto
next
  case (Or b1 b2)
  then show ?case by auto
next
  case (Less a b')
  then show ?case apply(auto)
    by (metis aval_eq_on_locals)+
next
  case (Eq a b')
  then show ?case apply(auto)
    by (metis aval_eq_on_locals)+
qed





subsection \<open>Executable examples\<close>

value "aval (Plus (N 3) (N 4)) (\<lambda>_. 0::int)"
value "aval (V ''x'') ((\<lambda>_. 0::int)(''x'' := 42))"
value "aval (Times (Minus (V ''x'') (N 2)) (N 3)) ((\<lambda>_. 0::int)(''x'' := 5))"

value "bval (Less (V ''x'') (N 10)) ((\<lambda>_. 0::int)(''x'' := 7))"
value "bval (Eq (V ''x'') (N 5)) ((\<lambda>_. 0::int)(''x'' := 5))"
value "bval (Not (Bc True)) (\<lambda>_. 0::int)"

end


