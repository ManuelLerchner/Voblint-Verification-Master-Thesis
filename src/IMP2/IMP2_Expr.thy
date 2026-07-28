theory IMP2_Expr
  imports IMP2_Syntax IMP2_Globals "HOL-IMP.AExp" "HOL-IMP.BExp" "HOL-IMP.Star"
begin

section \<open>Expression evaluation\<close>

text \<open>The extended evaluators delegate wrapped base expressions to the imported
  arithmetic and Boolean evaluators. This theory also re-exports the reflexive-transitive
  closure used by the procedure small-step relation.\<close>

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

subsection \<open>Syntactic variable occurrence, parameterised over the predicate\<close>

text \<open>
  Both "does this expression mention a global?" and "does this expression
  mention variable x?" are the same syntax-directed walk, differing only in
  the leaf predicate on the mentioned name. Defining the walk once as
  @{text "_where P"} and instantiating @{text P} to @{const is_global} (below)
  or to an equality test (\<open>IMP2_Proc.aexp_mentions\<close>) avoids two copies of the
  same recursion.
\<close>

fun aexp_n_mentions_where :: "(vname \<Rightarrow> bool) \<Rightarrow> AExp.aexp \<Rightarrow> bool" where
  "aexp_n_mentions_where P (aexp.N _) = False"
| "aexp_n_mentions_where P (aexp.V x) = P x"
| "aexp_n_mentions_where P (AExp.aexp.Plus a b) = (aexp_n_mentions_where P a \<or> aexp_n_mentions_where P b)"

fun aexp_mentions_where :: "(vname \<Rightarrow> bool) \<Rightarrow> aexp \<Rightarrow> bool" where
  "aexp_mentions_where P (BaseN a) = aexp_n_mentions_where P a"
| "aexp_mentions_where P (Plus a b) = (aexp_mentions_where P a \<or> aexp_mentions_where P b)"
| "aexp_mentions_where P (Minus a b) = (aexp_mentions_where P a \<or> aexp_mentions_where P b)"
| "aexp_mentions_where P (Times a b) = (aexp_mentions_where P a \<or> aexp_mentions_where P b)"

fun bexp_n_mentions_where :: "(vname \<Rightarrow> bool) \<Rightarrow> BExp.bexp \<Rightarrow> bool" where
  "bexp_n_mentions_where P (bexp.Bc _) = False"
| "bexp_n_mentions_where P (BExp.bexp.Not b) = bexp_n_mentions_where P b"
| "bexp_n_mentions_where P (BExp.bexp.And b1 b2) = (bexp_n_mentions_where P b1 \<or> bexp_n_mentions_where P b2)"
| "bexp_n_mentions_where P (BExp.bexp.Less a b) = (aexp_n_mentions_where P a \<or> aexp_n_mentions_where P b)"

fun bexp_mentions_where :: "(vname \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> bool" where
  "bexp_mentions_where P (BaseB b) = bexp_n_mentions_where P b"
| "bexp_mentions_where P (Not b) = bexp_mentions_where P b"
| "bexp_mentions_where P (And b1 b2) = (bexp_mentions_where P b1 \<or> bexp_mentions_where P b2)"
| "bexp_mentions_where P (Or b1 b2) = (bexp_mentions_where P b1 \<or> bexp_mentions_where P b2)"
| "bexp_mentions_where P (Less a b) = (aexp_mentions_where P a \<or> aexp_mentions_where P b)"
| "bexp_mentions_where P (Eq a b) = (aexp_mentions_where P a \<or> aexp_mentions_where P b)"

subsection \<open>Syntactic global-variable occurrence\<close>

definition aexp_n_mentions_global :: "AExp.aexp \<Rightarrow> bool" where
  "aexp_n_mentions_global = aexp_n_mentions_where is_global"

definition aexp_mentions_global :: "aexp \<Rightarrow> bool" where
  "aexp_mentions_global = aexp_mentions_where is_global"

definition bexp_n_mentions_global :: "BExp.bexp \<Rightarrow> bool" where
  "bexp_n_mentions_global = bexp_n_mentions_where is_global"

definition bexp_mentions_global :: "bexp \<Rightarrow> bool" where
  "bexp_mentions_global = bexp_mentions_where is_global"

lemmas mentions_global_defs [simp] =
  aexp_n_mentions_global_def aexp_mentions_global_def
  bexp_n_mentions_global_def bexp_mentions_global_def

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
  apply (induction a)
  using aexp_n_aval_eq_on_locals
  by fastforce+

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
  then have "AExp.aval a s1 = AExp.aval a s2"
    and "AExp.aval b s1 = AExp.aval b s2"
    using aexp_n_aval_eq_on_locals unfolding mentions_global_defs
    by fastforce +
  then show ?case
    by simp
qed

lemma bval_eq_on_locals:
  assumes "\<not> bexp_mentions_global b"
    and "\<And>x. \<not> is_global x \<Longrightarrow> s1 x = s2 x"
  shows "bval b s1 = bval b s2"
  using assms
proof (induction b)
  case (BaseB a)
  then show ?case apply(auto)
    using bexp_n_bval_eq_on_locals[unfolded mentions_global_defs] by blast +
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
  case (Less a b)
  then have "aval a s1 = aval a s2" and "aval b s1 = aval b s2"
    unfolding bexp_n_mentions_global_def apply(auto)
    using aexp_mentions_global_def aval_eq_on_locals by presburger +
  then show ?case
    by auto
next
  case (Eq a b)
  then have "aval a s1 = aval a s2" and "aval b s1 = aval b s2"
    unfolding bexp_n_mentions_global_def apply(auto)
    using aexp_mentions_global_def aval_eq_on_locals by presburger +
  then show ?case 
    by auto
qed




subsection \<open>Executable examples\<close>

value "aval (Plus (N 3) (N 4)) (\<lambda>_. 0::int)"
value "aval (V ''x'') ((\<lambda>_. 0::int)(''x'' := 42))"
value "aval (Times (Minus (V ''x'') (N 2)) (N 3)) ((\<lambda>_. 0::int)(''x'' := 5))"

value "bval (Less (V ''x'') (N 10)) ((\<lambda>_. 0::int)(''x'' := 7))"
value "bval (Eq (V ''x'') (N 5)) ((\<lambda>_. 0::int)(''x'' := 5))"
value "bval (Not (Bc True)) (\<lambda>_. 0::int)"

end


