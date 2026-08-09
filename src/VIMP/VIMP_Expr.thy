theory VIMP_Expr
  imports VIMP_Syntax VIMP_Globals "HOL-IMP.Star"
begin

section \<open>Expression evaluation\<close>

text \<open>This theory also re-exports the reflexive-transitive closure used by the
  procedure small-step relation.\<close>

(* -- Expression Evaluation -------------------------------------- *)

fun aval :: "aexp => store => int" where
    "aval (N n)     s  = n"
  | "aval (V x)     s  = s x"
  | "aval (Plus  a b) s  = aval a s + aval b s"
  | "aval (Minus a b) s  = aval a s - aval b s"
  | "aval (Times a b) s  = aval a s * aval b s"

fun bval :: "bexp => store => bool" where
    "bval (Bc v)      s  = v"
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
  @{text "_where P"} and instantiating @{text P} to a global-variable
  classifier (below) or to an equality test (\<open>VIMP_Proc.aexp_mentions\<close>)
  avoids two copies of the same recursion.
\<close>

fun aexp_mentions_where :: "(vname \<Rightarrow> bool) \<Rightarrow> aexp \<Rightarrow> bool" where
  "aexp_mentions_where P (N _) = False"
| "aexp_mentions_where P (V x) = P x"
| "aexp_mentions_where P (Plus a b) = (aexp_mentions_where P a \<or> aexp_mentions_where P b)"
| "aexp_mentions_where P (Minus a b) = (aexp_mentions_where P a \<or> aexp_mentions_where P b)"
| "aexp_mentions_where P (Times a b) = (aexp_mentions_where P a \<or> aexp_mentions_where P b)"

fun bexp_mentions_where :: "(vname \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> bool" where
  "bexp_mentions_where P (Bc _) = False"
| "bexp_mentions_where P (Not b) = bexp_mentions_where P b"
| "bexp_mentions_where P (And b1 b2) = (bexp_mentions_where P b1 \<or> bexp_mentions_where P b2)"
| "bexp_mentions_where P (Or b1 b2) = (bexp_mentions_where P b1 \<or> bexp_mentions_where P b2)"
| "bexp_mentions_where P (Less a b) = (aexp_mentions_where P a \<or> aexp_mentions_where P b)"
| "bexp_mentions_where P (Eq a b) = (aexp_mentions_where P a \<or> aexp_mentions_where P b)"

subsection \<open>Syntactic global-variable occurrence\<close>

definition aexp_mentions_global :: "(vname \<Rightarrow> bool) \<Rightarrow> aexp \<Rightarrow> bool" where
  "aexp_mentions_global gs = aexp_mentions_where gs"

definition bexp_mentions_global :: "(vname \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> bool" where
  "bexp_mentions_global gs = bexp_mentions_where gs"

lemmas mentions_global_defs [simp] =
  aexp_mentions_global_def bexp_mentions_global_def

text \<open>
  @{const aexp_mentions_global} / @{const bexp_mentions_global} classify whether an
  expression may read a global variable.  Effectful edge trees use this to omit the
  unit-global @{term QueryG} when a transfer depends only on the local unknown.
\<close>

lemma aval_eq_on_locals:
  assumes "\<not> aexp_mentions_global gs a"
    and "\<And>x. \<not> gs x \<Longrightarrow> s1 x = s2 x"
  shows "aval a s1 = aval a s2"
  using assms
  by (induction a) auto

lemma bval_eq_on_locals:
  assumes "\<not> bexp_mentions_global gs b"
    and "\<And>x. \<not> gs x \<Longrightarrow> s1 x = s2 x"
  shows "bval b s1 = bval b s2"
  using assms
proof (induction b)
  case (Bc v)
  then show ?case by simp
next
  case (Not b)
  then show ?case by simp
next
  case (And b1 b2)
  then show ?case by simp
next
  case (Or b1 b2)
  then show ?case by simp
next
  case (Less a b)
  then have "aval a s1 = aval a s2" and "aval b s1 = aval b s2"
    unfolding bexp_mentions_global_def apply(auto)
    using aexp_mentions_global_def aval_eq_on_locals by presburger +
  then show ?case
    by auto
next
  case (Eq a b)
  then have "aval a s1 = aval a s2" and "aval b s1 = aval b s2"
    unfolding bexp_mentions_global_def apply(auto)
    using aexp_mentions_global_def aval_eq_on_locals by presburger +
  then show ?case 
    by auto
qed




subsection \<open>Executable examples\<close>

value "aval (Plus (N 3) (N 4)) (\<lambda>_. 0::int)"
value "aval (V (STR ''x'')) ((\<lambda>_. 0::int)((STR ''x'') := 42))"
value "aval (Times (Minus (V (STR ''x'')) (N 2)) (N 3)) ((\<lambda>_. 0::int)((STR ''x'') := 5))"

value "bval (Less (V (STR ''x'')) (N 10)) ((\<lambda>_. 0::int)((STR ''x'') := 7))"
value "bval (Eq (V (STR ''x'')) (N 5)) ((\<lambda>_. 0::int)((STR ''x'') := 5))"
value "bval (Not (Bc True)) (\<lambda>_. 0::int)"

end

