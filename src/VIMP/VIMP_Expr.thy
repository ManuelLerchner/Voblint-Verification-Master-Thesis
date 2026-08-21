theory VIMP_Expr
  imports VIMP_Syntax VIMP_Globals "HOL-IMP.Star"
begin

section \<open>Expression evaluation\<close>

text \<open>This theory also re-exports the reflexive-transitive closure used by the
  procedure small-step relation.\<close>

(* -- Expression Evaluation -------------------------------------- *)

text \<open>
  \<open>truthy\<close> is C's own condition test: an \<open>int\<close> is true exactly when it is
  nonzero.  \<open>aval\<close> gives every \<open>exp\<close> constructor -- arithmetic, comparison,
  and logical alike -- an \<open>int\<close> result: \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/\<open>And\<close>/\<open>Or\<close>
  evaluate to \<open>1\<close> or \<open>0\<close> via \<open>truthy\<close>, exactly as their C counterparts do.
\<close>

definition truthy :: "int \<Rightarrow> bool" where
  [simp]: "truthy n \<longleftrightarrow> n \<noteq> 0"

fun aval :: "exp => store => int" where
    "aval (N n)     s  = n"
  | "aval (V x)     s  = s x"
  | "aval (Plus  a b) s  = aval a s + aval b s"
  | "aval (Minus a b) s  = aval a s - aval b s"
  | "aval (Times a b) s  = aval a s * aval b s"
  | "aval (Less a b)  s  = (if aval a s < aval b s then 1 else 0)"
  | "aval (Eq   a b)  s  = (if aval a s = aval b s then 1 else 0)"
  | "aval (Not b)     s  = (if truthy (aval b s) then 0 else 1)"
  | "aval (And b1 b2) s  = (if truthy (aval b1 s) \<and> truthy (aval b2 s) then 1 else 0)"
  | "aval (Or  b1 b2) s  = (if truthy (aval b1 s) \<or> truthy (aval b2 s) then 1 else 0)"

subsection \<open>Syntactic variable occurrence, parameterised over the predicate\<close>

text \<open>
  Both "does this expression mention a global?" and "does this expression
  mention variable x?" are the same syntax-directed walk, differing only in
  the leaf predicate on the mentioned name. Defining the walk once as
  @{text "_where P"} and instantiating @{text P} to a global-variable
  classifier (below) or to an equality test (\<open>VIMP_Proc.exp_mentions\<close>)
  avoids two copies of the same recursion.
\<close>

fun exp_mentions_where :: "(vname \<Rightarrow> bool) \<Rightarrow> exp \<Rightarrow> bool" where
  "exp_mentions_where P (N _) = False"
| "exp_mentions_where P (V x) = P x"
| "exp_mentions_where P (Plus a b) = (exp_mentions_where P a \<or> exp_mentions_where P b)"
| "exp_mentions_where P (Minus a b) = (exp_mentions_where P a \<or> exp_mentions_where P b)"
| "exp_mentions_where P (Times a b) = (exp_mentions_where P a \<or> exp_mentions_where P b)"
| "exp_mentions_where P (Less a b) = (exp_mentions_where P a \<or> exp_mentions_where P b)"
| "exp_mentions_where P (Eq a b) = (exp_mentions_where P a \<or> exp_mentions_where P b)"
| "exp_mentions_where P (Not b) = exp_mentions_where P b"
| "exp_mentions_where P (And b1 b2) = (exp_mentions_where P b1 \<or> exp_mentions_where P b2)"
| "exp_mentions_where P (Or b1 b2) = (exp_mentions_where P b1 \<or> exp_mentions_where P b2)"

subsection \<open>Syntactic global-variable occurrence\<close>

definition exp_mentions_global :: "(vname \<Rightarrow> bool) \<Rightarrow> exp \<Rightarrow> bool" where
  "exp_mentions_global gs = exp_mentions_where gs"

lemmas mentions_global_defs [simp] =
  exp_mentions_global_def

text \<open>
  @{const exp_mentions_global} classifies whether an expression may read a
  global variable.  Effectful edge trees use this to omit the unit-global
  @{term QueryG} when a transfer depends only on the local unknown.
\<close>

lemma aval_eq_on_locals:
  assumes "\<not> exp_mentions_global gs e"
    and "\<And>x. \<not> gs x \<Longrightarrow> s1 x = s2 x"
  shows "aval e s1 = aval e s2"
  using assms
  by (induction e) auto

subsection \<open>Executable examples\<close>

value "aval (Plus (N 3) (N 4)) (\<lambda>_. 0::int)"
value "aval (V (STR ''x'')) ((\<lambda>_. 0::int)((STR ''x'') := 42))"
value "aval (Times (Minus (V (STR ''x'')) (N 2)) (N 3)) ((\<lambda>_. 0::int)((STR ''x'') := 5))"

value "aval (Less (V (STR ''x'')) (N 10)) ((\<lambda>_. 0::int)((STR ''x'') := 7))"
value "aval (Eq (V (STR ''x'')) (N 5)) ((\<lambda>_. 0::int)((STR ''x'') := 5))"
value "aval (Not (N 1)) (\<lambda>_. 0::int)"
value "aval (Plus (N 3) (Less (V (STR ''x'')) (N 5))) ((\<lambda>_. 0::int)((STR ''x'') := 2))"

end

