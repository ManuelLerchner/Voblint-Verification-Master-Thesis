theory VIMP_Expr
  imports VIMP_Syntax
begin

section \<open>Expression evaluation\<close>

text \<open>\<open>truthy\<close> is C's condition test; comparisons and logical operators evaluate
  to \<open>1\<close>/\<open>0\<close> through it.\<close>

definition truthy :: "int \<Rightarrow> bool" where
  [simp]: "truthy n \<longleftrightarrow> n \<noteq> 0"

fun aval :: "exp \<Rightarrow> store \<Rightarrow> int" where
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

end

