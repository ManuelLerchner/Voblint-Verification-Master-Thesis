theory Var_Id
  imports VIMP_Proc
begin

section \<open>Static variable identities\<close>

text \<open>
  A name is not an identity: two procedures may both call a formal \<open>n\<close>, and the two
  are different variables that may carry different kinds. A \<open>var_id\<close> names the scope
  a binding belongs to, in the role of CIL's \<open>varinfo\<close>. \<open>ReturnId\<close> is the
  return slot of one procedure. It is a constructor rather than a spelling, so no
  source program can name it, and each procedure's slot can carry its own kind.
\<close>

datatype var_id =
    GlobalId vname
  | ScopedId pname vname
  | ReturnId pname
  | ReturnVar

derive linorder var_id

text \<open>\<open>ReturnVar\<close> is the one slot a return writes and a call result is read from,
  Goblint's \<^verbatim>\<open>return_varinfo\<close>: activation-local, belonging to no single procedure.
  \<open>ReturnId p\<close> names the kind procedure \<open>p\<close> returns, which elaboration converts a
  returned value to.\<close>

fun var_scope :: "var_id \<Rightarrow> pname option" where
  "var_scope (GlobalId _) = None"
| "var_scope (ScopedId q _) = Some q"
| "var_scope (ReturnId q) = Some q"
| "var_scope ReturnVar = None"

text \<open>The source name of an identity, which a report shows and erasure restores.
  The return slot keeps the reserved source name \<^const>\<open>ret_var\<close>.\<close>

fun var_name :: "var_id \<Rightarrow> vname" where
  "var_name (GlobalId x) = x"
| "var_name (ScopedId _ x) = x"
| "var_name (ReturnId _) = ret_var"
| "var_name ReturnVar = ret_var"

subsection \<open>Resolution\<close>

text \<open>
  VIMP has no block scopes and no shadowing: a name the program declares global is
  that global in every procedure, and every other name is local to the procedure
  that mentions it (@{const enter_state} resets exactly those at a call). Resolution
  reads that rule off the globals classifier \<open>\<G>\<close>.
\<close>

definition resolve_var :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> vname \<Rightarrow> var_id" where
  "resolve_var \<G> q x = (if \<G> x then GlobalId x else ScopedId q x)"

lemma var_name_resolve_var [simp]: "var_name (resolve_var \<G> q x) = x"
  by (simp add: resolve_var_def)

lemma var_scope_resolve_var [simp]:
  "var_scope (resolve_var \<G> q x) = (if \<G> x then None else Some q)"
  by (simp add: resolve_var_def)

lemma resolve_var_not_ReturnId [simp]: "resolve_var \<G> q x \<noteq> ReturnId r"
  by (simp add: resolve_var_def)

lemma resolve_var_not_ReturnVar [simp]: "resolve_var \<G> q x \<noteq> ReturnVar"
  by (simp add: resolve_var_def)

text \<open>Resolution is unique: within one procedure distinct names get distinct
  identities, and two procedures share an identity only for a global.\<close>

theorem resolve_var_eq_iff:
  "resolve_var \<G> q x = resolve_var \<G> r y \<longleftrightarrow> x = y \<and> (\<G> x \<or> q = r)"
  by (auto simp: resolve_var_def)

subsection \<open>Kinds and typed stores\<close>

text \<open>
  A kind environment answers a kind for every identity. VIMP's grammar declares no
  kinds yet, so an environment is an input to elaboration; \<open>int_kenv\<close> is the one a
  program without declarations means, every variable a C \<open>int\<close>.
\<close>

type_synonym kenv = "var_id \<Rightarrow> ikind"
type_synonym tstore = "var_id \<Rightarrow> int"

definition int_kenv :: kenv where
  "int_kenv = (\<lambda>_. I32)"

text \<open>A store is typed when every identity holds a value of its kind.\<close>

definition styped :: "kenv \<Rightarrow> tstore \<Rightarrow> bool" where
  "styped \<kappa> t \<longleftrightarrow> (\<forall>v. t v \<in> ik_range (\<kappa> v))"

lemma stypedD: "styped \<kappa> t \<Longrightarrow> t v \<in> ik_range (\<kappa> v)"
  by (simp add: styped_def)

lemma styped_zero [simp, intro]: "styped \<kappa> (\<lambda>_. 0)"
  by (simp add: styped_def del: ik_range_iff)

lemma styped_update [simp, intro]: "styped \<kappa> t \<Longrightarrow> styped \<kappa> (t(v := ik_norm (\<kappa> v) n))"
  by (simp add: styped_def del: ik_range_iff)

end
