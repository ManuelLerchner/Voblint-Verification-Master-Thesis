theory Typed_Semantics
  imports Typed_Com
begin

section \<open>Typed source semantics\<close>

text \<open>
  A typed program runs on typed stores, which hold one value per variable identity. Every
  written value has the kind of the identity it is written to: elaboration already
  converts an assigned value, an actual argument and a returned value, and the semantics
  converts the two values it writes itself, a call result and a library result, to the
  destination's kind. This theory fixes the globals, the result write, the library
  results and the initial stores of that semantics.
\<close>

text \<open>The globals are the \<^const>\<open>GlobalId\<close> identities. A call keeps them and resets
  every other identity, the shared return slot included, as \<^const>\<open>enter_state\<close>
  keeps the declared globals.\<close>

fun tglobal :: "var_id \<Rightarrow> bool" where
  "tglobal (GlobalId _) = True"
| "tglobal _ = False"

text \<open>Writing a call or library result converts it to the destination's kind.\<close>

fun tcombine_assign :: "kenv \<Rightarrow> var_id option \<Rightarrow> int \<Rightarrow> tstore \<Rightarrow> tstore" where
  "tcombine_assign \<kappa> None _ t = t"
| "tcombine_assign \<kappa> (Some v) n t = t(v := ik_norm (\<kappa> v) n)"

text \<open>A library call yields what \<^const>\<open>special_result\<close> allows, with its arguments
  evaluated by the typed evaluator.\<close>

fun tspecial :: "special_desc \<Rightarrow> texp list \<Rightarrow> tstore \<Rightarrow> int \<Rightarrow> bool" where
  "tspecial SD_Nondet_Int [] t n \<longleftrightarrow> True"
| "tspecial SD_Min [a, b] t n \<longleftrightarrow> n = min (teval a t) (teval b t)"
| "tspecial SD_Max [a, b] t n \<longleftrightarrow> n = max (teval a t) (teval b t)"
| "tspecial _ _ _ _ \<longleftrightarrow> False"

text \<open>A typed program starts with its globals at zero, like \<^const>\<open>cinit_stores\<close>, and
  every other identity holding some value of its kind.\<close>

definition tinit_stores :: "kenv \<Rightarrow> tstore set" where
  "tinit_stores \<kappa> = {t. styped \<kappa> t \<and> (\<forall>x. t (GlobalId x) = 0)}"

end
