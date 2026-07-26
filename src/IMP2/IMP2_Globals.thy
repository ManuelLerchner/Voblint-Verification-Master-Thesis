theory IMP2_Globals
  imports IMP2_Syntax
begin

(*
  Locals/globals split over the scalar store = vname => int.

  A variable is global iff its name starts with 'G'; combine_states <s|t>
  takes locals from s and globals from t.  This is the splitting used by local
  scopes and procedure calls: on entry the caller's store is saved, on exit the
  callee's globals are kept and the caller's locals restored.

  Self-contained: depends only on store, not on com / small-step / CFG.
*)

(* Procedure names. *)
type_synonym pname = string

text \<open>A variable is global exactly when its name is empty or starts with
  @{text G}. Treating the empty name as global makes the predicate total and keeps store
  entry and combination aligned.\<close>
definition is_global :: "vname => bool" where
  "is_global x = (x = [] \<or> hd x = CHR ''G'')"

(* <s|t>: take locals from s, globals from t. *)
definition combine_states :: "store => store => store"  ("<_|_>" [0, 0] 1000) where
  "combine_states s t = (\<lambda>n. if is_global n then t n else s n)"

lemma combine_query [simp]:
  "<s|t> n = (if is_global n then t n else s n)"
  unfolding combine_states_def by simp

(* Concrete call/scope entry: globals from s, locals reset to 0. *)
definition enter_state :: "store \<Rightarrow> store" where
  "enter_state s = (\<lambda>n. if is_global n then s n else 0)"

(* Combining a store with itself is a no-op. *)
lemma combine_collapse [simp]:
  "<s|s> = s"
  by (rule ext) simp

(* Nested combines on the left/right collapse: only the outer locals and the
   innermost globals survive. *)
lemma combine_nest_left [simp]:
  "<<s|t>|u> = <s|u>"
  by (rule ext) simp

lemma combine_nest_right [simp]:
  "<s|<t|u>> = <s|u>"
  by (rule ext) simp

(* Updating a local variable commutes through the locals slot. *)
lemma combine_upd_local:
  "\<not> is_global x \<Longrightarrow> (<s|t>)(x := v) = <s(x := v)|t>"
  by (rule ext) auto

(* Updating a global variable commutes through the globals slot. *)
lemma combine_upd_global:
  "is_global x \<Longrightarrow> (<s|t>)(x := v) = <s|t(x := v)>"
  by (rule ext) auto

(* Case split on the locals/globals provenance of a variable. *)
lemma combine_cases:
  obtains (Local) "\<not> is_global n" "<s|t> n = s n"
        | (Global) "is_global n" "<s|t> n = t n"
  by (cases "is_global n") auto

subsection \<open>Executable examples\<close>

value "is_global ''Gx''"
value "is_global ''x''"
value "is_global []"

value "<(\<lambda>_. 0::int)(''x'' := 1, ''Gx'' := 2) | (\<lambda>_. 0::int)(''x'' := 9, ''Gx'' := 5)> ''x''"
value "<(\<lambda>_. 0::int)(''x'' := 1, ''Gx'' := 2) | (\<lambda>_. 0::int)(''x'' := 9, ''Gx'' := 5)> ''Gx''"

value "enter_state ((\<lambda>_. 0::int)(''x'' := 7, ''Gx'' := 3)) ''x''"
value "enter_state ((\<lambda>_. 0::int)(''x'' := 7, ''Gx'' := 3)) ''Gx''"

end
