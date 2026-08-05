theory VIMP_Globals
  imports VIMP_Syntax
begin

section \<open>Locals and globals over the scalar store\<close>

text \<open>
  The store is a single \<open>vname => int\<close> function; the locals/globals split is a
  naming convention on top of it, not a separate representation.
  \<open>is_global\<close> names the split; \<open>combine_states\<close> \<open><s|t>\<close> takes locals from \<open>s\<close>
  and globals from \<open>t\<close>. This is the splitting a procedure call needs on both
  ends: on entry the caller's store is saved and locals reset (\<open>enter_state\<close>),
  on exit the callee's globals are kept and the caller's locals restored
  (\<open><caller|callee>\<close>).

  Self-contained: depends only on the store, not on \<open>com\<close>, small-step, or the
  CFG.
\<close>

(* Procedure names. *)
type_synonym pname = string

text \<open>A variable is global exactly when its name is empty or starts with
  @{text G}. Treating the empty name as global makes the predicate total and keeps store
  entry and combination aligned.\<close>
definition is_global :: "vname => bool" where
  "is_global x = (x = [] \<or> hd x = CHR ''G'')"

text \<open>
  \<open>combine_states gs s t\<close>: take locals from \<open>s\<close>, globals from \<open>t\<close>, where
  \<open>gs\<close> decides the split. This is the store a procedure call reconstructs on
  return, so the caller's locals survive the call unless the callee wrote
  through a global. \<open>gs\<close> is an explicit classifier rather than a fixed
  constant so a caller can supply \<^const>\<open>is_global\<close> or a declaration-driven
  classifier, whichever a given layer needs; no mixfix notation, since a
  genuinely three-argument operation is not a binary one.
\<close>
definition combine_states :: "(vname \<Rightarrow> bool) \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store" where
  "combine_states gs s t = (\<lambda>n. if gs n then t n else s n)"

lemma combine_query [simp]:
  "combine_states gs s t n = (if gs n then t n else s n)"
  unfolding combine_states_def by simp

text \<open>Concrete call/scope entry: globals persist from \<open>s\<close>, locals reset to
  \<open>0\<close> -- the store a callee starts execution in.\<close>
definition enter_state :: "(vname \<Rightarrow> bool) \<Rightarrow> store \<Rightarrow> store" where
  "enter_state gs s = (\<lambda>n. if gs n then s n else 0)"

(* Combining a store with itself is a no-op, for any classifier. *)
lemma combine_collapse [simp]:
  "combine_states gs s s = s"
  by (rule ext) simp

(* Nested combines on the left/right collapse: only the outer locals and the
   innermost globals survive, for any (single, shared) classifier. *)
lemma combine_nest_left [simp]:
  "combine_states gs (combine_states gs s t) u = combine_states gs s u"
  by (rule ext) simp

lemma combine_nest_right [simp]:
  "combine_states gs s (combine_states gs t u) = combine_states gs s u"
  by (rule ext) simp

subsection \<open>Executable examples\<close>

value "is_global ''Gx''"
value "is_global ''x''"
value "is_global []"

value "combine_states is_global
         ((\<lambda>_. 0::int)(''x'' := 1, ''Gx'' := 2)) ((\<lambda>_. 0::int)(''x'' := 9, ''Gx'' := 5)) ''x''"
value "combine_states is_global
         ((\<lambda>_. 0::int)(''x'' := 1, ''Gx'' := 2)) ((\<lambda>_. 0::int)(''x'' := 9, ''Gx'' := 5)) ''Gx''"

value "enter_state is_global ((\<lambda>_. 0::int)(''x'' := 7, ''Gx'' := 3)) ''x''"
value "enter_state is_global ((\<lambda>_. 0::int)(''x'' := 7, ''Gx'' := 3)) ''Gx''"

end
