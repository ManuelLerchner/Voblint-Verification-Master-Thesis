theory VIMP_Globals
  imports VIMP_Syntax
begin

section \<open>Locals and globals over the scalar store\<close>

text \<open>
  The store is one \<open>vname \<Rightarrow> int\<close> function; the locals/globals split is a
  classifier \<open>gs :: vname \<Rightarrow> bool\<close> on top of it. A call needs both halves of
  that split: \<open>enter_state\<close> keeps the globals and resets the locals on entry,
  \<open>combine_env caller callee\<close> restores the caller's locals and keeps the
  callee's globals on exit.
\<close>

type_synonym pname = String.literal

definition combine_env :: "(vname \<Rightarrow> bool) \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store" where
  "combine_env gs s t = (\<lambda>n. if gs n then t n else s n)"

definition enter_state :: "(vname \<Rightarrow> bool) \<Rightarrow> store \<Rightarrow> store" where
  "enter_state gs s = (\<lambda>n. if gs n then s n else 0)"

lemma combine_query [simp]:
  "combine_env gs s t n = (if gs n then t n else s n)"
  unfolding combine_env_def by simp

lemma enter_state_apply [simp]:
  "enter_state gs s n = (if gs n then s n else 0)"
  unfolding enter_state_def by simp

lemma combine_collapse [simp]:
  "combine_env gs s s = s"
  by (rule ext) simp

lemma combine_nest_left [simp]:
  "combine_env gs (combine_env gs s t) u = combine_env gs s u"
  by (rule ext) simp

lemma combine_nest_right [simp]:
  "combine_env gs s (combine_env gs t u) = combine_env gs s u"
  by (rule ext) simp

end

