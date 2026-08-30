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

  \<open>combine_env\<close> and \<open>enter_frame\<close> are pure per-variable selectors, generic in the
  codomain: the concrete VIMP semantics uses each at \<open>store = vname \<Rightarrow> int\<close>
  (\<open>enter_frame\<close> fixed at reset value \<open>0\<close>, i.e. \<open>enter_state\<close>), and every abstract
  domain's own \<open>vname \<Rightarrow> 'a\<close> state reuses the same two definitions -- at its own
  reset/join value -- rather than restating an \<open>_abs\<close> copy of either.
\<close>

type_synonym pname = String.literal

definition combine_env :: "(vname \<Rightarrow> bool) \<Rightarrow> (vname \<Rightarrow> 'a) \<Rightarrow> (vname \<Rightarrow> 'a) \<Rightarrow> (vname \<Rightarrow> 'a)" where
  "combine_env gs s t = (\<lambda>n. if gs n then t n else s n)"

definition enter_frame :: "(vname \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> (vname \<Rightarrow> 'a) \<Rightarrow> (vname \<Rightarrow> 'a)" where
  "enter_frame gs reset_val s = (\<lambda>n. if gs n then s n else reset_val)"

definition enter_state :: "(vname \<Rightarrow> bool) \<Rightarrow> store \<Rightarrow> store" where
  "enter_state gs s = enter_frame gs 0 s"

lemma combine_query [simp]:
  "combine_env gs s t n = (if gs n then t n else s n)"
  unfolding combine_env_def by simp

lemma enter_frame_apply [simp]:
  "enter_frame gs reset_val s n = (if gs n then s n else reset_val)"
  unfolding enter_frame_def by simp

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

section \<open>C-faithful initial store set\<close>

text \<open>
  VIMP approximates C startup by initializing every global with no explicit
  initializer to 0 and treating every local integer slot as unconstrained.
  \<open>cinit_stores\<close> is the corresponding set of concrete stores: those where every
  global is 0 and locals are unconstrained. This matches VIMP's total-store
  semantics, where every declared variable already has some value on entry; it
  is not a model of C's indeterminate-value or undefined-behaviour rules, and
  VIMP has no global initializer syntax for a declaration such as \<open>int x = 42;\<close>
  to diverge from.
\<close>

definition cinit_stores :: "(vname \<Rightarrow> bool) \<Rightarrow> store set" where
  "cinit_stores gs = {s. \<forall>x. gs x \<longrightarrow> s x = 0}"

end

