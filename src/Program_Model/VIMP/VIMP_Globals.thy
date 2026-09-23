theory VIMP_Globals
  imports VIMP_Syntax
begin

section \<open>Locals and globals over the scalar store\<close>

text \<open>
  The store is one \<open>vname \<Rightarrow> int\<close> function; the locals/globals split is a
  classifier \<open>\<G> :: vname \<Rightarrow> bool\<close> on top of it. A call needs both halves of
  that split: \<open>enter_state\<close> keeps the globals and resets the locals on entry,
  \<open>combine_env caller callee\<close> restores the caller's locals and keeps the
  callee's globals on exit.

  \<open>combine_env\<close> is the single pointwise selector, generic in both key and
  codomain. \<open>enter_frame\<close> specializes it with a constant reset map. The
  concrete semantics uses these operations at \<open>store = vname \<Rightarrow> int\<close>, while
  abstract states reuse them at their own codomain.
\<close>

type_synonym pname = String.literal

definition combine_env ::
    "('k \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('k \<Rightarrow> 'a)" where
  "combine_env \<G> s t = (\<lambda>n. if \<G> n then t n else s n)"

definition enter_frame :: "('k \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('k \<Rightarrow> 'a)" where
  "enter_frame \<G> reset_val s = combine_env \<G> (\<lambda>_. reset_val) s"

definition enter_state :: "(vname \<Rightarrow> bool) \<Rightarrow> store \<Rightarrow> store" where
  "enter_state \<G> s = enter_frame \<G> 0 s"

lemma combine_query [simp]:
  "combine_env \<G> s t n = (if \<G> n then t n else s n)"
  unfolding combine_env_def by simp

lemma enter_frame_apply [simp]:
  "enter_frame \<G> reset_val s n = (if \<G> n then s n else reset_val)"
  unfolding enter_frame_def by simp

lemma enter_state_apply [simp]:
  "enter_state \<G> s n = (if \<G> n then s n else 0)"
  unfolding enter_state_def by simp

lemma combine_collapse [simp]:
  "combine_env \<G> s s = s"
  by (rule ext) simp

lemma combine_nest_left [simp]:
  "combine_env \<G> (combine_env \<G> s t) u = combine_env \<G> s u"
  by (rule ext) simp

lemma combine_nest_right [simp]:
  "combine_env \<G> s (combine_env \<G> t u) = combine_env \<G> s u"
  by (rule ext) simp

section \<open>C-faithful initial store set\<close>

text \<open>
  VIMP approximates C startup by initializing every global with no explicit
  initializer to 0 and leaving every other name of the initial store
  unconstrained. \<open>cinit_stores\<close> is the corresponding set of concrete stores:
  those where every global is 0, so \<open>main\<close>'s locals may hold any integer. It
  constrains only the initial store. A callee's locals do not come from it:
  \<open>enter_state\<close> resets them to 0 on every entry, which defines what C leaves
  indeterminate, as \<open>c_div\<close> defines division by zero. Neither convention is a
  model of C's indeterminate-value or undefined-behaviour rules, and VIMP has no
  global initializer syntax for a declaration such as \<open>int x = 42;\<close> to diverge
  from.
\<close>

definition cinit_stores :: "(vname \<Rightarrow> bool) \<Rightarrow> store set" where
  "cinit_stores \<G> = {s. \<forall>x. \<G> x \<longrightarrow> s x = 0}"

end

