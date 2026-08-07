theory VIMP_Globals
  imports VIMP_Syntax
begin

section \<open>Locals and globals over the scalar store\<close>

text \<open>
  The store is a single \<open>vname => int\<close> function; the locals/globals split is a
  classifier \<open>gs :: vname => bool\<close> layered on top of it, not a separate
  representation. \<open>combine_states\<close> \<open><s|t>\<close> takes locals from \<open>s\<close> and globals
  from \<open>t\<close>, as decided by \<open>gs\<close>. This is the splitting a procedure call needs
  on both ends: on entry the caller's store is saved and locals reset
  (\<open>enter_state\<close>), on exit the callee's globals are kept and the caller's
  locals restored (\<open><caller|callee>\<close>).

  Self-contained: depends only on the store, not on \<open>com\<close>, small-step, or the
  CFG.
\<close>

(* Procedure names. *)
type_synonym pname = string

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

text \<open>A name-based classifier, for illustration only: names starting with
  @{text G} are global. \<open>combine_states\<close> and \<open>enter_state\<close> take any
  classifier of this type; nothing in this theory is tied to this one.\<close>
definition example_gs :: "vname \<Rightarrow> bool" where
  "example_gs x = (x = [] \<or> hd x = CHR ''G'')"

value "example_gs ''Gx''"
value "example_gs ''x''"
value "example_gs []"

value "combine_states example_gs
         ((\<lambda>_. 0::int)(''x'' := 1, ''Gx'' := 2)) ((\<lambda>_. 0::int)(''x'' := 9, ''Gx'' := 5)) ''x''"
value "combine_states example_gs
         ((\<lambda>_. 0::int)(''x'' := 1, ''Gx'' := 2)) ((\<lambda>_. 0::int)(''x'' := 9, ''Gx'' := 5)) ''Gx''"

value "enter_state example_gs ((\<lambda>_. 0::int)(''x'' := 7, ''Gx'' := 3)) ''x''"
value "enter_state example_gs ((\<lambda>_. 0::int)(''x'' := 7, ''Gx'' := 3)) ''Gx''"

end
