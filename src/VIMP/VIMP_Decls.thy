theory VIMP_Decls
  imports VIMP_Notation VIMP_Var_Id
begin

section \<open>Declaration tables from a program\<close>

text \<open>
  A program's declarations reach the typed core as a \<^type>\<open>decl_table\<close> keyed by
  \<^type>\<open>var_id\<close> rather than by name. Three sources feed it: the declared
  globals, each procedure's formals, and each procedure's declared locals.

  Globals and formals still read their kind out of \<^const>\<open>prog_tyenv\<close>, which
  answers by name alone. That is the remaining order-dependence: two procedures
  whose formals share a name share whatever kind the flat declaration list
  happened to record first. Locals do not go through it -- they arrive already
  paired with the procedure that binds them -- so a local is the one of the
  three whose kind is decided by its own declaration. Closing the rest means
  recording formals scoped at the frontend as well.
\<close>

definition global_entries :: "imp_prog \<Rightarrow> (var_id \<times> var_info) list" where
  "global_entries p =
     map (\<lambda>x. (GlobalId x, \<lparr>vi_kind = prog_tyenv p x, vi_origin = SourceGlobal\<rparr>))
         (declared_global_vars p)"

definition formal_entries :: "imp_prog \<Rightarrow> (var_id \<times> var_info) list" where
  "formal_entries p =
     concat (map (\<lambda>(q, d).
               map (\<lambda>x. (ScopedId q x,
                          \<lparr>vi_kind = prog_tyenv p x, vi_origin = SourceFormal\<rparr>))
                   (formals d))
             (proc_rep p))"

definition local_entries :: "imp_prog \<Rightarrow> (var_id \<times> var_info) list" where
  "local_entries p =
     map (\<lambda>(q, tv). (ScopedId q (tv_name tv),
                      \<lparr>vi_kind = tv_kind tv, vi_origin = SourceLocal\<rparr>))
         (declared_locals p)"

definition prog_decls :: "imp_prog \<Rightarrow> decl_table" where
  "prog_decls p = map_of (global_entries p @ formal_entries p @ local_entries p)"

subsection \<open>Well-formedness\<close>

text \<open>
  Every entry is filed under an identity whose shape matches its recorded
  origin, by construction: each of the three lists builds exactly one
  constructor. Uniqueness needs no argument -- \<^const>\<open>map_of\<close> keys on the
  identity, and a name-carrying identity makes one binding per name per scope
  automatic.
\<close>

lemma origin_fits_global_entries:
  "(v, vi) \<in> set (global_entries p) \<Longrightarrow> origin_fits v (vi_origin vi)"
  by (auto simp: global_entries_def)

lemma origin_fits_formal_entries:
  "(v, vi) \<in> set (formal_entries p) \<Longrightarrow> origin_fits v (vi_origin vi)"
  by (auto simp: formal_entries_def split: prod.splits)

lemma origin_fits_local_entries:
  "(v, vi) \<in> set (local_entries p) \<Longrightarrow> origin_fits v (vi_origin vi)"
  by (auto simp: local_entries_def split: prod.splits)

lemma wf_decls_prog_decls [simp]: "wf_decls (prog_decls p)"
  unfolding wf_decls_def prog_decls_def
proof (intro allI impI)
  fix v vi
  assume "map_of (global_entries p @ formal_entries p @ local_entries p) v = Some vi"
  then have "(v, vi) \<in> set (global_entries p @ formal_entries p @ local_entries p)"
    by (rule map_of_SomeD)
  then show "origin_fits v (vi_origin vi)"
    using origin_fits_global_entries origin_fits_formal_entries origin_fits_local_entries
    by auto
qed

subsection \<open>Reading a declaration back\<close>

text \<open>
  A global's identity is never shadowed by a procedure's, so a declared global
  keeps its kind whatever the procedures declare.
\<close>

lemma map_of_map_GlobalId:
  "x \<in> set xs \<Longrightarrow> map_of (map (\<lambda>y. (GlobalId y, f y)) xs) (GlobalId x) = Some (f x)"
  by (induct xs) auto

lemma kind_of_var_GlobalId:
  assumes "x \<in> set (declared_global_vars p)"
  shows "kind_of_var (prog_decls p) (GlobalId x) = Some (prog_tyenv p x)"
  using assms
  by (simp add: prog_decls_def kind_of_var_def global_entries_def
                map_of_append map_add_def map_of_map_GlobalId)

subsection \<open>Scoped locals\<close>

text \<open>
  The point of the whole table. Two procedures declare \<open>acc\<close> at different
  kinds; each identity answers with its own declaration, while
  \<^const>\<open>prog_tyenv\<close> -- which is keyed by name -- cannot tell them apart and
  answers \<open>I32\<close> for both, that being what a name absent from the flat
  declaration list defaults to.
\<close>

abbreviation two_kinds_prog :: imp_prog where
  "two_kinds_prog \<equiv> program {
     void f(n) { uint8 acc; acc := n; return acc }
     void g(n) { int64 acc; acc := n; return acc }
     void main() { int32 a, b; a := f(1); b := g(2) }
   }"

lemma prog_decls_scoped_locals_disagree [simp]:
  "kind_of_var (prog_decls two_kinds_prog) (ScopedId (STR ''f'') (STR ''acc'')) = Some U8"
  "kind_of_var (prog_decls two_kinds_prog) (ScopedId (STR ''g'') (STR ''acc'')) = Some I64"
  by (simp_all add: prog_decls_def kind_of_var_def global_entries_def
                    formal_entries_def local_entries_def prog_tyenv_def tv_env_def
                    mk_program_typed_def imp_prog.make_def proc_decl_of_def)

lemma prog_tyenv_cannot_tell_them_apart:
  "prog_tyenv two_kinds_prog (STR ''acc'') = I32"
  by (simp add: prog_tyenv_def tv_env_def)

end
