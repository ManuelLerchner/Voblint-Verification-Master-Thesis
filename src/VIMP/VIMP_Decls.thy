theory VIMP_Decls
  imports VIMP_Notation VIMP_Var_Id
begin

section \<open>Declaration tables from a program\<close>

text \<open>
  A program's declarations reach the typed core as a \<^type>\<open>decl_table\<close> keyed by
  \<^type>\<open>var_id\<close> rather than by name. Two sources feed it: the declared
  globals, and each procedure's scoped declarations -- its annotated formals
  and its declared locals alike.

  A global's kind comes from \<^const>\<open>prog_tyenv\<close>, which is sound for globals:
  a global name is unique program-wide, so answering by name alone answers
  correctly. A procedure-scoped name does not go through it. Its kind comes
  from \<^const>\<open>declared_scoped\<close>, which pairs each declaration with the
  procedure that binds it, so two procedures may bind one name at two kinds
  and each identity answers with its own declaration.

  The flat list remains the fallback for a formal the source left unannotated,
  which is the one case where no scoped declaration exists to read.
\<close>

definition proc_formals :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname list" where
  "proc_formals p q = (case prog_table p q of None \<Rightarrow> [] | Some d \<Rightarrow> formals d)"

definition proc_scoped_decls :: "imp_prog \<Rightarrow> pname \<Rightarrow> typed_var list" where
  "proc_scoped_decls p q = map snd (filter (\<lambda>e. fst e = q) (declared_scoped p))"

definition scoped_kind_of :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname \<Rightarrow> ikind option" where
  "scoped_kind_of p q =
     map_of (map (\<lambda>tv. (tv_name tv, tv_kind tv)) (proc_scoped_decls p q))"

text \<open>
  \<open>scoped_kind\<close> is the total reading: the procedure's own declaration
  where there is one, and otherwise the flat environment, which is what an
  unannotated formal or an implicit local resolves to.
\<close>

definition scoped_kind :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname \<Rightarrow> ikind" where
  "scoped_kind p q x =
     (case scoped_kind_of p q x of Some k \<Rightarrow> k | None \<Rightarrow> prog_tyenv p x)"

definition global_entries :: "imp_prog \<Rightarrow> (var_id \<times> var_info) list" where
  "global_entries p =
     map (\<lambda>x. (GlobalId x, \<lparr>vi_kind = prog_tyenv p x, vi_origin = SourceGlobal\<rparr>))
         (declared_global_vars p)"

definition formal_entries :: "imp_prog \<Rightarrow> (var_id \<times> var_info) list" where
  "formal_entries p =
     concat (map (\<lambda>(q, d).
               map (\<lambda>x. (ScopedId q x,
                          \<lparr>vi_kind = scoped_kind p q x, vi_origin = SourceFormal\<rparr>))
                   (formals d))
             (proc_rep p))"

text \<open>
  \<open>scoped_entries\<close> also covers the annotated formals, since they share
  \<^const>\<open>declared_scoped\<close> with the locals. \<open>prog_decls\<close> puts
  \<^const>\<open>formal_entries\<close> first, so a formal keeps its \<^const>\<open>SourceFormal\<close>
  origin and the duplicate here is shadowed; both agree on the kind.
\<close>

definition scoped_entries :: "imp_prog \<Rightarrow> (var_id \<times> var_info) list" where
  "scoped_entries p =
     map (\<lambda>(q, tv). (ScopedId q (tv_name tv),
                      \<lparr>vi_kind = tv_kind tv, vi_origin = SourceLocal\<rparr>))
         (declared_scoped p)"

definition prog_decls :: "imp_prog \<Rightarrow> decl_table" where
  "prog_decls p = map_of (global_entries p @ formal_entries p @ scoped_entries p)"

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

lemma origin_fits_scoped_entries:
  "(v, vi) \<in> set (scoped_entries p) \<Longrightarrow> origin_fits v (vi_origin vi)"
  by (auto simp: scoped_entries_def split: prod.splits)

lemma wf_decls_prog_decls [simp]: "wf_decls (prog_decls p)"
  unfolding wf_decls_def prog_decls_def
proof (intro allI impI)
  fix v vi
  assume "map_of (global_entries p @ formal_entries p @ scoped_entries p) v = Some vi"
  then have "(v, vi) \<in> set (global_entries p @ formal_entries p @ scoped_entries p)"
    by (rule map_of_SomeD)
  then show "origin_fits v (vi_origin vi)"
    using origin_fits_global_entries origin_fits_formal_entries origin_fits_scoped_entries
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

subsection \<open>Scoped declarations\<close>

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
                    formal_entries_def scoped_entries_def prog_tyenv_def tv_env_def
                    mk_program_typed_def imp_prog.make_def proc_decl_of_def)

lemma prog_tyenv_cannot_tell_them_apart:
  "prog_tyenv two_kinds_prog (STR ''acc'') = I32"
  by (simp add: prog_tyenv_def tv_env_def)

text \<open>
  Formals resolve the same way, which is what the flat environment got wrong
  rather than merely imprecise: two procedures take a parameter \<open>n\<close> at
  different kinds, and \<^const>\<open>prog_tyenv\<close> answers whichever declaration the
  flat list happened to record first for both of them.
\<close>

abbreviation two_kind_formals_prog :: imp_prog where
  "two_kind_formals_prog \<equiv> program {
     uint8 f(uint8 n) { return n + 200 }
     int64 g(int64 n) { return n + 200 }
     void main() { int32 a, b; a := f(100); b := g(100) }
   }"

lemma prog_decls_scoped_formals_disagree [simp]:
  "kind_of_var (prog_decls two_kind_formals_prog) (ScopedId (STR ''f'') (STR ''n'')) = Some U8"
  "kind_of_var (prog_decls two_kind_formals_prog) (ScopedId (STR ''g'') (STR ''n'')) = Some I64"
  by (simp_all add: prog_decls_def kind_of_var_def global_entries_def
                    formal_entries_def scoped_entries_def scoped_kind_def
                    scoped_kind_of_def proc_scoped_decls_def prog_table_def
                    prog_main_name_def mk_program_typed_def imp_prog.make_def
                    proc_decl_of_def proc_decl_of_typed_def)

lemma prog_tyenv_cannot_tell_formals_apart:
  "prog_tyenv two_kind_formals_prog (STR ''n'') = U8"
  by (simp add: prog_tyenv_def tv_env_def)

end
