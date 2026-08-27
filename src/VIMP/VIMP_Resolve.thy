theory VIMP_Resolve
  imports VIMP_Decls
begin

section \<open>Resolving source names to static identities\<close>

text \<open>
  A source program names its variables with bare \<^typ>\<open>vname\<close>s, and the same
  name means a different variable in each procedure that binds it.
  \<^const>\<open>prog_decls\<close> already records those distinct meanings as distinct
  \<^typ>\<open>var_id\<close>s. What is missing is the step that makes the compiled program
  use them.

  Resolution is that step, and it is a renaming: every occurrence of a name is
  replaced by \<^const>\<open>var_id_name\<close> of the identity it resolves to. Because
  that encoding is injective on separator-free identities, distinct identities
  become distinct names, so the flat \<^const>\<open>prog_tyenv\<close> of the renamed program
  answers exactly what \<^const>\<open>kind_of_var\<close> answers for the identity. The
  program that reaches the compiler is scoped, while every type in the
  pipeline -- store, abstract state, solver unknown -- stays keyed by
  \<^typ>\<open>vname\<close>.

  The alternative, parameterizing the syntax over its variable type, would
  reach every store, abstract state and solver unknown, and it would still
  have to answer how \<open>pstep\<close> resolves a name: that relation fixes one
  environment for the whole program and its configuration carries no procedure
  identity, so a per-procedure environment cannot be read there at all.
  Renaming reaches the commands themselves, which is where the resolution has
  to land, and leaves every signature alone.
\<close>

subsection \<open>Scopes\<close>

text \<open>
  A procedure binds its formals and its declared locals. Every other name it
  mentions is either a declared global or an implicit local; C would reject
  the latter, VIMP gives it a synthetic binding in the procedure that mentions
  it, which is what the corpus's read-only implicit locals already rely on.
\<close>

definition proc_bound :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname set" where
  "proc_bound p q = set (proc_formals p q) \<union> tv_name ` set (proc_scoped_decls p q)"

lemma finite_proc_bound [simp]: "finite (proc_bound p q)"
  by (simp add: proc_bound_def)

text \<open>
  A formal or a declared local shadows a global of the same name, as in C.
  The resolver rejects that collision outright, so the branch order below is
  the rule rather than a tie-break, but stating it here keeps
  \<open>resolve_name\<close> total and independent of validation.
\<close>

definition resolve_name :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname \<Rightarrow> var_id" where
  "resolve_name p q x =
     (if x \<notin> proc_bound p q \<and> declared_global p x then GlobalId x else ScopedId q x)"

lemma resolve_name_global [simp]:
  "x \<notin> proc_bound p q \<Longrightarrow> declared_global p x \<Longrightarrow> resolve_name p q x = GlobalId x"
  by (simp add: resolve_name_def)

lemma resolve_name_scoped [simp]:
  "x \<in> proc_bound p q \<Longrightarrow> resolve_name p q x = ScopedId q x"
  by (simp add: resolve_name_def)

lemma resolve_name_implicit_local [simp]:
  "\<not> declared_global p x \<Longrightarrow> resolve_name p q x = ScopedId q x"
  by (simp add: resolve_name_def)

definition rename_name :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname \<Rightarrow> vname" where
  "rename_name p q x = var_id_name (resolve_name p q x)"

lemma rename_name_global [simp]:
  "x \<notin> proc_bound p q \<Longrightarrow> declared_global p x \<Longrightarrow> rename_name p q x = x"
  by (simp add: rename_name_def)

text \<open>
  A declared global keeps its own name, so an unscoped program is represented
  exactly as it is today and \<^const>\<open>declared_global\<close> still classifies the
  renamed program correctly with no adjustment.
\<close>

subsection \<open>Renaming a procedure\<close>

definition rename_proc :: "imp_prog \<Rightarrow> pname \<Rightarrow> proc_decl \<Rightarrow> proc_decl" where
  "rename_proc p q d =
     \<lparr>formals = map (rename_name p q) (formals d),
      body = rename_com (rename_name p q) (body d),
      ret_kind = ret_kind d\<rparr>"

lemma formals_rename_proc [simp]:
  "formals (rename_proc p q d) = map (rename_name p q) (formals d)"
  by (simp add: rename_proc_def)

lemma ret_kind_rename_proc [simp]: "ret_kind (rename_proc p q d) = ret_kind d"
  by (simp add: rename_proc_def)

subsection \<open>The names a procedure mentions\<close>

definition proc_names :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname list" where
  "proc_names p q =
     sorted_list_of_set
       (proc_bound p q \<union>
        (case prog_table p q of None \<Rightarrow> {} | Some d \<Rightarrow> com_vnames (body d)))"

lemma set_proc_names [simp]:
  "set (proc_names p q) =
     proc_bound p q \<union>
     (case prog_table p q of None \<Rightarrow> {} | Some d \<Rightarrow> com_vnames (body d))"
  unfolding proc_names_def by (auto split: option.splits)

lemma proc_bound_subset_proc_names: "proc_bound p q \<subseteq> set (proc_names p q)"
  by auto

subsection \<open>The resolved kind table\<close>

text \<open>
  The resolved program's declarations are one entry per identity: a declared
  global under its own name, and every procedure-scoped name under the
  identity its procedure gives it. Building the list keyed by \<^typ>\<open>var_id\<close>
  first and encoding afterwards is what makes the lookup theorem below a
  statement about \<^const>\<open>var_id_name\<close> being injective rather than about the
  shape of a concatenation.
\<close>

definition scoped_names :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname list" where
  "scoped_names p q = filter (\<lambda>x. x \<notin> proc_bound p q \<longrightarrow> \<not> declared_global p x)
                             (proc_names p q)"

lemma scoped_names_iff [simp]:
  "x \<in> set (scoped_names p q) \<longleftrightarrow>
     x \<in> set (proc_names p q) \<and> resolve_name p q x = ScopedId q x"
  by (auto simp: scoped_names_def resolve_name_def)

definition id_kind_entries :: "imp_prog \<Rightarrow> (var_id \<times> ikind) list" where
  "id_kind_entries p =
     map (\<lambda>x. (GlobalId x, prog_tyenv p x)) (declared_global_vars p)
     @ concat (map (\<lambda>q. map (\<lambda>x. (ScopedId q x, scoped_kind p q x)) (scoped_names p q))
                   (map fst (proc_rep p)))"

lemma id_kind_entries_GlobalId:
  "x \<in> set (declared_global_vars p) \<Longrightarrow>
     (GlobalId x, prog_tyenv p x) \<in> set (id_kind_entries p)"
  by (force simp: id_kind_entries_def)

lemma id_kind_entries_ScopedId:
  assumes "q \<in> set (map fst (proc_rep p))" and "x \<in> set (scoped_names p q)"
  shows "(ScopedId q x, scoped_kind p q x) \<in> set (id_kind_entries p)"
  using assms by (force simp: id_kind_entries_def)

definition resolved_kinds :: "imp_prog \<Rightarrow> typed_var list" where
  "resolved_kinds p = map (\<lambda>e. TV (var_id_name (fst e)) (snd e)) (id_kind_entries p)"

subsection \<open>The resolved program\<close>

text \<open>
  A resolved program needs no scoped table to answer a kind -- every name in
  it is already an identity and the flat list carries every declaration -- but
  it keeps one, renamed, because printing the program back needs to know which
  procedure declared each local. \<^const>\<open>display_scoped\<close> is what turns those
  identities back into the names the source wrote.
\<close>

definition resolved_scoped :: "imp_prog \<Rightarrow> (pname \<times> typed_var) list" where
  "resolved_scoped p =
     map (\<lambda>e. (fst e,
                TV (var_id_name (ScopedId (fst e) (tv_name (snd e)))) (tv_kind (snd e))))
         (declared_scoped p)"

definition resolve_prog :: "imp_prog \<Rightarrow> imp_prog" where
  "resolve_prog p =
     imp_prog.make
       (map (\<lambda>e. (fst e, rename_proc p (fst e) (snd e))) (proc_rep p))
       (declared_global_vars p)
       (resolved_kinds p)
       (resolved_scoped p)"

lemma declared_global_vars_resolve_prog [simp]:
  "declared_global_vars (resolve_prog p) = declared_global_vars p"
  by (simp add: resolve_prog_def imp_prog.make_def)

lemma declared_global_resolve_prog [simp]:
  "declared_global (resolve_prog p) x \<longleftrightarrow> declared_global p x"
  by simp

lemma declared_kinds_resolve_prog [simp]:
  "declared_kinds (resolve_prog p) = resolved_kinds p"
  by (simp add: resolve_prog_def imp_prog.make_def)

lemma proc_rep_resolve_prog [simp]:
  "proc_rep (resolve_prog p) = map (\<lambda>e. (fst e, rename_proc p (fst e) (snd e))) (proc_rep p)"
  by (simp add: resolve_prog_def imp_prog.make_def)

lemma prog_table_resolve_prog:
  "prog_table (resolve_prog p) q = map_option (rename_proc p q) (prog_table p q)"
proof -
  have "map_of (map (\<lambda>e. (fst e, rename_proc p (fst e) (snd e))) xs) q
          = map_option (rename_proc p q) (map_of xs q)" for xs :: "(pname \<times> proc_decl) list"
    by (induct xs) auto
  then show ?thesis by (simp add: prog_table_def)
qed

lemma prog_procs_resolve_prog [simp]: "prog_procs (resolve_prog p) = prog_procs p"
  by (simp add: prog_procs_def comp_def)

subsection \<open>Validation\<close>

text \<open>
  Resolution is only meaningful where the identities it builds are pairwise
  distinct and separator-free, since that is exactly what makes
  \<^const>\<open>var_id_name\<close> injective on them. The checks below are those
  conditions, decided rather than assumed, so the lookup theorem holds
  unconditionally once a program passes.
\<close>

datatype resolve_error =
    DuplicateProcedure pname
  | DuplicateGlobal vname
  | DuplicateFormal pname
  | DuplicateScopedDecl pname
  | GlobalBoundInProcedure pname vname
  | SeparatorInName vname
  | AmbiguousIdentity
  | MissingEntryProcedure

definition proc_error :: "imp_prog \<Rightarrow> pname \<times> proc_decl \<Rightarrow> resolve_error list" where
  "proc_error p e =
     (if \<not> distinct (formals (snd e)) then [DuplicateFormal (fst e)] else [])
     @ (if \<not> distinct (map tv_name (proc_scoped_decls p (fst e)))
        then [DuplicateScopedDecl (fst e)] else [])
     @ map (GlobalBoundInProcedure (fst e))
           (filter (declared_global p) (sorted_list_of_set (proc_bound p (fst e))))"

definition sep_free_error :: "imp_prog \<Rightarrow> resolve_error list" where
  "sep_free_error p =
     map SeparatorInName
       (filter (\<lambda>x. \<not> sep_free x)
          (declared_global_vars p @ map fst (proc_rep p)
           @ concat (map (\<lambda>q. proc_names p q) (map fst (proc_rep p)))))"

definition resolve_errors :: "imp_prog \<Rightarrow> resolve_error list" where
  "resolve_errors p =
     (if \<not> distinct (map fst (proc_rep p))
      then map DuplicateProcedure (map fst (proc_rep p)) else [])
     @ (if \<not> distinct (declared_global_vars p)
        then map DuplicateGlobal (declared_global_vars p) else [])
     @ concat (map (proc_error p) (proc_rep p))
     @ sep_free_error p
     @ (if \<not> distinct (map fst (id_kind_entries p)) then [AmbiguousIdentity] else [])
     @ (if prog_table p prog_main_name = None then [MissingEntryProcedure] else [])"

definition resolve :: "imp_prog \<Rightarrow> resolve_error list + imp_prog" where
  "resolve p = (case resolve_errors p of [] \<Rightarrow> Inr (resolve_prog p) | es \<Rightarrow> Inl es)"

lemma resolve_InrD:
  assumes "resolve p = Inr rp"
  shows "resolve_errors p = []" and "rp = resolve_prog p"
  using assms by (auto simp: resolve_def split: list.splits)

lemma resolve_errors_NilD:
  assumes "resolve_errors p = []"
  shows "distinct (map fst (id_kind_entries p))"
    and "\<forall>x \<in> set (declared_global_vars p). sep_free x"
    and "\<forall>q \<in> set (map fst (proc_rep p)). sep_free q"
    and "\<forall>q \<in> set (map fst (proc_rep p)). \<forall>x \<in> set (proc_names p q). sep_free x"
    and "prog_table p prog_main_name \<noteq> None"
  using assms
  by (auto simp: resolve_errors_def sep_free_error_def filter_empty_conv
           split: if_splits)

lemma resolve_errors_scoped_distinct:
  assumes "resolve_errors p = []" and "q \<in> set (map fst (proc_rep p))"
  shows "distinct (map tv_name (proc_scoped_decls p q))"
proof -
  from assms(1) have "concat (map (proc_error p) (proc_rep p)) = []"
    by (simp add: resolve_errors_def split: if_splits)
  moreover from assms(2) obtain d where "(q, d) \<in> set (proc_rep p)" by auto
  ultimately have "proc_error p (q, d) = []" by simp
  then show ?thesis by (simp add: proc_error_def split: if_splits)
qed

subsection \<open>Every identity is separator-free\<close>

lemma var_id_sep_free_entries:
  assumes "resolve_errors p = []" and "v \<in> fst ` set (id_kind_entries p)"
  shows "var_id_sep_free v"
proof -
  have g: "\<forall>x \<in> set (declared_global_vars p). sep_free x"
    and q: "\<forall>q \<in> set (map fst (proc_rep p)). sep_free q"
    and n: "\<forall>q \<in> set (map fst (proc_rep p)). \<forall>x \<in> set (proc_names p q). sep_free x"
    using assms(1) by (rule resolve_errors_NilD)+
  from assms(2) show ?thesis
    using g q n
    by (fastforce simp: id_kind_entries_def var_id_sep_free_def scoped_names_def)
qed

subsection \<open>The resolved program answers by identity\<close>

text \<open>
  The one lemma the whole construction rests on: encoding an injective key map
  through \<^const>\<open>var_id_name\<close> leaves the lookup alone.
\<close>

lemma map_of_map_key:
  assumes "inj_on f (insert k (fst ` set es))"
  shows "map_of (map (\<lambda>e. (f (fst e), snd e)) es) (f k) = map_of es k"
  using assms
proof (induct es)
  case (Cons e es)
  have "inj_on f (insert k (fst ` set es))"
    using Cons.prems by (auto elim: inj_on_subset)
  moreover have "f (fst e) = f k \<longleftrightarrow> fst e = k"
    using Cons.prems by (auto simp: inj_on_def)
  ultimately show ?case using Cons.hyps by auto
qed simp

lemma inj_on_var_id_name_entries:
  assumes "resolve_errors p = []"
  shows "inj_on var_id_name (fst ` set (id_kind_entries p))"
  using var_id_sep_free_entries[OF assms]
  by (auto simp: inj_on_def intro: var_id_name_inj)

lemma prog_tyenv_resolve_prog:
  assumes "resolve_errors p = []" and "(v, k) \<in> set (id_kind_entries p)"
  shows "prog_tyenv (resolve_prog p) (var_id_name v) = k"
proof -
  have inj: "inj_on var_id_name (insert v (fst ` set (id_kind_entries p)))"
    using inj_on_var_id_name_entries[OF assms(1)] assms(2)
    by (simp add: insert_absorb rev_image_eqI)
  have dist: "distinct (map fst (id_kind_entries p))"
    using assms(1) by (rule resolve_errors_NilD)
  have "map_of (id_kind_entries p) v = Some k"
    using dist assms(2) by (rule map_of_is_SomeI)
  moreover have
    "map_of (map (\<lambda>e. (var_id_name (fst e), snd e)) (id_kind_entries p)) (var_id_name v)
       = map_of (id_kind_entries p) v"
    by (rule map_of_map_key[OF inj])
  ultimately show ?thesis
    by (simp add: prog_tyenv_def tv_env_def resolved_kinds_def comp_def)
qed

theorem prog_tyenv_resolve_scoped:
  assumes "resolve p = Inr rp"
      and "q \<in> set (map fst (proc_rep p))"
      and "x \<in> set (scoped_names p q)"
  shows "prog_tyenv rp (var_id_name (ScopedId q x)) = scoped_kind p q x"
  using resolve_InrD[OF assms(1)]
        prog_tyenv_resolve_prog[OF _ id_kind_entries_ScopedId[OF assms(2,3)]]
  by simp

theorem prog_tyenv_resolve_global:
  assumes "resolve p = Inr rp" and "x \<in> set (declared_global_vars p)"
  shows "prog_tyenv rp x = prog_tyenv p x"
  using resolve_InrD[OF assms(1)]
        prog_tyenv_resolve_prog[OF _ id_kind_entries_GlobalId[OF assms(2)]]
  by simp

text \<open>
  A bound name's resolved kind is the one its own declaration gives it. This
  is what the flat environment of the source program could not do: there,
  \<open>n\<close> answers with whichever procedure's declaration the collection order
  happened to record first.
\<close>

lemma scoped_kind_declared:
  assumes "distinct (map tv_name (proc_scoped_decls p q))"
      and "tv \<in> set (proc_scoped_decls p q)"
  shows "scoped_kind p q (tv_name tv) = tv_kind tv"
proof -
  have "distinct (map fst (map (\<lambda>t. (tv_name t, tv_kind t)) (proc_scoped_decls p q)))"
    using assms(1) by (simp add: comp_def)
  moreover have
    "(tv_name tv, tv_kind tv) \<in> set (map (\<lambda>t. (tv_name t, tv_kind t)) (proc_scoped_decls p q))"
    using assms(2) by force
  ultimately have "scoped_kind_of p q (tv_name tv) = Some (tv_kind tv)"
    unfolding scoped_kind_of_def by (rule map_of_is_SomeI)
  then show ?thesis by (simp add: scoped_kind_def)
qed

theorem prog_tyenv_resolve_declaration:
  assumes "resolve p = Inr rp"
      and "q \<in> set (map fst (proc_rep p))"
      and "tv \<in> set (proc_scoped_decls p q)"
      and "tv_name tv \<in> set (scoped_names p q)"
  shows "prog_tyenv rp (var_id_name (ScopedId q (tv_name tv))) = tv_kind tv"
proof -
  have "distinct (map tv_name (proc_scoped_decls p q))"
    using resolve_InrD(1)[OF assms(1)] assms(2)
    by (rule resolve_errors_scoped_distinct)
  then show ?thesis
    using prog_tyenv_resolve_scoped[OF assms(1,2,4)] scoped_kind_declared[OF _ assms(3)]
    by simp
qed

subsection \<open>Witness\<close>

text \<open>
  The defect the whole construction exists to close. Two procedures take a
  parameter \<open>n\<close> at different kinds; the source program's flat environment
  answers \<^const>\<open>U8\<close> for both, and the resolved program answers each
  procedure's own declaration.
\<close>

lemma resolve_two_kind_formals [simp]:
  "prog_tyenv (resolve_prog two_kind_formals_prog)
     (var_id_name (ScopedId (STR ''f'') (STR ''n''))) = U8"
  "prog_tyenv (resolve_prog two_kind_formals_prog)
     (var_id_name (ScopedId (STR ''g'') (STR ''n''))) = I64"
  by (eval, eval)

lemma resolve_two_kind_formals_accepted:
  "resolve_errors two_kind_formals_prog = []"
  by eval

end
