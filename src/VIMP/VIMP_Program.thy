theory VIMP_Program
  imports VIMP_Proc
begin

section \<open>Whole programs\<close>

text \<open>
  \<open>declared_global_vars\<close> is the declared-global list in source order; a list,
  so finiteness is by type. \<open>declared_global\<close> is the derived classifier every
  program-level operation uses; procedure-level interfaces take the classifier
  as an explicit \<open>vname \<Rightarrow> bool\<close> argument instead.
\<close>

record imp_prog =
  proc_rep :: "(pname * proc_decl) list"
  declared_global_vars :: "vname list"

definition declared_global :: "imp_prog \<Rightarrow> vname \<Rightarrow> bool" where
  "declared_global p x \<longleftrightarrow> x \<in> set (declared_global_vars p)"

lemma declared_global_iff [simp]:
  "declared_global p x \<longleftrightarrow> x \<in> set (declared_global_vars p)"
  by (simp add: declared_global_def)

text \<open>The \<open>program\<close> parser fixes the entry name and rejects formals on it, so
  \<open>main\<close> is an ordinary \<open>proc_rep\<close> entry. \<open>prog_main\<close> is total through \<open>the\<close>;
  \<open>wf_source_program\<close>'s entry conjunct is what makes the lookup meaningful.\<close>

definition prog_table :: "imp_prog \<Rightarrow> proc_table" where
  "prog_table p = map_of (proc_rep p)"

definition prog_procs :: "imp_prog \<Rightarrow> pname list" where
  "prog_procs p = filter (\<lambda>n. n \<noteq> prog_main_name) (map fst (proc_rep p))"

definition prog_main :: "imp_prog \<Rightarrow> com" where
  "prog_main p = main_body (prog_table p)"

lemma prog_main_eq_main_body [simp]: "main_body (prog_table p) = prog_main p"
  by (simp add: prog_main_def)

text \<open>\<open>mk_program\<close> conses the entry onto \<open>proc_rep\<close>, so a program built through
  it satisfies \<open>wf_source_program\<close>'s entry conjunct by construction.\<close>
definition mk_program :: "(pname * proc_decl) list \<Rightarrow> com \<Rightarrow> vname list \<Rightarrow> imp_prog" where
  "mk_program ps m gv = imp_prog.make ((prog_main_name, \<lparr>formals = [], body = m\<rparr>) # ps) gv"

lemma mk_program_simps [simp]:
  "prog_table (mk_program ps m gv) = (map_of ps)(prog_main_name \<mapsto> \<lparr>formals = [], body = m\<rparr>)"
  "prog_main (mk_program ps m gv) = m"
  "declared_global_vars (mk_program ps m gv) = gv"
  "prog_main_name \<notin> set (map fst ps) \<Longrightarrow> prog_procs (mk_program ps m gv) = map fst ps"
  by (force simp: prog_table_def prog_main_def main_body_def prog_procs_def mk_program_def
      imp_prog.make_def filter_id_conv)+

text \<open>The finite variable scope of an activation: every declared global, the
  activation's formals and body occurrences, and the reserved return location.\<close>

definition scope_vnames :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname set" where
  "scope_vnames p owner =
    set (declared_global_vars p) \<union> {ret_var} \<union>
    (case prog_table p owner of
      None \<Rightarrow> {} |
      Some decl \<Rightarrow> set (formals decl) \<union> com_vnames (body decl))"

lemma finite_scope_vnames [simp]: "finite (scope_vnames p owner)"
  unfolding scope_vnames_def by (auto split: option.splits)

definition scope_vnames_list :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname list" where
  "scope_vnames_list p owner = sorted_list_of_set (scope_vnames p owner)"

lemma set_scope_vnames_list [simp]:
  "set (scope_vnames_list p owner) = scope_vnames p owner"
  unfolding scope_vnames_list_def by simp

end
