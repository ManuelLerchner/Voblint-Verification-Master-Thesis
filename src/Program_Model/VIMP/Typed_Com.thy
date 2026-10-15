theory Typed_Com
  imports Typed_Exp VIMP_Program
begin

section \<open>Typed commands\<close>

text \<open>
  A typed command is the generic command type at identities and typed expressions,
  with the annotation left free. Elaboration resolves every name of a procedure and
  inserts the conversions C performs where a value is written: to the variable's kind
  at an assignment, to the formal's kind at an actual argument, and to the
  procedure's return kind at a return. A condition is evaluated at its own kind. The
  call destination is only resolved here, since converting the returned value to it
  happens when the frame is popped, which is the business of a typed semantics.
\<close>

type_synonym 'a tcom = "('a, var_id, texp) gcom"

text \<open>An actual argument converts to the kind of the formal it binds. An argument
  without a formal, which only a library call has, keeps its own kind.\<close>

fun elab_args :: "(vname \<Rightarrow> var_id) \<Rightarrow> kenv \<Rightarrow> var_id list \<Rightarrow> exp list \<Rightarrow> texp list" where
  "elab_args \<rho> \<kappa> (f # fs) (e # es) = elaborate \<rho> \<kappa> (\<kappa> f) e # elab_args \<rho> \<kappa> fs es"
| "elab_args \<rho> \<kappa> [] es = map (elaborate_syn \<rho> \<kappa>) es"
| "elab_args \<rho> \<kappa> fs [] = []"

lemma tvars_elab_args: "e \<in> set (elab_args \<rho> \<kappa> fs es) \<Longrightarrow> tvars e \<subseteq> range \<rho>"
  by (induction \<rho> \<kappa> fs es rule: elab_args.induct)
     (auto simp: elaborate_syn_def dest: subsetD [OF tvars_elaborate])

text \<open>\<open>fm p\<close> lists the formals of procedure \<open>p\<close>, empty for a library call, and
  \<open>q\<close> is the procedure whose body is elaborated.\<close>

fun elab_com ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pname \<Rightarrow> vname list) \<Rightarrow> kenv \<Rightarrow> pname
     \<Rightarrow> ('a, vname, exp) gcom \<Rightarrow> 'a tcom" where
  "elab_com \<G> fm \<kappa> q (SKIP i) = SKIP i"
| "elab_com \<G> fm \<kappa> q (Assign i x e) =
     Assign i (resolve_var \<G> q x) (elaborate (resolve_var \<G> q) \<kappa> (\<kappa> (resolve_var \<G> q x)) e)"
| "elab_com \<G> fm \<kappa> q (Check i l c) = Check i l (elaborate_syn (resolve_var \<G> q) \<kappa> c)"
| "elab_com \<G> fm \<kappa> q (Seq c1 c2) = Seq (elab_com \<G> fm \<kappa> q c1) (elab_com \<G> fm \<kappa> q c2)"
| "elab_com \<G> fm \<kappa> q (If i b c1 c2) =
     If i (elaborate_syn (resolve_var \<G> q) \<kappa> b) (elab_com \<G> fm \<kappa> q c1) (elab_com \<G> fm \<kappa> q c2)"
| "elab_com \<G> fm \<kappa> q (While i b c) =
     While i (elaborate_syn (resolve_var \<G> q) \<kappa> b) (elab_com \<G> fm \<kappa> q c)"
| "elab_com \<G> fm \<kappa> q (Call i dst p es) =
     Call i (map_option (resolve_var \<G> q) dst) p
       (elab_args (resolve_var \<G> q) \<kappa> (map (resolve_var \<G> p) (fm p)) es)"
| "elab_com \<G> fm \<kappa> q (Return i e) =
     Return i (map_option (elaborate (resolve_var \<G> q) \<kappa> (\<kappa> (ReturnId q))) e)"
| "elab_com \<G> fm \<kappa> q (Restore i) = Restore i"
| "elab_com \<G> fm \<kappa> q (Unwind i) = Unwind i"

subsection \<open>Well-typed commands\<close>

text \<open>A typed command is well-typed when its expressions are, and every written
  value already has the kind of the place it is written to. \<open>fids p\<close> lists the
  identities of the formals of \<open>p\<close>.\<close>

fun args_ok :: "kenv \<Rightarrow> var_id list \<Rightarrow> texp list \<Rightarrow> bool" where
  "args_ok \<kappa> (f # fs) (e # es) \<longleftrightarrow> texp_kind e = \<kappa> f \<and> args_ok \<kappa> fs es"
| "args_ok \<kappa> _ _ \<longleftrightarrow> True"

fun wt_tcom :: "kenv \<Rightarrow> (pname \<Rightarrow> var_id list) \<Rightarrow> pname \<Rightarrow> 'a tcom \<Rightarrow> bool" where
  "wt_tcom \<kappa> fids q (SKIP i) \<longleftrightarrow> True"
| "wt_tcom \<kappa> fids q (Assign i v e) \<longleftrightarrow> wt_texp \<kappa> e \<and> texp_kind e = \<kappa> v"
| "wt_tcom \<kappa> fids q (Check i l c) \<longleftrightarrow> wt_texp \<kappa> c"
| "wt_tcom \<kappa> fids q (Seq c1 c2) \<longleftrightarrow> wt_tcom \<kappa> fids q c1 \<and> wt_tcom \<kappa> fids q c2"
| "wt_tcom \<kappa> fids q (If i b c1 c2) \<longleftrightarrow>
     wt_texp \<kappa> b \<and> wt_tcom \<kappa> fids q c1 \<and> wt_tcom \<kappa> fids q c2"
| "wt_tcom \<kappa> fids q (While i b c) \<longleftrightarrow> wt_texp \<kappa> b \<and> wt_tcom \<kappa> fids q c"
| "wt_tcom \<kappa> fids q (Call i dst p es) \<longleftrightarrow> list_all (wt_texp \<kappa>) es \<and> args_ok \<kappa> (fids p) es"
| "wt_tcom \<kappa> fids q (Return i e) \<longleftrightarrow>
     pred_option (\<lambda>a. wt_texp \<kappa> a \<and> texp_kind a = \<kappa> (ReturnId q)) e"
| "wt_tcom \<kappa> fids q (Restore i) \<longleftrightarrow> True"
| "wt_tcom \<kappa> fids q (Unwind i) \<longleftrightarrow> True"

lemma elab_args_wt:
  "list_all (wt_texp \<kappa>) (elab_args \<rho> \<kappa> fs es) \<and> args_ok \<kappa> fs (elab_args \<rho> \<kappa> fs es)"
  by (induction \<rho> \<kappa> fs es rule: elab_args.induct)
     (simp_all add: wt_texp_elaborate elaborate_syn_def list_all_iff)

theorem wt_tcom_elab_com:
  "wt_tcom \<kappa> (\<lambda>p. map (resolve_var \<G> p) (fm p)) q (elab_com \<G> fm \<kappa> q c)"
  by (induction c)
     (simp_all add: wt_texp_elaborate elaborate_syn_def elab_args_wt option.pred_map comp_def
       option.pred_True)

subsection \<open>Erasure and shape\<close>

text \<open>Erasing a typed command names every identity by its source name and drops kinds
  and conversions. It returns the command elaboration started from. The statement is
  syntactic: a typed command and its erasure can execute differently wherever a kind
  wraps, so it says nothing about preserving behaviour.\<close>

abbreviation tcom_erase :: "'a tcom \<Rightarrow> ('a, vname, exp) gcom" where
  "tcom_erase \<equiv> map_gcom id var_name texp_erase"

lemma map_texp_erase_elab_args [simp]:
  assumes "\<And>x. var_name (\<rho> x) = x" and "list_all cast_free es"
  shows "map texp_erase (elab_args \<rho> \<kappa> fs es) = es"
  using assms(2)
proof (induction es arbitrary: fs)
  case Nil
  show ?case by (cases fs) simp_all
next
  case (Cons e es)
  have syn: "list_all cast_free xs \<Longrightarrow> map (\<lambda>a. texp_erase (elaborate_syn \<rho> \<kappa> a)) xs = xs"
    for xs
    by (induction xs) (simp_all add: elaborate_syn_def texp_erase_elaborate [OF assms(1)])
  show ?case
    using Cons syn
    by (cases fs) (simp_all add: texp_erase_elaborate [OF assms(1)] comp_def elaborate_syn_def)
qed

theorem tcom_erase_elab_com:
  assumes "\<forall>e \<in> set3_gcom c. cast_free e"
  shows "tcom_erase (elab_com \<G> fm \<kappa> q c) = c"
  using assms
proof (induction c)
  case (Return i e)
  then show ?case by (cases e) (simp_all add: texp_erase_elaborate [OF var_name_resolve_var])
qed (auto simp: texp_erase_elaborate [OF var_name_resolve_var] elaborate_syn_def
       map_texp_erase_elab_args [OF var_name_resolve_var] option.map_comp comp_def
       option.map_ident list_all_iff)

text \<open>
  Elaboration keeps a command's skeleton: the constructors, the annotations and the
  number of arguments of every call. Only the variables and expressions at its leaves
  change. Location elaboration (\<open>elab\<close>) reads nothing but that skeleton, so
  the order of the two elaborations cannot change which node a statement is assigned.
  Stating that as an equation needs location elaboration generalized to the typed
  command type, which belongs with the typed compilation.
\<close>

lemma length_elab_args [simp]: "length (elab_args \<rho> \<kappa> fs es) = length es"
  by (induction \<rho> \<kappa> fs es rule: elab_args.induct) simp_all

theorem skeleton_elab_com:
  "map_gcom id (\<lambda>_. ()) (\<lambda>_. ()) (elab_com \<G> fm \<kappa> q c) = map_gcom id (\<lambda>_. ()) (\<lambda>_. ()) c"
  by (induction c) (simp_all add: option.map_comp comp_def map_replicate_const)

subsection \<open>Programs\<close>

text \<open>Kinds are declared per identity, and an identity without a declaration is a C
  \<open>int\<close>.\<close>

type_synonym kind_decls = "(var_id \<times> ikind) list"

definition kenv_of :: "kind_decls \<Rightarrow> kenv" where
  "kenv_of ds v = (case map_of ds v of Some k \<Rightarrow> k | None \<Rightarrow> I32)"

definition prog_formals :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname list" where
  "prog_formals p q = (case prog_table p q of Some d \<Rightarrow> formals d | None \<Rightarrow> [])"

end
