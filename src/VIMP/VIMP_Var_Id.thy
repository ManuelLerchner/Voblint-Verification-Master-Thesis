theory VIMP_Var_Id
  imports VIMP_Typing VIMP_Proc
begin

section \<open>Static variable identity\<close>

text \<open>
  A name is not an identity. \<^type>\<open>tyenv\<close> answers a kind for a \<^type>\<open>vname\<close>
  program-wide, so two procedures whose formals share a name share a kind, and
  which kind they share depends on the order the declarations were collected in.
  CIL avoids this by giving every global, formal and local its own \<open>varinfo\<close>;
  Goblint's abstract state is then keyed by that record rather than by the text.

  \<open>var_id\<close> is that identity here. Each constructor names the scope its
  binding belongs to, so a name can be bound once per scope without any two
  bindings ever colliding.
\<close>

datatype var_id =
    GlobalId vname
  | ScopedId pname vname
  | ReturnId pname

text \<open>
  \<^const>\<open>ScopedId\<close> covers formals and procedure locals alike -- both are bound
  by one procedure and invisible outside it, and VIMP has no block syntax that
  could distinguish them further.

  The identity carries its source name rather than a positional index. Within a
  scope, uniqueness of the binding is then uniqueness of the name, which needs
  no side condition, and every report can recover a display name from the
  identity alone. The cost is that renaming a variable changes its identity, so
  this is not the declaration-based identity CIL's \<open>vid\<close> provides; positional
  indices become worthwhile at the point VIMP gains block scopes to shadow in.
\<close>

subsection \<open>Scope\<close>

fun var_scope :: "var_id \<Rightarrow> pname option" where
    "var_scope (GlobalId _) = None"
  | "var_scope (ScopedId p _) = Some p"
  | "var_scope (ReturnId p) = Some p"

definition is_global_var :: "var_id \<Rightarrow> bool" where
  "is_global_var v \<longleftrightarrow> var_scope v = None"

lemma is_global_var_simps [simp]:
  "is_global_var (GlobalId x)"
  "\<not> is_global_var (ScopedId p x)"
  "\<not> is_global_var (ReturnId p)"
  by (simp_all add: is_global_var_def)

text \<open>
  Globality is a property of the identity, so the classifier that concrete and
  abstract operations currently take as a separate \<^typ>\<open>vname \<Rightarrow> bool\<close>
  parameter becomes derivable. Nothing has to agree with anything for it to be
  right.
\<close>

subsection \<open>Declarations\<close>

datatype decl_origin = SourceGlobal | SourceFormal | SourceLocal | ReturnSlot

record var_info =
  vi_kind :: ikind
  vi_origin :: decl_origin

text \<open>
  \<^type>\<open>var_info\<close> records no name: the identity already carries it, and a
  second copy would only create an obligation to keep the two in step.
\<close>

type_synonym decl_table = "var_id \<rightharpoonup> var_info"

definition kind_of_var :: "decl_table \<Rightarrow> var_id \<Rightarrow> ikind option" where
  "kind_of_var \<Delta> v = map_option vi_kind (\<Delta> v)"

lemma kind_of_var_None [simp]: "\<Delta> v = None \<Longrightarrow> kind_of_var \<Delta> v = None"
  by (simp add: kind_of_var_def)

lemma kind_of_var_Some [simp]:
  "\<Delta> v = Some vi \<Longrightarrow> kind_of_var \<Delta> v = Some (vi_kind vi)"
  by (simp add: kind_of_var_def)

lemma kind_of_var_dom: "(kind_of_var \<Delta> v \<noteq> None) = (v \<in> dom \<Delta>)"
  by (auto simp: kind_of_var_def)

text \<open>
  The lookup is partial and stays partial. An undeclared identity has no kind,
  and no total fallback supplies one -- that fallback is exactly what let an
  undeclared name silently acquire \<open>I32\<close>. Elaboration discharges the option
  once and writes the kind into the typed node, so transfer functions read a
  kind off the expression they are given and never consult a table.
\<close>

subsection \<open>Well-formed declaration tables\<close>

fun origin_fits :: "var_id \<Rightarrow> decl_origin \<Rightarrow> bool" where
    "origin_fits (GlobalId _) o' = (o' = SourceGlobal)"
  | "origin_fits (ScopedId _ _) o' = (o' = SourceFormal \<or> o' = SourceLocal)"
  | "origin_fits (ReturnId _) o' = (o' = ReturnSlot)"

definition wf_decls :: "decl_table \<Rightarrow> bool" where
  "wf_decls \<Delta> \<longleftrightarrow> (\<forall>v vi. \<Delta> v = Some vi \<longrightarrow> origin_fits v (vi_origin vi))"

lemma wf_declsD:
  "wf_decls \<Delta> \<Longrightarrow> \<Delta> v = Some vi \<Longrightarrow> origin_fits v (vi_origin vi)"
  by (simp add: wf_decls_def)

lemma wf_decls_empty [simp]: "wf_decls Map.empty"
  by (simp add: wf_decls_def)

text \<open>
  Duplicate bindings need no clause. A table is a map keyed by identity, and a
  name-carrying identity makes "one binding per name per scope" hold by
  construction; a positional identity would need an injectivity side condition
  here instead.

  What remains is that an entry's recorded origin matches the shape of the
  identity it is filed under, so a global cannot be filed as a formal or the
  return slot as a local.
\<close>

subsection \<open>Return slots\<close>

text \<open>
  The return slot is per procedure, not one reserved name shared by all of them:
  procedures return different kinds, and a single slot would have to hold all of
  them at once. Recursive activations still share one static identity and are
  separated by the frame they run in, exactly as ordinary locals are.

  Because \<^const>\<open>ReturnId\<close> is a constructor rather than a spelling, no source
  program can name it, and the side condition asserting that the reserved name
  is not global has nothing left to exclude.
\<close>

definition ret_kind_of :: "decl_table \<Rightarrow> pname \<Rightarrow> ikind option" where
  "ret_kind_of \<Delta> p = kind_of_var \<Delta> (ReturnId p)"

lemma ret_kind_of_dom: "(ret_kind_of \<Delta> p \<noteq> None) = (ReturnId p \<in> dom \<Delta>)"
  unfolding ret_kind_of_def by (rule kind_of_var_dom)

subsection \<open>Representing an identity as a name\<close>

text \<open>
  The identity is what the typed core reasons about; a \<^type>\<open>vname\<close> is how it
  is stored. Every store, abstract state and solver unknown is keyed by
  \<^type>\<open>vname\<close>, and an identity carries exactly a scope and a name, so it can
  be injected into that key space instead of replacing it.

  \<open>#\<close> is what makes the injection safe: the lexer's identifier class is
  \<open>[a-zA-Z_][a-zA-Z_0-9]*\<close>, so no source program can write a name containing
  one. The reserved return slot \<^const>\<open>ret_var\<close> already relies on that.
  Globals keep their own name -- they are unique program-wide already -- so an
  unscoped program is represented exactly as it is today.
\<close>

definition var_sep :: string where "var_sep = ''#''"

fun var_id_name :: "var_id \<Rightarrow> vname" where
    "var_id_name (GlobalId x) = x"
  | "var_id_name (ScopedId p x) =
       String.implode (String.explode p @ var_sep @ String.explode x)"
  | "var_id_name (ReturnId p) =
       String.implode (String.explode p @ var_sep @ var_sep @ ''ret'')"

text \<open>
  \<^const>\<open>var_id_name\<close> is injective on identities whose scope and name are
  themselves separator-free, which is every identity a resolver builds from
  source. \<open>ScopedId p x\<close> and \<open>ReturnId p\<close> stay apart because the return slot
  doubles the separator and \<open>x\<close> cannot begin with one.
\<close>

definition sep_free_chars :: "string \<Rightarrow> bool" where
  "sep_free_chars cs \<longleftrightarrow> CHR ''#'' \<notin> set cs"

definition sep_free :: "vname \<Rightarrow> bool" where
  "sep_free x \<longleftrightarrow> sep_free_chars (String.explode x)"

definition var_id_sep_free :: "var_id \<Rightarrow> bool" where
  "var_id_sep_free v \<longleftrightarrow>
     (case v of GlobalId x \<Rightarrow> sep_free x
      | ScopedId p x \<Rightarrow> sep_free p \<and> sep_free x
      | ReturnId p \<Rightarrow> sep_free p)"

text \<open>
  Injectivity is established by a decoder rather than by comparing encodings:
  a left inverse gives it immediately, and reporting needs the decoder anyway
  to recover a display name from a stored key.
\<close>

definition not_sep :: "char \<Rightarrow> bool" where
  "not_sep c \<longleftrightarrow> c \<noteq> CHR ''#''"

text \<open>
  \<^type>\<open>String.literal\<close> is a type of ASCII character lists, so re-encoding a
  name's characters through \<^const>\<open>String.implode\<close> leaves them alone. Without
  this the \<^const>\<open>String.ascii_of\<close> that \<^const>\<open>String.implode\<close> introduces
  blocks every rewrite below.
\<close>

lemma map_ascii_of_explode [simp]:
  "map String.ascii_of (String.explode s) = String.explode s"
  by (metis String.explode_implode_eq String.implode_explode_eq)

lemma takeWhile_not_sep_append:
  "sep_free_chars cs \<Longrightarrow> takeWhile not_sep (cs @ CHR ''#'' # rest) = cs"
  by (induct cs) (auto simp: sep_free_chars_def not_sep_def)

lemma dropWhile_not_sep_append:
  "sep_free_chars cs \<Longrightarrow> dropWhile not_sep (cs @ CHR ''#'' # rest) = CHR ''#'' # rest"
  by (induct cs) (auto simp: sep_free_chars_def not_sep_def)

fun decode_chars :: "string \<Rightarrow> var_id" where
  "decode_chars cs =
     (let owner = takeWhile not_sep cs; rest = dropWhile not_sep cs
      in if rest = [] then GlobalId (String.implode cs)
         else if tl rest = CHR ''#'' # ''ret'' then ReturnId (String.implode owner)
         else ScopedId (String.implode owner) (String.implode (tl rest)))"

definition name_var_id :: "vname \<Rightarrow> var_id" where
  "name_var_id x = decode_chars (String.explode x)"

lemma name_var_id_var_id_name:
  assumes "var_id_sep_free v"
  shows "name_var_id (var_id_name v) = v"
  using assms
proof (cases v)
  case (GlobalId x)
  then show ?thesis using assms
    by (auto simp: Let_def name_var_id_def var_id_sep_free_def sep_free_def sep_free_chars_def
                   not_sep_def takeWhile_eq_all_conv String.implode_explode_eq)
next
  case (ScopedId p x)
  then show ?thesis using assms
    by (auto simp: Let_def name_var_id_def var_sep_def var_id_sep_free_def sep_free_def
                   sep_free_chars_def takeWhile_not_sep_append dropWhile_not_sep_append
                   String.implode_explode_eq)
next
  case (ReturnId p)
  then show ?thesis using assms
    by (auto simp: Let_def name_var_id_def var_sep_def var_id_sep_free_def sep_free_def
                   sep_free_chars_def takeWhile_not_sep_append dropWhile_not_sep_append
                   String.implode_explode_eq)
qed

lemma var_id_name_inj:
  assumes "var_id_sep_free v" "var_id_sep_free w" "var_id_name v = var_id_name w"
  shows "v = w"
  by (metis assms name_var_id_var_id_name)

end
