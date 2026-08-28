theory VIMP_Source_Print
  imports VIMP_Var_Id "HOL-Library.Char_ord"
begin

text \<open>Executable source rendering for VIMP commands and procedure tables.\<close>

fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n =
     (if n < 10 then [char_of (n + 48)]
      else string_of_nat (n div 10) @ [char_of (n mod 10 + 48)])"

definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i =
     (if i < 0 then ''-'' @ string_of_nat (nat (- i))
      else string_of_nat (nat i))"

text \<open>
  \<open>exp_prio\<close> mirrors \<open>VIMP_Grammar_Generated\<close>'s own generated mixfix
  priorities level for level (\<open>Or\<close> loosest, \<open>Times\<close>/\<open>Not\<close>
  tightest), so \<open>string_of_exp\<close> parenthesizes a suexpression exactly when
  its own constructor binds looser than the calling position requires. The
  printed text reparses to the same tree for any \<open>exp\<close> actually reachable
  by parsing source text -- arithmetic, comparison, and logical operators
  alike, sharing the one grammar. A tree built some other way (e.g.
  \<open>Times (Plus a b) c\<close>, not obtainable from concrete VIMP source, since
  nothing can demote a \<open>Plus\<close> back under a \<open>*\<close> without parens) still prints
  as *some* string, just not necessarily the tightest one -- an inherent
  limit of the source grammar itself, not a printer defect.
\<close>

fun exp_prio :: "exp \<Rightarrow> nat" where
  "exp_prio (N _) = 1000"
| "exp_prio (V _) = 1000"
| "exp_prio (Not _) = 80"
| "exp_prio (Times _ _) = 70"
| "exp_prio (Plus _ _) = 60"
| "exp_prio (Minus _ _) = 60"
| "exp_prio (Less _ _) = 50"
| "exp_prio (Eq _ _) = 50"
| "exp_prio (And _ _) = 40"
| "exp_prio (Or _ _) = 30"

fun string_of_exp :: "nat \<Rightarrow> exp \<Rightarrow> string" where
  "string_of_exp min_prio e =
     (let body =
        (case e of
           N n \<Rightarrow> string_of_int n
         | V x \<Rightarrow> String.explode (display_scoped x)
         | Plus a b \<Rightarrow> string_of_exp 60 a @ ''+'' @ string_of_exp 61 b
         | Minus a b \<Rightarrow> string_of_exp 60 a @ ''-'' @ string_of_exp 61 b
         | Times a b \<Rightarrow> string_of_exp 70 a @ ''*'' @ string_of_exp 71 b
         | Less a b \<Rightarrow> string_of_exp 51 a @ ''<'' @ string_of_exp 51 b
         | Eq a b \<Rightarrow> string_of_exp 51 a @ ''=='' @ string_of_exp 51 b
         | Not a \<Rightarrow> ''!'' @ string_of_exp 80 a
         | And a b \<Rightarrow> string_of_exp 40 a @ ''&&'' @ string_of_exp 41 b
         | Or a b \<Rightarrow> string_of_exp 30 a @ ''||'' @ string_of_exp 31 b)
      in if exp_prio e < min_prio then ''('' @ body @ '')'' else body)"

definition source_nl :: string where "source_nl = [CHR 0x0A]"

fun join_source :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "join_source sep [] = []"
| "join_source sep [s] = s"
| "join_source sep (s # ss) = s @ sep @ join_source sep ss"

fun string_of_com :: "com \<Rightarrow> string" where
  "string_of_com SKIP = ''skip''"
| "string_of_com (Assign x e) =
    String.explode (display_scoped x) @ '' := '' @ string_of_exp 0 e"
| "string_of_com (VIMP_Proc.com.Check c) = ''__voblint_check('' @ string_of_exp 0 c @ '')''"
| "string_of_com (Seq c1 c2) =
    string_of_com c1 @ '';'' @ source_nl @ string_of_com c2"
| "string_of_com (If b c1 c2) =
    ''if ('' @ string_of_exp 0 b @ '') { '' @ string_of_com c1
    @ '' } else { '' @ string_of_com c2 @ '' }''"
| "string_of_com (While b c) =
    ''while ('' @ string_of_exp 0 b @ '') { '' @ string_of_com c @ '' }''"
| "string_of_com (Call dst p es) =
    (case dst of
      None \<Rightarrow> String.explode p @ ''('' @ join_source '', '' (map (string_of_exp 0) es) @ '')''
    | Some x \<Rightarrow> String.explode (display_scoped x) @ '' := '' @ String.explode p @ ''(''
        @ join_source '', '' (map (string_of_exp 0) es) @ '')'')"
| "string_of_com (Return (Some e)) = ''return '' @ string_of_exp 0 e"
| "string_of_com (Return None) = ''return''"
| "string_of_com Restore = ''restore''"
| "string_of_com Unwind = ''<unwind>''"



fun source_indent :: "nat \<Rightarrow> string" where
  "source_indent 0 = []"
| "source_indent (Suc n) = ''  '' @ source_indent n"

text \<open>\<open>append_last\<close> puts the \<open>;\<close> VIMP's grammar requires between sequential
  statements onto the final rendered line of the first, rather than between
  every line unconditionally -- a multi-line \<open>if\<close>/\<open>while\<close> block's closing
  \<open>}\<close> is one rendered "statement" spanning several list entries, and only
  its last line is where the following statement's separator belongs.\<close>

fun append_last :: "string \<Rightarrow> string list \<Rightarrow> string list" where
  "append_last suffix [] = []"
| "append_last suffix [s] = [s @ suffix]"
| "append_last suffix (s # ss) = s # append_last suffix ss"

fun pretty_source_lines_com :: "nat \<Rightarrow> com \<Rightarrow> string list" where
  "pretty_source_lines_com n SKIP = [source_indent n @ ''skip'']"
| "pretty_source_lines_com n (Assign x e) =
    [source_indent n @ String.explode (display_scoped x) @ '' := '' @ string_of_exp 0 e]"
| "pretty_source_lines_com n (VIMP_Proc.com.Check c) =
    [source_indent n @ ''__voblint_check('' @ string_of_exp 0 c @ '')'']"
| "pretty_source_lines_com n (Seq c1 c2) =
    append_last '';'' (pretty_source_lines_com n c1) @ pretty_source_lines_com n c2"
| "pretty_source_lines_com n (If b c1 c2) =
    [source_indent n @ ''if ('' @ string_of_exp 0 b @ '') {'']
    @ pretty_source_lines_com (n + 2) c1
    @ [source_indent n @ ''} else {'']
    @ pretty_source_lines_com (n + 2) c2
    @ [source_indent n @ ''}'']"
| "pretty_source_lines_com n (While b c) =
    [source_indent n @ ''while ('' @ string_of_exp 0 b @ '') {'']
    @ pretty_source_lines_com (n + 2) c
    @ [source_indent n @ ''}'']"
| "pretty_source_lines_com n (Call dst p es) =
    [source_indent n @ string_of_com (Call dst p es)]"
| "pretty_source_lines_com n (Return e) =
    [source_indent n @ string_of_com (Return e)]"
| "pretty_source_lines_com n Restore = [source_indent n @ ''restore'']"
| "pretty_source_lines_com n Unwind = [source_indent n @ ''<unwind>'']"

subsection \<open>Printing declarations\<close>

text \<open>
  The printed form is the strict syntax the frontend accepts, which means
  every declaration carries its kind: a global, a formal, a procedure's return
  and each procedure-local. Printing any of them bare produced source the
  parser rejects, so what came out was not a program the language has.
\<close>

fun string_of_ikind :: "ikind \<Rightarrow> string" where
    "string_of_ikind I8 = ''int8''"   | "string_of_ikind U8 = ''uint8''"
  | "string_of_ikind I16 = ''int16''" | "string_of_ikind U16 = ''uint16''"
  | "string_of_ikind I32 = ''int32''" | "string_of_ikind U32 = ''uint32''"
  | "string_of_ikind I64 = ''int64''" | "string_of_ikind U64 = ''uint64''"

definition string_of_ret_kind :: "ikind option \<Rightarrow> string" where
  "string_of_ret_kind rk = (case rk of None \<Rightarrow> ''void'' | Some k \<Rightarrow> string_of_ikind k)"

text \<open>
  A name is looked up as it is stored and printed as \<^const>\<open>display_scoped\<close>
  shows it. The two differ once the program has been resolved: the kind belongs
  to the identity, while the source wrote the bare name.
\<close>

definition string_of_typed_name :: "tyenv \<Rightarrow> vname \<Rightarrow> string" where
  "string_of_typed_name \<Gamma> x =
     string_of_ikind (\<Gamma> x) @ '' '' @ String.explode (display_scoped x)"

text \<open>
  One declaration line per name rather than one line listing several. A line
  carries a single kind, so grouping would have to partition by kind first;
  one name per line says the same thing and reads the same after a reparse.
\<close>

text \<open>
  A procedure's scoped declarations cover its annotated formals as well as its
  locals. The formals are already printed in the signature, so the declaration
  prologue drops them: printing a formal a second time as a local would give a
  program the parser rejects for declaring a formal as a local.
\<close>

text \<open>
  Every name printed here goes through \<^const>\<open>display_scoped\<close>, so a resolved
  program prints as the source that produced it. On a name no resolver
  produced this is the identity, so an unresolved program prints exactly as it
  always did.
\<close>

definition pretty_local_lines ::
  "nat \<Rightarrow> (pname \<times> typed_var) list \<Rightarrow> vname list \<Rightarrow> pname \<Rightarrow> string list" where
  "pretty_local_lines n scoped fs p =
    map (\<lambda>tv. source_indent n @ string_of_ikind (tv_kind tv) @ '' ''
                @ String.explode (display_scoped (tv_name tv)) @ '';'')
        (filter (\<lambda>tv. tv_name tv \<notin> set fs)
          (map snd (filter (\<lambda>e. fst e = p) scoped)))"

definition pretty_source_lines_proc ::
  "tyenv \<Rightarrow> (pname \<times> typed_var) list \<Rightarrow> nat \<Rightarrow> pname \<Rightarrow> proc_decl \<Rightarrow> string list" where
  "pretty_source_lines_proc \<Gamma> scoped n p decl =
    (source_indent n @ string_of_ret_kind (ret_kind decl) @ '' '' @ String.explode p
       @ ''(''
       @ join_source '', '' (map (string_of_typed_name \<Gamma>) (formals decl))
       @ '') {'')
    # pretty_local_lines (n + 2) scoped (formals decl) p
    @ pretty_source_lines_com (n + 2) (body decl)
    @ [source_indent n @ ''}'']"

text \<open>
  Matches VIMP's canonical concrete syntax exactly: no \<open>program { ... }\<close>
  wrapper (a standalone source file is delimited by its own end, not by an
  enclosing keyword -- see grammar/vimp.yaml), procedures rendered as
  \<open>void NAME(args) { ... }\<close>. \<open>globals\<close> is the program's declared-global
  list; passing \<open>[]\<close> omits the \<open>global ...;\<close> line entirely, matching how
  an unwrapped program with no globals reads.
\<close>

definition pretty_string_of_program ::
  "tyenv \<Rightarrow> (pname \<times> typed_var) list \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> com
    \<Rightarrow> vname list \<Rightarrow> string" where
  "pretty_string_of_program \<Gamma> locals \<Pi> ps main globals =
    join_source source_nl
      (map (\<lambda>g. ''global '' @ string_of_typed_name \<Gamma> g @ '';'') globals
      @ concat (map (\<lambda>p. case \<Pi> p of
          None \<Rightarrow> [''procedure '' @ String.explode p @ '' <missing>'']
        | Some decl \<Rightarrow> pretty_source_lines_proc \<Gamma> locals 0 p decl) ps)
      @ [''void main() {'']
      @ pretty_local_lines 2 locals [] (STR ''main'')
      @ pretty_source_lines_com 2 main @ [''}''])"

end
