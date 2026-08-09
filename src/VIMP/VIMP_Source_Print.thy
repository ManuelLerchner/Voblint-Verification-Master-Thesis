theory VIMP_Source_Print
  imports VIMP_Proc "HOL-Library.Char_ord"
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
  No wrapping parens on \<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close>: unlike \<open>bexp\<close>, VIMP's source
  grammar has no parenthesized \<open>aexp\<close> form at all (\<open>VIMP_Notation.thy\<close>'s
  \<open>imp2_aexp\<close> productions never declare one), so a parenthesized rendering
  here would print text this analyzer's own parsers cannot read back --
  actively misleading for a "this is what the source looks like" printer.
  Precedence is exactly \<open>*\<close> tighter than \<open>+\<close>/\<open>-\<close>, both left-associative
  (\<open>VIMP_Notation.thy\<close>'s \<open>_ + _ [65,66] 65\<close> / \<open>_ * _ [70,71] 70\<close>), so this
  prints correctly for any \<open>aexp\<close> actually reachable by parsing source text.
  A tree built some other way (e.g. \<open>Times (Plus a b) c\<close>, not obtainable
  from any concrete VIMP source, since nothing can demote a \<open>Plus\<close> back
  under a \<open>*\<close> without parens) still prints as *some* string, just not one
  that means the same tree back -- an inherent limit of the source grammar
  itself, not a printer defect.
\<close>

fun string_of_aexp :: "aexp \<Rightarrow> string" where
  "string_of_aexp (N n) = string_of_int n"
| "string_of_aexp (V x) = String.explode x"
| "string_of_aexp (Plus a b) = string_of_aexp a @ ''+'' @ string_of_aexp b"
| "string_of_aexp (Minus a b) = string_of_aexp a @ ''-'' @ string_of_aexp b"
| "string_of_aexp (Times a b) = string_of_aexp a @ ''*'' @ string_of_aexp b"

fun string_of_bexp :: "bexp \<Rightarrow> string" where
  "string_of_bexp (Bc True) = ''true''"
| "string_of_bexp (Bc False) = ''false''"
| "string_of_bexp (Not b) = ''!('' @ string_of_bexp b @ '')''"
| "string_of_bexp (And b1 b2) =
    ''('' @ string_of_bexp b1 @ ''&&'' @ string_of_bexp b2 @ '')''"
| "string_of_bexp (Or b1 b2) =
    ''('' @ string_of_bexp b1 @ ''||'' @ string_of_bexp b2 @ '')''"
| "string_of_bexp (Less a1 a2) =
    string_of_aexp a1 @ ''<'' @ string_of_aexp a2"
| "string_of_bexp (Eq a1 a2) =
    string_of_aexp a1 @ ''=='' @ string_of_aexp a2"

definition source_nl :: string where "source_nl = [CHR 0x0A]"

fun join_source :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "join_source sep [] = []"
| "join_source sep [s] = s"
| "join_source sep (s # ss) = s @ sep @ join_source sep ss"

fun string_of_com :: "com \<Rightarrow> string" where
  "string_of_com SKIP = ''skip''"
| "string_of_com (Assign x e) = String.explode x @ '' := '' @ string_of_aexp e"
| "string_of_com (Random x) = String.explode x @ '' := random()''"
| "string_of_com (VIMP_Proc.com.Check c) = ''__voblint_check('' @ string_of_bexp c @ '')''"
| "string_of_com (Seq c1 c2) =
    string_of_com c1 @ '';'' @ source_nl @ string_of_com c2"
| "string_of_com (If b c1 c2) =
    ''if ('' @ string_of_bexp b @ '') { '' @ string_of_com c1
    @ '' } else { '' @ string_of_com c2 @ '' }''"
| "string_of_com (While b c) =
    ''while ('' @ string_of_bexp b @ '') { '' @ string_of_com c @ '' }''"
| "string_of_com (Call dst p es) =
    (case dst of
      None \<Rightarrow> String.explode p @ ''('' @ join_source '', '' (map string_of_aexp es) @ '')''
    | Some x \<Rightarrow> String.explode x @ '' := '' @ String.explode p @ ''(''
        @ join_source '', '' (map string_of_aexp es) @ '')'')"
| "string_of_com (Return (Some e)) = ''return '' @ string_of_aexp e"
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
    [source_indent n @ String.explode x @ '' := '' @ string_of_aexp e]"
| "pretty_source_lines_com n (Random x) =
    [source_indent n @ String.explode x @ '' := random()'']"
| "pretty_source_lines_com n (VIMP_Proc.com.Check c) =
    [source_indent n @ ''__voblint_check('' @ string_of_bexp c @ '')'']"
| "pretty_source_lines_com n (Seq c1 c2) =
    append_last '';'' (pretty_source_lines_com n c1) @ pretty_source_lines_com n c2"
| "pretty_source_lines_com n (If b c1 c2) =
    [source_indent n @ ''if ('' @ string_of_bexp b @ '') {'']
    @ pretty_source_lines_com (n + 2) c1
    @ [source_indent n @ ''} else {'']
    @ pretty_source_lines_com (n + 2) c2
    @ [source_indent n @ ''}'']"
| "pretty_source_lines_com n (While b c) =
    [source_indent n @ ''while ('' @ string_of_bexp b @ '') {'']
    @ pretty_source_lines_com (n + 2) c
    @ [source_indent n @ ''}'']"
| "pretty_source_lines_com n (Call dst p es) =
    [source_indent n @ string_of_com (Call dst p es)]"
| "pretty_source_lines_com n (Return e) =
    [source_indent n @ string_of_com (Return e)]"
| "pretty_source_lines_com n Restore = [source_indent n @ ''restore'']"
| "pretty_source_lines_com n Unwind = [source_indent n @ ''<unwind>'']"

definition pretty_source_lines_proc :: "nat \<Rightarrow> pname \<Rightarrow> proc_decl \<Rightarrow> string list" where
  "pretty_source_lines_proc n p decl =
    (source_indent n @ ''void '' @ String.explode p @ ''('' @ join_source '', '' (map String.explode (formals decl)) @ '') {'')
    # pretty_source_lines_com (n + 2) (body decl)
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
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> vname list \<Rightarrow> string" where
  "pretty_string_of_program \<Pi> ps main globals =
    join_source source_nl
      ((if globals = [] then []
        else [''global '' @ join_source '', '' (map String.explode globals) @ '';''])
      @ concat (map (\<lambda>p. case \<Pi> p of
          None \<Rightarrow> [''procedure '' @ String.explode p @ '' <missing>'']
        | Some decl \<Rightarrow> pretty_source_lines_proc 0 p decl) ps)
      @ [''void main() {''] @ pretty_source_lines_com 2 main @ [''}''])"

end
