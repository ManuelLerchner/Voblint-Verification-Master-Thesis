theory VIMP_Source_Print
  imports VIMP_Proc "HOL-Library.Char_ord"
begin

section \<open>Printing a program back as source text\<close>

text \<open>
  Turns an \<^type>\<open>com\<close> back into the concrete syntax it was parsed from, executably, so a
  check report can quote the line it is talking about.  Nothing is proved about the result
  --- it is a display function, not the inverse of parsing, and no soundness statement
  depends on it.
\<close>

fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n =
     (if n < 10 then [char_of (n + 48)]
      else string_of_nat (n div 10) @ [char_of (n mod 10 + 48)])"

definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i =
     (if i < 0 then ''-'' @ string_of_nat (nat (- i))
      else string_of_nat (nat i))"

text \<open>\<open>exp_prio\<close> mirrors the grammar's mixfix priorities level for level, so
  \<open>string_of_exp\<close> parenthesizes a subexpression exactly when its constructor
  binds looser than the calling position requires. Every tree obtainable from
  source text reparses to itself; a tree built another way still prints, just
  not necessarily tightest.\<close>

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
         | V x \<Rightarrow> String.explode x
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
| "string_of_com (Assign x e) = String.explode x @ '' := '' @ string_of_exp 0 e"
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
    | Some x \<Rightarrow> String.explode x @ '' := '' @ String.explode p @ ''(''
        @ join_source '', '' (map (string_of_exp 0) es) @ '')'')"
| "string_of_com (Return (Some e)) = ''return '' @ string_of_exp 0 e"
| "string_of_com (Return None) = ''return''"
| "string_of_com Restore = ''restore''"
| "string_of_com Unwind = ''<unwind>''"

fun source_indent :: "nat \<Rightarrow> string" where
  "source_indent 0 = []"
| "source_indent (Suc n) = ''  '' @ source_indent n"

text \<open>The \<open>;\<close> separator goes on the last rendered line of the first statement,
  since a block statement spans several lines.\<close>
fun append_last :: "string \<Rightarrow> string list \<Rightarrow> string list" where
  "append_last suffix [] = []"
| "append_last suffix [s] = [s @ suffix]"
| "append_last suffix (s # ss) = s # append_last suffix ss"

fun pretty_source_lines_com :: "nat \<Rightarrow> com \<Rightarrow> string list" where
  "pretty_source_lines_com n SKIP = [source_indent n @ ''skip'']"
| "pretty_source_lines_com n (Assign x e) =
    [source_indent n @ String.explode x @ '' := '' @ string_of_exp 0 e]"
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

definition pretty_source_lines_proc :: "nat \<Rightarrow> pname \<Rightarrow> proc_decl \<Rightarrow> string list" where
  "pretty_source_lines_proc n p decl =
    (source_indent n @ ''void '' @ String.explode p @ ''(''
       @ join_source '', '' (map String.explode (formals decl)) @ '') {'')
    # pretty_source_lines_com (n + 2) (body decl)
    @ [source_indent n @ ''}'']"

text \<open>Canonical concrete syntax: no \<open>program { ... }\<close> wrapper, and no
  \<open>global\<close> line when \<open>globals\<close> is empty.\<close>
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

