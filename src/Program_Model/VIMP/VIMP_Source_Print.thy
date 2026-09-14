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

fun string_of_nat :: "nat \<Rightarrow> String.literal" where
  "string_of_nat n =
     (if n < 10 then String.implode [char_of (n + 48)]
      else string_of_nat (n div 10) + String.implode [char_of (n mod 10 + 48)])"

definition string_of_int :: "int \<Rightarrow> String.literal" where
  "string_of_int i =
     (if i < 0 then STR ''-'' + string_of_nat (nat (- i))
      else string_of_nat (nat i))"

text \<open>\<open>exp_prio\<close> mirrors the grammar's mixfix priorities level for level, so
  \<open>string_of_exp\<close> parenthesizes a subexpression exactly when its constructor
  binds looser than the calling position requires. Every tree obtainable from
  source text reparses to itself; a tree built another way still prints, just
  not necessarily tightest.\<close>

fun exp_prio :: "exp \<Rightarrow> nat" where
  "exp_prio (N _) = 1000"
| "exp_prio (V _) = 1000"
| "exp_prio (Not _) = 90"
| "exp_prio (Times _ _) = 80"
| "exp_prio (Div _ _) = 80"
| "exp_prio (Mod _ _) = 80"
| "exp_prio (Plus _ _) = 70"
| "exp_prio (Minus _ _) = 70"
| "exp_prio (Less _ _) = 60"
| "exp_prio (LessEq _ _) = 60"
| "exp_prio (Greater _ _) = 60"
| "exp_prio (GreaterEq _ _) = 60"
| "exp_prio (NotEq _ _) = 50"
| "exp_prio (Eq _ _) = 50"
| "exp_prio (And _ _) = 40"
| "exp_prio (Or _ _) = 30"

fun string_of_exp :: "nat \<Rightarrow> exp \<Rightarrow> String.literal" where
  "string_of_exp min_prio e =
     (let body =
        (case e of
           N n \<Rightarrow> string_of_int n
         | V x \<Rightarrow> x
         | Plus a b \<Rightarrow> string_of_exp 70 a + STR ''+'' + string_of_exp 71 b
         | Minus a b \<Rightarrow> string_of_exp 70 a + STR ''-'' + string_of_exp 71 b
         | Times a b \<Rightarrow> string_of_exp 80 a + STR ''*'' + string_of_exp 81 b
         | Div a b \<Rightarrow> string_of_exp 80 a + STR ''/'' + string_of_exp 81 b
         | Mod a b \<Rightarrow> string_of_exp 80 a + STR ''%'' + string_of_exp 81 b
         | Less a b \<Rightarrow> string_of_exp 61 a + STR ''<'' + string_of_exp 61 b
         | LessEq a b \<Rightarrow> string_of_exp 61 a + STR ''<='' + string_of_exp 61 b
         | Greater a b \<Rightarrow> string_of_exp 61 a + STR ''>'' + string_of_exp 61 b
         | GreaterEq a b \<Rightarrow> string_of_exp 61 a + STR ''>='' + string_of_exp 61 b
         | NotEq a b \<Rightarrow> string_of_exp 51 a + STR ''!='' + string_of_exp 51 b
         | Eq a b \<Rightarrow> string_of_exp 51 a + STR ''=='' + string_of_exp 51 b
         | Not a \<Rightarrow> STR ''!'' + string_of_exp 90 a
         | And a b \<Rightarrow> string_of_exp 40 a + STR ''&&'' + string_of_exp 41 b
         | Or a b \<Rightarrow> string_of_exp 30 a + STR ''||'' + string_of_exp 31 b)
      in if exp_prio e < min_prio then STR ''('' + body + STR '')'' else body)"

lemma string_of_exp_comparison_precedence:
  "string_of_exp 0 (Eq (N 2) (Less (N 3) (N 4))) = STR ''2==3<4''"
  "string_of_exp 0 (Less (Eq (N 2) (N 3)) (N 4)) = STR ''(2==3)<4''"
  "string_of_exp 0 (NotEq (GreaterEq (N 2) (N 3)) (N 0)) = STR ''2>=3!=0''"
  "string_of_exp 0 (GreaterEq (N 2) (NotEq (N 3) (N 0))) = STR ''2>=(3!=0)''"
  by eval+

definition source_nl :: String.literal where
  "source_nl = String.implode [CHR 0x0A]"

fun join_source :: "String.literal \<Rightarrow> String.literal list \<Rightarrow> String.literal" where
  "join_source sep [] = STR ''''"
| "join_source sep [s] = s"
| "join_source sep (s # ss) = s + sep + join_source sep ss"

fun string_of_com :: "com \<Rightarrow> String.literal" where
  "string_of_com SKIP = STR ''skip;''"
| "string_of_com (Assign x e) =
    x + STR '' = '' + string_of_exp 0 e + STR '';''"
| "string_of_com (VIMP_Proc.com.Check c) =
    STR ''__voblint_check('' + string_of_exp 0 c + STR '');''"
| "string_of_com (Seq c1 c2) =
    string_of_com c1 + source_nl + string_of_com c2"
| "string_of_com (If b c1 c2) =
    STR ''if ('' + string_of_exp 0 b + STR '') { '' + string_of_com c1
    + (if c2 = SKIP
       then STR '' }''
       else STR '' } else { '' + string_of_com c2 + STR '' }'')"
| "string_of_com (While b c) =
    STR ''while ('' + string_of_exp 0 b + STR '') { ''
      + string_of_com c + STR '' }''"
| "string_of_com (Call dst p es) =
    (case dst of
       None \<Rightarrow>
         p + STR ''(''
           + join_source (STR '', '') (map (string_of_exp 0) es)
           + STR '');''
     | Some x \<Rightarrow>
         x + STR '' = '' + p + STR ''(''
           + join_source (STR '', '') (map (string_of_exp 0) es)
           + STR '');'')"
| "string_of_com (Return (Some e)) =
    STR ''return '' + string_of_exp 0 e + STR '';''"
| "string_of_com (Return None) = STR ''return;''"
| "string_of_com Restore = STR ''restore''"
| "string_of_com Unwind = STR ''<unwind>''"

fun source_indent :: "nat \<Rightarrow> String.literal" where
  "source_indent 0 = STR ''''"
| "source_indent (Suc n) = STR ''  '' + source_indent n"

text \<open>Append a suffix to the last line of a rendered fragment.\<close>

fun append_last ::
  "String.literal \<Rightarrow> String.literal list \<Rightarrow> String.literal list" where
  "append_last suffix [] = []"
| "append_last suffix [s] = [s + suffix]"
| "append_last suffix (s # ss) = s # append_last suffix ss"

fun pretty_source_lines_com ::
  "nat \<Rightarrow> com \<Rightarrow> String.literal list" where
  "pretty_source_lines_com n SKIP =
    [source_indent n + STR ''skip;'']"
| "pretty_source_lines_com n (Assign x e) =
    [source_indent n + x + STR '' = '' + string_of_exp 0 e + STR '';'']"
| "pretty_source_lines_com n (VIMP_Proc.com.Check c) =
    [source_indent n + STR ''__voblint_check(''
       + string_of_exp 0 c + STR '');'']"
| "pretty_source_lines_com n (Seq c1 c2) =
    pretty_source_lines_com n c1 @ pretty_source_lines_com n c2"
| "pretty_source_lines_com n (If b c1 c2) =
    [source_indent n + STR ''if ('' + string_of_exp 0 b + STR '') {'']
    @ pretty_source_lines_com (n + 2) c1
    @ (if c2 = SKIP then []
       else
         [source_indent n + STR ''} else {'']
         @ pretty_source_lines_com (n + 2) c2)
    @ [source_indent n + STR ''}'']"
| "pretty_source_lines_com n (While b c) =
    [source_indent n + STR ''while ('' + string_of_exp 0 b + STR '') {'']
    @ pretty_source_lines_com (n + 2) c
    @ [source_indent n + STR ''}'']"
| "pretty_source_lines_com n (Call dst p es) =
    [source_indent n + string_of_com (Call dst p es)]"
| "pretty_source_lines_com n (Return e) =
    [source_indent n + string_of_com (Return e)]"
| "pretty_source_lines_com n Restore =
    [source_indent n + STR ''restore'']"
| "pretty_source_lines_com n Unwind =
    [source_indent n + STR ''<unwind>'']"

definition pretty_source_lines_proc ::
  "nat \<Rightarrow> pname \<Rightarrow> proc_decl \<Rightarrow> String.literal list" where
  "pretty_source_lines_proc n p decl =
    (source_indent n + STR ''fun '' + p + STR ''(''
       + join_source (STR '', '') (formals decl) + STR '') {'')
    # (pretty_source_lines_com (n + 2) (body decl)
       @ [source_indent n + STR ''}''])"

text \<open>Canonical concrete syntax: no \<open>program { ... }\<close> wrapper, and no
  \<open>global\<close> line when \<open>globals\<close> is empty.\<close>

definition pretty_string_of_program ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> vname list \<Rightarrow> String.literal" where
  "pretty_string_of_program \<Pi> ps main globals =
    join_source source_nl
      ((if globals = [] then []
        else
          [STR ''global ''
             + join_source (STR '', '') globals
             + STR '';''])
       @ concat
           (map
             (\<lambda>p. case \<Pi> p of
                None \<Rightarrow> [STR ''procedure '' + p + STR '' <missing>'']
              | Some decl \<Rightarrow> pretty_source_lines_proc 0 p decl)
             ps)
       @ [STR ''fun main() {'']
       @ pretty_source_lines_com 2 main
       @ [STR ''}''])"

end