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

fun string_of_aexp :: "aexp \<Rightarrow> string" where
  "string_of_aexp (N n) = string_of_int n"
| "string_of_aexp (V x) = String.explode x"
| "string_of_aexp (Plus a b) =
    ''('' @ string_of_aexp a @ ''+'' @ string_of_aexp b @ '')''"
| "string_of_aexp (Minus a b) =
    ''('' @ string_of_aexp a @ ''-'' @ string_of_aexp b @ '')''"
| "string_of_aexp (Times a b) =
    ''('' @ string_of_aexp a @ ''*'' @ string_of_aexp b @ '')''"

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
    string_of_com c1 @ '' ;'' @ source_nl @ string_of_com c2"
| "string_of_com (If b c1 c2) =
    ''if ('' @ string_of_bexp b @ '') then ('' @ string_of_com c1
    @ '') else ('' @ string_of_com c2 @ '')''"
| "string_of_com (While b c) =
    ''while ('' @ string_of_bexp b @ '') do ('' @ string_of_com c @ '')''"
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

fun pretty_source_lines_com :: "nat \<Rightarrow> com \<Rightarrow> string list" where
  "pretty_source_lines_com n SKIP = [source_indent n @ ''skip'']"
| "pretty_source_lines_com n (Assign x e) =
    [source_indent n @ String.explode x @ '' := '' @ string_of_aexp e]"
| "pretty_source_lines_com n (Random x) =
    [source_indent n @ String.explode x @ '' := random()'']"
| "pretty_source_lines_com n (VIMP_Proc.com.Check c) =
    [source_indent n @ ''__voblint_check('' @ string_of_bexp c @ '')'']"
| "pretty_source_lines_com n (Seq c1 c2) =
    pretty_source_lines_com n c1 @ pretty_source_lines_com n c2"
| "pretty_source_lines_com n (If b c1 c2) =
    [source_indent n @ ''if ('' @ string_of_bexp b @ '') then'']
    @ pretty_source_lines_com (n + 2) c1
    @ [source_indent n @ ''else'']
    @ pretty_source_lines_com (n + 2) c2"
| "pretty_source_lines_com n (While b c) =
    [source_indent n @ ''while ('' @ string_of_bexp b @ '') do'']
    @ pretty_source_lines_com (n + 2) c"
| "pretty_source_lines_com n (Call dst p es) =
    [source_indent n @ string_of_com (Call dst p es)]"
| "pretty_source_lines_com n (Return e) =
    [source_indent n @ string_of_com (Return e)]"
| "pretty_source_lines_com n Restore = [source_indent n @ ''restore'']"
| "pretty_source_lines_com n Unwind = [source_indent n @ ''<unwind>'']"

definition pretty_source_lines_proc :: "pname \<Rightarrow> proc_decl \<Rightarrow> string list" where
  "pretty_source_lines_proc p decl =
    (''procedure '' @ String.explode p @ ''('' @ join_source '', '' (map String.explode (formals decl)) @ ''):'')
    # pretty_source_lines_com 2 (body decl)"

definition pretty_string_of_program ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> string" where
  "pretty_string_of_program \<Pi> ps main =
    join_source source_nl
      (concat (map (\<lambda>p. case \<Pi> p of
        None \<Rightarrow> [''procedure '' @ String.explode p @ '' <missing>'']
      | Some decl \<Rightarrow> pretty_source_lines_proc p decl) ps)
      @ [''main:''] @ pretty_source_lines_com 2 main)"

end
