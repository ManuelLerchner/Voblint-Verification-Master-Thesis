theory IMP2_Source_Print
  imports IMP2_Proc "HOL-Library.Char_ord"
begin

text \<open>Executable source rendering for IMP2 commands and procedure tables.\<close>

fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n =
     (if n < 10 then [char_of (n + 48)]
      else string_of_nat (n div 10) @ [char_of (n mod 10 + 48)])"

definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i =
     (if i < 0 then ''-'' @ string_of_nat (nat (- i))
      else string_of_nat (nat i))"

fun string_of_aexp_hol :: "AExp.aexp \<Rightarrow> string" where
  "string_of_aexp_hol (AExp.N n) = string_of_int n"
| "string_of_aexp_hol (AExp.V x) = x"
| "string_of_aexp_hol (AExp.Plus a b) =
    ''('' @ string_of_aexp_hol a @ ''+'' @ string_of_aexp_hol b @ '')''"

fun string_of_aexp :: "aexp \<Rightarrow> string" where
  "string_of_aexp (BaseN a) = string_of_aexp_hol a"
| "string_of_aexp (Plus a b) =
    ''('' @ string_of_aexp a @ ''+'' @ string_of_aexp b @ '')''"
| "string_of_aexp (Minus a b) =
    ''('' @ string_of_aexp a @ ''-'' @ string_of_aexp b @ '')''"
| "string_of_aexp (Times a b) =
    ''('' @ string_of_aexp a @ ''*'' @ string_of_aexp b @ '')''"

fun string_of_bexp_hol :: "BExp.bexp \<Rightarrow> string" where
  "string_of_bexp_hol (BExp.Bc True) = ''true''"
| "string_of_bexp_hol (BExp.Bc False) = ''false''"
| "string_of_bexp_hol (BExp.Not b) = ''!('' @ string_of_bexp_hol b @ '')''"
| "string_of_bexp_hol (BExp.And b1 b2) =
    ''('' @ string_of_bexp_hol b1 @ ''&&'' @ string_of_bexp_hol b2 @ '')''"
| "string_of_bexp_hol (BExp.Less a1 a2) =
    string_of_aexp_hol a1 @ ''<'' @ string_of_aexp_hol a2"

fun string_of_bexp :: "bexp \<Rightarrow> string" where
  "string_of_bexp (BaseB b) = string_of_bexp_hol b"
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
| "string_of_com (Assign x e) = x @ '' := '' @ string_of_aexp e"
| "string_of_com (Seq c1 c2) =
    string_of_com c1 @ '' ;'' @ source_nl @ string_of_com c2"
| "string_of_com (If b c1 c2) =
    ''if ('' @ string_of_bexp b @ '') then ('' @ string_of_com c1
    @ '') else ('' @ string_of_com c2 @ '')''"
| "string_of_com (While b c) =
    ''while ('' @ string_of_bexp b @ '') do ('' @ string_of_com c @ '')''"
| "string_of_com (Call dst p es) =
    (case dst of
      None \<Rightarrow> p @ ''('' @ join_source '', '' (map string_of_aexp es) @ '')''
    | Some x \<Rightarrow> x @ '' := '' @ p @ ''(''
        @ join_source '', '' (map string_of_aexp es) @ '')'')"
| "string_of_com (Return (Some e)) = ''return '' @ string_of_aexp e"
| "string_of_com (Return None) = ''return''"
| "string_of_com Restore = ''restore''"
| "string_of_com Unwind = ''<unwind>''"

definition string_of_proc_decl :: "pname \<Rightarrow> proc_decl \<Rightarrow> string" where
  "string_of_proc_decl p decl =
    ''procedure '' @ p @ ''('' @ join_source '', '' (formals decl) @ ''):''
    @ source_nl @ string_of_com (body decl)
    @ (case result decl of None \<Rightarrow> [] | Some e \<Rightarrow>
         source_nl @ ''return '' @ string_of_aexp e)"

definition string_of_program ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> string" where
  "string_of_program \<Pi> ps main =
    join_source source_nl (map (\<lambda>p. case \<Pi> p of
      None \<Rightarrow> ''procedure '' @ p @ '' <missing>''
    | Some decl \<Rightarrow> string_of_proc_decl p decl) ps
    @ [''main: '' @ string_of_com main])"


end
