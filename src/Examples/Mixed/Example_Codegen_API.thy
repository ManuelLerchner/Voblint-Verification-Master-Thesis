theory Example_Codegen_API
  imports Example_Analysis_Dispatch
begin

section \<open>A String.literal program-construction facade\<close>

text \<open>
  \<open>vname\<close>/\<open>pname\<close> are \<^typ>\<open>char list\<close> internally, and
  \<^theory>\<open>HOL-Library.Code_Abstract_Char\<close> makes every \<open>char\<close> in such a list an
  opaque target-native integer (see
  \<^theory>\<open>Voblint_Examples.Example_Analysis_Dispatch\<close>), so an external caller
  building a name by hand would have to construct one \<open>char\<close> at a time via
  \<open>char_of_integer\<close>. \<^typ>\<open>String.literal\<close> is already the target language's
  native string (\<^verbatim>\<open>String\<close> in Haskell, \<^verbatim>\<open>string\<close> in OCaml ---
  \<^theory>\<open>HOL.String\<close> ships that mapping unconditionally, no extra import
  needed), so the functions below take \<^typ>\<open>String.literal\<close> wherever the raw
  constructors below them take a \<^typ>\<open>char list\<close> name, and convert with
  \<^const>\<open>String.explode\<close>. Internal syntax (\<open>imp \<lbrakk> ... \<rbrakk>\<close>, \<open>program { ... }\<close>)
  and every proof keep building \<^typ>\<open>vname\<close>/\<^typ>\<open>pname\<close> directly; this is
  purely an additional outer entry point for callers who only have generated
  code, not a replacement for them.
\<close>

definition api_var :: "String.literal \<Rightarrow> aexp" where
  "api_var x = V (String.explode x)"

definition api_assign :: "String.literal \<Rightarrow> aexp \<Rightarrow> com" where
  "api_assign x a = Assign (String.explode x) a"

definition api_random :: "String.literal \<Rightarrow> com" where
  "api_random x = Random (String.explode x)"

definition api_call ::
  "String.literal option \<Rightarrow> String.literal \<Rightarrow> aexp list \<Rightarrow> com" where
  "api_call dst p args = com.Call (map_option String.explode dst) (String.explode p) args"

text \<open>
  \<open>api_proc\<close> is the only public way to build a \<^typ>\<open>proc_decl\<close> (\<^const>\<open>proc_decl_of\<close>
  is already the general constructor, taking the formals list and the body
  directly; this just converts the formals' names from \<^typ>\<open>String.literal\<close>).
\<close>

definition api_proc :: "String.literal list \<Rightarrow> com \<Rightarrow> proc_decl" where
  "api_proc fs bd = proc_decl_of (map String.explode fs) bd"

definition api_program ::
  "(String.literal \<times> proc_decl) list \<Rightarrow> com \<Rightarrow> String.literal list \<Rightarrow> imp_prog" where
  "api_program procs m globals =
     imp_prog.make (map (\<lambda>(n, d). (String.explode n, d)) procs) m (map String.explode globals)"

subsection \<open>Round-trip check against the internal parser\<close>

text \<open>
  \<open>dispatch_demo_prog\<close> (\<^theory>\<open>Voblint_Examples.Example_Analysis_Dispatch\<close>)
  built via \<open>program { ... }\<close> and the same program rebuilt through the
  facade above are the same \<^typ>\<open>imp_prog\<close> value --- the facade is a
  reshaping of arguments, not a second construction path with independent
  behaviour.
\<close>

lemma api_program_matches_dispatch_demo:
  "api_program []
     (Seq (Seq (Seq (api_assign (STR ''y'') (N 1))
                    (Check (Less (N 0) (V ''y''))))
               (api_assign (STR ''y'') (Minus (N 0) (N 1))))
          (Check (Less (N 0) (V ''y''))))
     []
   = dispatch_demo_prog"
  by eval

subsection \<open>Executable code generation\<close>

text \<open>
  \<open>analyse\<close> genuinely takes the domain choice and the program as runtime
  arguments, not constants baked in at export time. The raw AST constructors
  and \<open>imp_prog.make\<close> stay exported alongside \<open>analyse\<close> and the
  \<^typ>\<open>String.literal\<close> facade above it, so external Haskell/OCaml code can
  build a fresh \<open>imp_prog\<close> either way and hand it to \<open>analyse\<close>.

  \<^theory>\<open>HOL-Library.Code_Target_Numeral\<close> makes \<open>int\<close>/\<open>nat\<close> abstract types
  backed by the target language's native arbitrary-precision integer
  (Haskell's \<open>Integer\<close>, OCaml's target-numeral representation) instead of
  Isabelle's own binary-numeral/Peano-successor encodings, so arithmetic and
  comparisons inside the exported analyser run on native integers rather
  than walking a \<open>Num\<close>/\<open>Nat\<close> term. \<open>int_of_integer\<close>/\<open>nat_of_integer\<close> and
  their inverses \<open>integer_of_int\<close>/\<open>integer_of_nat\<close> are the resulting
  bridge --- the only way external code can build or inspect an \<open>int\<close>/\<open>nat\<close>
  once the representation is opaque.

  \<^theory>\<open>HOL-Library.Code_Abstract_Char\<close> does the same for \<open>char\<close> ---
  relevant because \<^typ>\<open>vname\<close> is \<^typ>\<open>char list\<close>, so every variable
  name and every CFG/map lookup keyed on one compares characters. Locals,
  globals, and procedure names all resolve to native-integer character
  comparisons instead of an 8-bit-vector term walk. \<open>char_of_integer\<close> and
  \<open>integer_of_char\<close> are the resulting bridge; \<open>api_var\<close>/\<open>api_assign\<close>/
  \<open>api_random\<close>/\<open>api_call\<close>/\<open>api_proc\<close>/\<open>api_program\<close> above are the
  \<^typ>\<open>String.literal\<close> alternative that avoids it for callers who only want
  to build a program, not inspect a name character-by-character.
\<close>

export_code
  analyse Sign_Analysis Interval_Analysis
  imp_prog.make
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  api_var api_assign api_random api_call api_proc api_program
  checking Haskell

export_code
  analyse Sign_Analysis Interval_Analysis
  imp_prog.make
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  api_var api_assign api_random api_call api_proc api_program
  in Haskell module_name Voblint_Analyse file_prefix "Voblint_Analyse"

export_code
  analyse Sign_Analysis Interval_Analysis
  imp_prog.make
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  api_var api_assign api_random api_call api_proc api_program

export_code
  analyse Sign_Analysis Interval_Analysis
  imp_prog.make
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  api_var api_assign api_random api_call api_proc api_program
  in OCaml module_name Voblint_Analyse file_prefix "Voblint_Analyse_OCaml"

end
