theory IMP2_Notation
  imports IMP2_Proc
begin

text \<open>
  IMP2 quotation bracket: @{text "\<lbrakk> \<dots> \<rbrakk>"} produces a single
  @{type IMP2_Proc.com} without HOL string quotes or qualified constructor names.
  (The same bracket with procedure declarations produces a whole @{text imp_prog};
  see the whole-program form below.)

  Design is inspired by:
  https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Examples.Basic_Micro_Rust.html
  and 
  https://github.com/awslabs/AutoCorrode/blob/e234addc5e67f78cbff63defd24199578e8e1af3/Micro_Rust_Parsing_Frontend/Micro_Rust_Syntax.thy#L5

  Inside the bracket:
  - bare identifiers become @{const V} literals (HOL string literals via @{type vname})
  - numerals become @{const N}
  - arithmetic:
      +, -, * map to @{const Plus}, @{const Minus}, @{const Times}
  - boolean comparisons:
      <, == map to @{const Less}, @{const Eq}
  - constants:
      true/false map to @{const Bc}

  Example:
  @{verbatim [display]
   "definition loop_prog :: IMP2_Proc.com where
      \"loop_prog = \<lbrakk>
         x := 0;
         while (x < 20) { x := x + 1 }
       \<rbrakk>\""}
\<close>

text \<open>
  Whole-program form.  \<^verbatim>\<open>\<lbrakk> proc f { .. } proc g { .. } main { .. } \<rbrakk>\<close>
  bundles the procedure-name list, the procedure table, and the main command
  into one \<^verbatim>\<open>imp_prog\<close>, ready for
  \<^verbatim>\<open>compile_prog (prog_table p) (prog_procs p) (prog_main p)\<close>.
\<close>

type_synonym imp_prog = "pname list \<times> proc_table \<times> com"

abbreviation prog_procs :: "imp_prog \<Rightarrow> pname list" where "prog_procs p \<equiv> fst p"
abbreviation prog_table :: "imp_prog \<Rightarrow> proc_table" where "prog_table p \<equiv> fst (snd p)"
abbreviation prog_main  :: "imp_prog \<Rightarrow> com"        where "prog_main p \<equiv> snd (snd p)"

nonterminal imp2_com
nonterminal imp2_aexp
nonterminal imp2_bexp
nonterminal imp2_gdecl
nonterminal imp2_ids
nonterminal imp2_funcs

syntax
  "_IMP2"        :: "imp2_com \<Rightarrow> IMP2_Proc.com"              ("\<lbrakk> _ \<rbrakk>")

  "_imp2_skip"   :: imp2_com                                  ("skip")
  "_imp2_assign" :: "id \<Rightarrow> imp2_aexp \<Rightarrow> imp2_com"            ("_ := _"                 [900, 61] 61)
  "_imp2_seq"    :: "imp2_com \<Rightarrow> imp2_com \<Rightarrow> imp2_com"       ("_; _"                   [60, 61] 60)
  "_imp2_if"     :: "imp2_bexp \<Rightarrow> imp2_com \<Rightarrow> imp2_com \<Rightarrow> imp2_com"
                                                               ("if '( _ ') { _ } else { _ }" [0, 0, 61] 61)
  "_imp2_while"  :: "imp2_bexp \<Rightarrow> imp2_com \<Rightarrow> imp2_com"      ("while '( _ ') { _ }"    [0, 61] 61)
  "_imp2_scope"  :: "imp2_com \<Rightarrow> imp2_com"                   ("scope { _ }"            [61] 61)
  "_imp2_call"   :: "id \<Rightarrow> imp2_com"                         ("_'(')"                  [1000] 61)

  "_PROG"        :: "imp2_gdecl \<Rightarrow> imp2_funcs \<Rightarrow> imp_prog"      ("\<lbrakk> _ _ \<rbrakk>")
  "_gdecl_none"  :: imp2_gdecl                                    ("")
  "_gdecl"       :: "imp2_ids \<Rightarrow> imp2_gdecl"                     ("int _ ;")
  "_ids_one"     :: "id \<Rightarrow> imp2_ids"                             ("_")
  "_ids_cons"    :: "id \<Rightarrow> imp2_ids \<Rightarrow> imp2_ids"                ("_ , _")
  "_funcs_nil"   :: imp2_funcs                                    ("")
  "_funcs_cons"  :: "id \<Rightarrow> imp2_com \<Rightarrow> imp2_funcs \<Rightarrow> imp2_funcs"  ("void _'(') { _ } _" [0, 0, 0] 0)

  "_imp2_var"    :: "id \<Rightarrow> imp2_aexp"                        ("_"   1000)
  "_imp2_num"    :: "num_const \<Rightarrow> imp2_aexp"                 ("_"   1000)
  "_imp2_zero"   :: imp2_aexp                                 ("0"   1000)
  "_imp2_one"    :: imp2_aexp                                 ("1"   1000)
  "_imp2_plus"   :: "imp2_aexp \<Rightarrow> imp2_aexp \<Rightarrow> imp2_aexp"   ("_ + _"                  [65, 66] 65)
  "_imp2_minus"  :: "imp2_aexp \<Rightarrow> imp2_aexp \<Rightarrow> imp2_aexp"   ("_ - _"                  [65, 66] 65)
  "_imp2_times"  :: "imp2_aexp \<Rightarrow> imp2_aexp \<Rightarrow> imp2_aexp"   ("_ * _"                  [70, 71] 70)

  "_imp2_true"   :: imp2_bexp                                 ("true")
  "_imp2_false"  :: imp2_bexp                                 ("false")
  "_imp2_less"   :: "imp2_aexp \<Rightarrow> imp2_aexp \<Rightarrow> imp2_bexp"   ("_ < _"                  [50, 51] 50)
  "_imp2_eq"     :: "imp2_aexp \<Rightarrow> imp2_aexp \<Rightarrow> imp2_bexp"   ("_ == _"                 [50, 51] 50)
  "_imp2_not"    :: "imp2_bexp \<Rightarrow> imp2_bexp"                ("! _"                    [90] 90)
  "_imp2_and"    :: "imp2_bexp \<Rightarrow> imp2_bexp \<Rightarrow> imp2_bexp"   ("_ && _"                 [35, 36] 35)
  "_imp2_or"     :: "imp2_bexp \<Rightarrow> imp2_bexp \<Rightarrow> imp2_bexp"   ("_ || _"                 [30, 31] 30)

parse_translation \<open>
  let
    val c_SKIP   = "IMP2_Proc.com.SKIP"
    val c_Assign = "IMP2_Proc.com.Assign"
    val c_Seq    = "IMP2_Proc.com.Seq"
    val c_If     = "IMP2_Proc.com.If"
    val c_While  = "IMP2_Proc.com.While"
    val c_Scope  = "IMP2_Proc.com.Scope"
    val c_Call   = "IMP2_Proc.com.Call"

    val c_N      = "IMP2_Syntax.N"
    val c_V      = "IMP2_Syntax.V"
    val c_Plus   = "IMP2_Syntax.aexp.Plus"
    val c_Minus  = "IMP2_Syntax.aexp.Minus"
    val c_Times  = "IMP2_Syntax.aexp.Times"

    val c_Bc     = "IMP2_Syntax.Bc"
    val c_Less   = "IMP2_Syntax.bexp.Less"
    val c_Eq     = "IMP2_Syntax.bexp.Eq"
    val c_Not    = "IMP2_Syntax.bexp.Not"
    val c_And    = "IMP2_Syntax.bexp.And"
    val c_Or     = "IMP2_Syntax.bexp.Or"

    fun K name = Const (name, dummyT)

    (* Decode Isabelle's Num binary structure: One=1, Bit0 n=2n, Bit1 n=2n+1.
       Leaf may also be a decimal-string Const (e.g. Const("20",_)) from the raw lexer. *)
    fun dest_num (Const (c, _)) =
          let val name = Long_Name.base_name c
          in if name = "One" then 1
             else case Int.fromString name of
                    SOME n => n
                  | NONE => raise TERM ("IMP2_Notation: not a num leaf", [Const (c, dummyT)])
          end
      | dest_num (Const (c, _) $ t) =
          let val name = Long_Name.base_name c
              val n    = dest_num t
          in if name = "Bit0" then 2 * n
             else if name = "Bit1" then 2 * n + 1
             else raise TERM ("IMP2_Notation: not a num constructor", [Const (c, dummyT) $ t])
          end
      | dest_num t =
          let
            fun dbg (Const (s, _)) = "Const[" ^ s ^ "]"
              | dbg (Free (s, _))  = "Free[" ^ s ^ "]"
              | dbg (f $ x) = "App(" ^ dbg f ^ "," ^ dbg x ^ ")"
              | dbg (Abs (s, _, _)) = "Abs[" ^ s ^ "]"
              | dbg (Bound i) = "Bound[" ^ Int.toString i ^ "]"
              | dbg _ = "Other"
          in raise TERM ("IMP2_Notation: dest_num catchall: " ^ dbg t, [t]) end

    fun read_num_const (Const ("_constify", _) $ t) = read_num_const t
      | read_num_const (Const ("_position", _) $ t) = read_num_const t
      | read_num_const ((Const ("_constrain", _) $ t) $ _) = read_num_const t
      | read_num_const (Free (s, _)) =
          (case Int.fromString s of
             SOME n => n
           | NONE => raise TERM ("IMP2_Notation: not a numeral", [Free (s, dummyT)]))
      | read_num_const (Const (s, _)) =
          (case Int.fromString (Long_Name.base_name s) of
             SOME n => n
           | NONE => raise TERM ("IMP2_Notation: not a numeral", [Const (s, dummyT)]))
      | read_num_const t = dest_num t

    fun aexp_tr (Const ("_imp2_var",  _) $ Free (x, _)) =
          K c_V $ HOLogic.mk_string x
      | aexp_tr (Const ("_imp2_zero", _)) = K c_N $ HOLogic.mk_number HOLogic.intT 0
      | aexp_tr (Const ("_imp2_one",  _)) = K c_N $ HOLogic.mk_number HOLogic.intT 1
      | aexp_tr (Const ("_imp2_num",  _) $ n) =
          K c_N $ HOLogic.mk_number HOLogic.intT (read_num_const n)
      | aexp_tr (Const ("_imp2_plus",  _) $ a $ b) = K c_Plus  $ aexp_tr a $ aexp_tr b
      | aexp_tr (Const ("_imp2_minus", _) $ a $ b) = K c_Minus $ aexp_tr a $ aexp_tr b
      | aexp_tr (Const ("_imp2_times", _) $ a $ b) = K c_Times $ aexp_tr a $ aexp_tr b
      | aexp_tr t = raise TERM ("IMP2_Notation: aexp_tr", [t])

    fun bexp_tr (Const ("_imp2_true",  _)) = K c_Bc $ @{term True}
      | bexp_tr (Const ("_imp2_false", _)) = K c_Bc $ @{term False}
      | bexp_tr (Const ("_imp2_less",  _) $ a $ b) = K c_Less $ aexp_tr a $ aexp_tr b
      | bexp_tr (Const ("_imp2_eq",    _) $ a $ b) = K c_Eq   $ aexp_tr a $ aexp_tr b
      | bexp_tr (Const ("_imp2_not",   _) $ b)     = K c_Not  $ bexp_tr b
      | bexp_tr (Const ("_imp2_and",   _) $ a $ b) = K c_And  $ bexp_tr a $ bexp_tr b
      | bexp_tr (Const ("_imp2_or",    _) $ a $ b) = K c_Or   $ bexp_tr a $ bexp_tr b
      | bexp_tr t = raise TERM ("IMP2_Notation: bexp_tr", [t])

    fun com_tr (Const ("_imp2_skip",   _)) = K c_SKIP
      | com_tr (Const ("_imp2_assign", _) $ Free (x, _) $ a) =
          K c_Assign $ HOLogic.mk_string x $ aexp_tr a
      | com_tr (Const ("_imp2_seq",    _) $ c1 $ c2) = K c_Seq   $ com_tr c1 $ com_tr c2
      | com_tr (Const ("_imp2_if",     _) $ b $ c1 $ c2) =
          K c_If $ bexp_tr b $ com_tr c1 $ com_tr c2
      | com_tr (Const ("_imp2_while",  _) $ b $ c) = K c_While $ bexp_tr b $ com_tr c
      | com_tr (Const ("_imp2_scope",  _) $ c)     = K c_Scope $ com_tr c
      | com_tr (Const ("_imp2_call",   _) $ Free (p, _)) =
          K c_Call $ HOLogic.mk_string p
      | com_tr t = raise TERM ("IMP2_Notation: com_tr", [t])

    val c_None    = "Option.option.None"
    val c_Some    = "Option.option.Some"
    val c_fun_upd = "Fun.fun_upd"
    val c_Pair    = "Product_Type.Pair"
    val c_Cons    = "List.list.Cons"
    val c_Nil     = "List.list.Nil"

    fun names_of (Const ("_ids_one", _) $ Free (x, _)) = [x]
      | names_of (Const ("_ids_cons", _) $ Free (x, _) $ rest) = x :: names_of rest
      | names_of t = raise TERM ("IMP2_Notation: names_of", [t])

    fun ids_tr (Const ("_gdecl_none", _)) = []
      | ids_tr (Const ("_gdecl", _) $ ids) = names_of ids
      | ids_tr t = raise TERM ("IMP2_Notation: ids_tr", [t])

    fun funcs_tr (Const ("_funcs_nil", _)) = []
      | funcs_tr (Const ("_funcs_cons", _) $ Free (f, _) $ body $ rest) =
          (f, body) :: funcs_tr rest
      | funcs_tr t = raise TERM ("IMP2_Notation: funcs_tr", [t])

    (* Variable occurrences in a command AST: reads and assignment targets.
       Procedure names under _imp2_call are not store variables, so skip them. *)
    fun add_vars (Const ("_imp2_var", _) $ Free (x, _)) acc = x :: acc
      | add_vars (Const ("_imp2_assign", _) $ Free (x, _) $ a) acc = add_vars a (x :: acc)
      | add_vars (Const ("_imp2_call", _) $ _) acc = acc
      | add_vars (t $ u) acc = add_vars u (add_vars t acc)
      | add_vars (Abs (_, _, b)) acc = add_vars b acc
      | add_vars _ acc = acc

    fun is_gname x = size x > 0 andalso String.sub (x, 0) = #"G"

    fun check_globals decls used =
      let
        val bad = filter_out is_gname decls
        val _ = if null bad then ()
                else error ("IMP2 program: declared global without 'G' prefix: " ^ commas_quote bad)
        val undeclared =
          distinct (op =) (filter_out (member (op =) decls) (filter is_gname used))
        val _ = if null undeclared then ()
                else error ("IMP2 program: global(s) used but not declared: " ^ commas_quote undeclared)
      in () end

    val empty_table = Abs ("_", dummyT, K c_None)

    fun mk_table acc [] = acc
      | mk_table acc ((p, b) :: rest) =
          mk_table (K c_fun_upd $ acc $ HOLogic.mk_string p $ (K c_Some $ b)) rest

    fun mk_names [] = K c_Nil
      | mk_names (n :: ns) = K c_Cons $ HOLogic.mk_string n $ mk_names ns

    (* dummyT constructors only; type inference runs after the translation. *)
    fun prog_tr gdecl_t funcs_t =
      let
        val decls = ids_tr gdecl_t
        val funcs = funcs_tr funcs_t
        val _ = check_globals decls (fold (fn (_, b) => add_vars b) funcs [])
        val (mains, procs) = List.partition (fn (n, _) => n = "main") funcs
        val main_ast =
          (case mains of
             [(_, b)] => b
           | [] => error "IMP2 program: missing 'void main() { ... }'"
           | _  => error "IMP2 program: more than one 'void main()'")
        val names = mk_names (map fst procs)
        val table = mk_table empty_table (map (fn (n, b) => (n, com_tr b)) procs)
        val main  = com_tr main_ast
      in K c_Pair $ names $ (K c_Pair $ table $ main) end
  in
    [("_IMP2", fn _ => fn [t] => com_tr t | _ => raise Match),
     ("_PROG", fn _ => fn [g, fs] => prog_tr g fs | _ => raise Match)]
  end
\<close>

subsection \<open>Executable examples\<close>

value "\<lbrakk> x := 0 \<rbrakk>"
value "\<lbrakk> x := 0; y := 1 \<rbrakk>"
value "\<lbrakk> if (x < 10) { x := 0 } else { x := 1 } \<rbrakk>"
value "\<lbrakk> while (x < 10) { x := x + 1 } \<rbrakk>"

end
