theory IMP2_Notation
  imports IMP2_Proc
begin

text \<open>
  IMP2 command quotation: @{text "imp \<lbrakk> \<dots> \<rbrakk>"} produces a single
  @{type IMP2_Proc.com} without HOL string quotes or qualified constructor names.
  The @{verbatim "imp"} keyword keeps the bracket distinct from Pure's premise
  brackets. The whole-program form uses an explicit @{verbatim "program"} prefix;
  see the whole-program form below.

  Design is inspired by:
  https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Examples.Basic_Micro_Rust.html
  and 
  https://github.com/awslabs/AutoCorrode/blob/e234addc5e67f78cbff63defd24199578e8e1af3/Micro_Rust_Parsing_Frontend/Micro_Rust_Syntax.thy#L5

  Inside the bracket:
  - bare identifiers become @{const V} literals (HOL string literals via @{type vname})
  - numerals become @{const N}
  - arithmetic:
      +, -, * map to @{const Plus}, @{const Minus}, @{const Times}
      unary minus @{text "-n"} on numerals becomes @{const N} with a negative int
  - boolean comparisons:
      <, == map to @{const Less}, @{const Eq}
  - constants:
      true/false map to @{const Bc}

  Example:
  @{verbatim [display]
   "definition loop_prog :: IMP2_Proc.com where
      \"loop_prog = imp \<lbrakk>
         x := 0;
         while (x < 20) { x := x + 1 }
       \<rbrakk>\""}
\<close>

text \<open>
  Whole-program form.  \<^verbatim>\<open>program { void f(..) { .. } void main() { .. } }\<close>
  bundles the procedure-name list, the procedure table, and the main command
  into one \<^verbatim>\<open>imp_prog\<close> record, ready for
  \<^verbatim>\<open>compile_prog (prog_table p) (prog_procs p) (prog_main p)\<close>.
\<close>

record imp_prog =
  prog_procs :: "pname list"
  prog_table :: proc_table
  prog_main  :: com

lemma prog_procs_make [simp]: "prog_procs (imp_prog.make ps pi m) = ps"
  and prog_table_make [simp]: "prog_table (imp_prog.make ps pi m) = pi"
  and prog_main_make  [simp]: "prog_main  (imp_prog.make ps pi m) = m"
  by (simp_all add: imp_prog.make_def)

nonterminal imp2_com
nonterminal imp2_stmt
nonterminal imp2_stmts
nonterminal imp2_aexp
nonterminal imp2_bexp
nonterminal imp2_gdecl
nonterminal imp2_ids
nonterminal imp2_actuals
nonterminal imp2_formals
nonterminal imp2_pbody
nonterminal imp2_funcs

syntax
  "_IMP2"        :: "imp2_com \<Rightarrow> IMP2_Proc.com"              ("imp \<lbrakk> _ \<rbrakk>")

  "_imp2_skip"   :: imp2_stmt                                  ("skip")
  "_imp2_assign" :: "id \<Rightarrow> imp2_aexp \<Rightarrow> imp2_stmt"            ("_ := _"                 [900, 61] 61)
  "_imp2_if"     :: "imp2_bexp \<Rightarrow> imp2_stmts \<Rightarrow> imp2_stmts \<Rightarrow> imp2_stmt"
                                                               ("if '( _ ') { _ } else { _ }" [0, 61, 61] 61)
  "_imp2_while"  :: "imp2_bexp \<Rightarrow> imp2_stmts \<Rightarrow> imp2_stmt"      ("while '( _ ') { _ }"    [0, 61] 61)
  "_imp2_call0"  :: "id \<Rightarrow> imp2_stmt"                           ("_'(')"                  [1000] 61)
  "_imp2_call"   :: "id \<Rightarrow> imp2_actuals \<Rightarrow> imp2_stmt"         ("_'( _ ')"               [1000, 0] 61)
  "_imp2_callret0" :: "id \<Rightarrow> id \<Rightarrow> imp2_stmt"              ("_ := _'(')"              [900, 1000] 61)
  "_imp2_callret" :: "id \<Rightarrow> id \<Rightarrow> imp2_actuals \<Rightarrow> imp2_stmt"    ("_ := _'( _ ')"           [900, 1000, 0] 61)


  "_imp2_stmts_one" :: "imp2_stmt \<Rightarrow> imp2_stmts"                  ("_" 61)
  "_imp2_stmts_seq" :: "imp2_stmts \<Rightarrow> imp2_stmt \<Rightarrow> imp2_stmts" ("_; _"                   [61, 61] 61)

  "_imp2_com_wrap" :: "imp2_stmt \<Rightarrow> imp2_com"                  ("_" 61)
  "_imp2_seq"    :: "imp2_com \<Rightarrow> imp2_com \<Rightarrow> imp2_com"       ("_; _"                   [60, 61] 60)
  "_imp2_actuals_one" :: "imp2_aexp \<Rightarrow> imp2_actuals"                    ("_")
  "_imp2_actuals_cons" :: "imp2_aexp \<Rightarrow> imp2_actuals \<Rightarrow> imp2_actuals" ("_ , _")
  "_imp2_pbody_stmt" :: "imp2_com \<Rightarrow> imp2_pbody"                      ("_")
  "_imp2_pbody_ret" :: "imp2_aexp \<Rightarrow> imp2_pbody"                    ("return _")
  "_imp2_pbody_stmt_ret" :: "imp2_com \<Rightarrow> imp2_aexp \<Rightarrow> imp2_pbody" ("_ ; return _")



  "_PROGKW0"    :: "imp2_funcs \<Rightarrow> imp_prog"                ("program { _ }")
  "_PROGKW"     :: "imp2_ids \<Rightarrow> imp2_funcs \<Rightarrow> imp_prog"      ("program { int _ ; _ }")
  "_ids_one"     :: "id \<Rightarrow> imp2_ids"                             ("_")
  "_ids_cons"    :: "id \<Rightarrow> imp2_ids \<Rightarrow> imp2_ids"                ("_ , _")
  "_formals_one"  :: "id \<Rightarrow> imp2_formals"                         ("_")
  "_formals_cons" :: "id \<Rightarrow> imp2_formals \<Rightarrow> imp2_formals"  ("_ , _")
  "_funcs_nil"   :: imp2_funcs                                    ("")
  "_funcs_cons0" :: "id \<Rightarrow> imp2_pbody \<Rightarrow> imp2_funcs \<Rightarrow> imp2_funcs"  ("void _'(') { _ } _")
  "_funcs_cons"  :: "id \<Rightarrow> imp2_formals \<Rightarrow> imp2_pbody \<Rightarrow> imp2_funcs \<Rightarrow> imp2_funcs"  ("void _'( _ ') { _ } _")


  "_imp2_var"    :: "id \<Rightarrow> imp2_aexp"                        ("_"   1000)
  "_imp2_num"    :: "num_const \<Rightarrow> imp2_aexp"                 ("_"   1000)
  "_imp2_zero"   :: imp2_aexp                                 ("0"   1000)
  "_imp2_one"    :: imp2_aexp                                 ("1"   1000)
  "_imp2_uminus" :: "imp2_aexp \<Rightarrow> imp2_aexp"                        ("- _"                    90)
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
    val c_Call   = "IMP2_Proc.com.Call"
    val c_Return = "IMP2_Proc.com.Return"
    val c_proc_decl_of = "IMP2_Proc.proc_decl_of"

    val c_None    = "Option.option.None"
    val c_Some    = "Option.option.Some"
    val c_fun_upd = "Fun.fun_upd"
    val c_imp_prog = "IMP2_Notation.imp_prog.make"
    val c_Cons    = "List.list.Cons"
    val c_Nil     = "List.list.Nil"

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

    fun neg_num n =
      K c_N $ HOLogic.mk_number HOLogic.intT (~ n)

    fun aexp_tr t =
      (case Term.strip_comb t of
         (Const ("_imp2_var", _), [Free (x, _)]) =>
           K c_V $ HOLogic.mk_string x
       | (Const ("_imp2_zero", _), []) => K c_N $ HOLogic.mk_number HOLogic.intT 0
       | (Const ("_imp2_one", _), []) => K c_N $ HOLogic.mk_number HOLogic.intT 1
       | (Const ("_imp2_num", _), [n]) =>
           K c_N $ HOLogic.mk_number HOLogic.intT (read_num_const n)
       | (Const ("_imp2_uminus", _), [a]) =>
           (case Term.strip_comb a of
              (Const ("_imp2_num", _), [n]) => neg_num (read_num_const n)
            | (Const ("_imp2_zero", _), []) =>
                K c_N $ HOLogic.mk_number HOLogic.intT 0
            | (Const ("_imp2_one", _), []) => neg_num 1
            | (Const ("_imp2_uminus", _), [b]) => aexp_tr b
            | _ =>
                K c_Minus $ (K c_N $ HOLogic.mk_number HOLogic.intT 0) $ aexp_tr a)
       | (Const ("_imp2_plus", _), [a, b]) => K c_Plus  $ aexp_tr a $ aexp_tr b
       | (Const ("_imp2_minus", _), [a, b]) => K c_Minus $ aexp_tr a $ aexp_tr b
       | (Const ("_imp2_times", _), [a, b]) => K c_Times $ aexp_tr a $ aexp_tr b
       | _ => raise TERM ("IMP2_Notation: aexp_tr", [t]))

    fun bexp_tr t =
      (case Term.strip_comb t of
         (Const ("_imp2_true", _), []) => K c_Bc $ @{term True}
       | (Const ("_imp2_false", _), []) => K c_Bc $ @{term False}
       | (Const ("_imp2_less", _), [a, b]) => K c_Less $ aexp_tr a $ aexp_tr b
       | (Const ("_imp2_eq", _), [a, b]) => K c_Eq   $ aexp_tr a $ aexp_tr b
       | (Const ("_imp2_not", _), [b]) => K c_Not $ bexp_tr b
       | (Const ("_imp2_and", _), [a, b]) => K c_And $ bexp_tr a $ bexp_tr b
       | (Const ("_imp2_or", _), [a, b]) => K c_Or $ bexp_tr a $ bexp_tr b
       | _ => raise TERM ("IMP2_Notation: bexp_tr", [t]))

    fun actuals_tr (Const ("_imp2_actuals_nil", _)) = K c_Nil
      | actuals_tr (Const ("_imp2_actuals_one", _) $ a) =
          K c_Cons $ aexp_tr a $ K c_Nil
      | actuals_tr (Const ("_imp2_actuals_cons", _) $ a $ rest) =
          K c_Cons $ aexp_tr a $ actuals_tr rest
      | actuals_tr t = raise TERM ("IMP2_Notation: actuals_tr", [t])

    (* Keep the raw AST; com_tr / aexp_tr run once, later in mk_table / main.
       NONE body means a return-only procedure, whose command part is SKIP. *)
    fun pbody_tr (Const ("_imp2_pbody_stmt", _) $ c) = (SOME c, NONE)
      | pbody_tr (Const ("_imp2_pbody_ret", _) $ e) = (NONE, SOME e)
      | pbody_tr (Const ("_imp2_pbody_stmt_ret", _) $ c $ e) = (SOME c, SOME e)
      | pbody_tr t = raise TERM ("IMP2_Notation: pbody_tr", [t])

    and stmts_tr (Const ("_imp2_stmts_one", _) $ s) = stmt_tr s
      | stmts_tr (Const ("_imp2_stmts_seq", _) $ ss $ s) =
          K c_Seq $ stmts_tr ss $ stmt_tr s
      | stmts_tr t = raise TERM ("IMP2_Notation: stmts_tr", [t])

    and stmt_tr (Const ("_imp2_skip",   _)) = K c_SKIP
      | stmt_tr (Const ("_imp2_assign", _) $ Free (x, _) $ a) =
          K c_Assign $ HOLogic.mk_string x $ aexp_tr a
      | stmt_tr (Const ("_imp2_if",     _) $ b $ s1 $ s2) =
          K c_If $ bexp_tr b $ stmts_tr s1 $ stmts_tr s2
      | stmt_tr (Const ("_imp2_while",  _) $ b $ s) = K c_While $ bexp_tr b $ stmts_tr s
      | stmt_tr (Const ("_imp2_call0",   _) $ Free (p, _)) =
          K c_Call $ K c_None $ HOLogic.mk_string p $ K c_Nil
      | stmt_tr (Const ("_imp2_call",   _) $ Free (p, _) $ actuals) =
          K c_Call $ K c_None $ HOLogic.mk_string p $ actuals_tr actuals
      | stmt_tr (Const ("_imp2_callret0", _) $ Free (x, _) $ Free (p, _)) =
          K c_Call $ (K c_Some $ HOLogic.mk_string x) $ HOLogic.mk_string p $ K c_Nil
      | stmt_tr (Const ("_imp2_callret", _) $ Free (x, _) $ Free (p, _) $ actuals) =
          K c_Call $ (K c_Some $ HOLogic.mk_string x) $ HOLogic.mk_string p $ actuals_tr actuals
      | stmt_tr t = raise TERM ("IMP2_Notation: stmt_tr", [t])

    and com_tr (Const ("_imp2_com_wrap", _) $ s) = stmt_tr s
      | com_tr (Const ("_imp2_seq",    _) $ c1 $ c2) = K c_Seq   $ com_tr c1 $ com_tr c2
      | com_tr t = raise TERM ("IMP2_Notation: com_tr", [t])

    fun names_of (Const ("_ids_nil", _)) = []
      | names_of (Const ("_ids_one", _) $ Free (x, _)) = [x]
      | names_of (Const ("_ids_cons", _) $ Free (x, _) $ rest) = x :: names_of rest
      | names_of t = raise TERM ("IMP2_Notation: names_of", [t])

    fun formals_of (Const ("_formals_one", _) $ Free (x, _)) = [x]
      | formals_of (Const ("_formals_cons", _) $ Free (x, _) $ rest) = x :: formals_of rest
      | formals_of t = raise TERM ("IMP2_Notation: formals_of", [t])

    fun ids_tr (Const ("_gdecl_none", _)) = []
      | ids_tr (Const ("_gdecl", _) $ ids) = names_of ids
      | ids_tr t = raise TERM ("IMP2_Notation: ids_tr", [t])

    fun funcs_tr (Const ("_funcs_nil", _)) = []
      | funcs_tr (Const ("_funcs_cons0", _) $ Free (f, _) $ pbody $ rest) =
          let
            val (body, result) = pbody_tr pbody
          in
            (f, [], body, result) :: funcs_tr rest
          end
      | funcs_tr (Const ("_funcs_cons", _) $ Free (f, _) $ formals $ pbody $ rest) =
          let
            val (body, result) = pbody_tr pbody
          in
            (f, formals_of formals, body, result) :: funcs_tr rest
          end
      | funcs_tr t = raise TERM ("IMP2_Notation: funcs_tr", [t])

    fun add_vars_proc (_, _, body, result) acc =
      let
        val acc' = (case body of NONE => acc | SOME c => add_vars c acc)
      in
        case result of
          NONE => acc'
        | SOME e => add_vars e acc'
      end

    (* Variable occurrences in a command AST: reads and assignment targets.
       Procedure names under call syntax are not store variables, so skip them. *)
    and add_vars (Const ("_imp2_var", _) $ Free (x, _)) acc = x :: acc
      | add_vars (Const ("_imp2_assign", _) $ Free (x, _) $ a) acc = add_vars a (x :: acc)
      | add_vars (Const ("_imp2_call", _) $ _ $ actuals) acc = add_vars actuals acc
      | add_vars (Const ("_imp2_callret", _) $ Free (x, _) $ _ $ actuals) acc = add_vars actuals (x :: acc)
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

    fun check_distinct kind xs =
      (case duplicates (op =) xs of
         [] => ()
       | ds => error ("IMP2 program: duplicate " ^ kind ^ ": " ^ commas_quote ds))

    val empty_table = Abs ("_", dummyT, K c_None)

    fun mk_names [] = K c_Nil
      | mk_names (n :: ns) = K c_Cons $ HOLogic.mk_string n $ mk_names ns

    fun mk_body NONE = K c_SKIP
      | mk_body (SOME c) = com_tr c

    (* A trailing "return e" becomes an explicit Return command appended to the body;
       the procedure declaration carries no separate result field. *)
    fun mk_body_ret NONE NONE = K c_SKIP
      | mk_body_ret (SOME c) NONE = com_tr c
      | mk_body_ret NONE (SOME e) = K c_Return $ (K c_Some $ aexp_tr e)
      | mk_body_ret (SOME c) (SOME e) =
          K c_Seq $ com_tr c $ (K c_Return $ (K c_Some $ aexp_tr e))

    fun mk_table acc [] = acc
      | mk_table acc ((p, formals, body, result) :: rest) =
          mk_table
            (K c_fun_upd $ acc $ HOLogic.mk_string p
              $ (K c_Some $ ((K c_proc_decl_of $ mk_names formals)
                  $ mk_body_ret body result)))
            rest

    (* dummyT constructors only; type inference runs after the translation. *)
    fun prog_tr decls funcs_t =
      let
        val funcs = funcs_tr funcs_t
        val _ = check_distinct "procedure" (map (fn (n, _, _, _) => n) funcs)
        val _ = check_distinct "declared global" decls
        val _ = List.app (fn (n, formals, _, _) =>
                  check_distinct ("formal parameter of " ^ quote n) formals) funcs
        val _ = check_globals decls (fold add_vars_proc funcs [])
        val (mains, procs) = List.partition (fn (n, _, _, _) => n = "main") funcs
        val main_ast =
          (case mains of
             [("main", [], body, NONE)] => body
           | [("main", _, _, SOME _)] => error "IMP2 program: main may not return"
           | [("main", _, _, NONE)] => error "IMP2 program: main must have no formals"
           | [] => error "IMP2 program: missing 'void main() { ... }'"
           | _  => error "IMP2 program: more than one 'void main()'")
        val names = mk_names (map (fn (n, _, _, _) => n) procs)
        val table = mk_table empty_table procs
        val main  = mk_body main_ast
      in K c_imp_prog $ names $ table $ main end
  in
    [("_IMP2", fn _ => fn [t] => com_tr t | _ => raise Match),
     ("_PROGKW0", fn _ => fn [fs] => prog_tr [] fs | _ => raise Match),
     ("_PROGKW", fn _ => fn [g, fs] => prog_tr (names_of g) fs | _ => raise Match)]
  end
\<close>

subsection \<open>Executable examples\<close>

value "imp \<lbrakk> x := 0 \<rbrakk>"
value "imp \<lbrakk> x := 0; y := 1 \<rbrakk>"
value "imp \<lbrakk> if (x < 10) { x := 0 } else { x := 1 } \<rbrakk>"
value "imp \<lbrakk> while (x < 10) { x := x + 1 } \<rbrakk>"

(* zero-arg baseline *)
value "(program { void main() { skip } } :: imp_prog)"
value "(program { int Gx; void ping() { Gx := Gx + 1 } void main() { ping() } } :: imp_prog)"

(* parameter passing, no return *)
value "(program { void ping(x) { skip } void main() { ping(3) } } :: imp_prog)"
value "(program { void ping(a, b) { skip } void main() { ping(1, 2) } } :: imp_prog)"

(* parameter + return value, called with return assignment *)
value "(program { void inc(x) { return x + 1 } void main() { r := inc(5) } } :: imp_prog)"
value "(program { void add(a, b) { skip; return a + b } void main() { r := add(1, 2) } } :: imp_prog)"

(* zero-arg callee returning a value *)
value "(program { void get() { return 42 } void main() { r := get() } } :: imp_prog)"

(* proc-table entry: formals + result wired through *)
value "the (prog_table (program { void inc(x) { return x + 1 } void main() { r := inc(5) } }) ''inc'')"


end
