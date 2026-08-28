theory VIMP_Notation
  imports VIMP_Program VIMP_Grammar_Generated
begin

section \<open>Concrete syntax\<close>

text \<open>
  The \<open>imp \<lbrakk> ... \<rbrakk>\<close> quotation produces an \<^typ>\<open>VIMP_Proc.com\<close> without
  HOL string quotes or qualified constructor names.  The \<open>imp\<close> keyword distinguishes
  command quotation from Pure premises; whole programs use the explicit \<open>program\<close> prefix.

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
  - comparisons:
      <, == map to @{const Less}, @{const Eq}, evaluating to an @{typ int} 0/1
  - constants:
      true/false lower to @{const N} 1/@{const N} 0

  Example:
  @{verbatim [display]
   "definition loop_prog :: VIMP_Proc.com where
      \"loop_prog = imp \<lbrakk>
         x := 0;
         while (x < 20) { x := x + 1 }
       \<rbrakk>\""}

  Whole-program syntax and its \<open>imp_prog\<close> lowering stay hand-written here,
  matching the grammar's \<open>special: program_structure\<close> boundary; every other
  nonterminal and lowering function comes from the generated
  \<open>Vimp_Grammar_Tr\<close> structure.
\<close>

nonterminal imp2_funcs

syntax
  "_IMP2"        :: "imp2_stmts_opt \<Rightarrow> VIMP_Proc.com"        ("imp \<lbrakk> _ \<rbrakk>")

  "_PROGKW0"    :: "imp2_funcs \<Rightarrow> imp_prog"                ("program { _ }")
  "_PROGKW"     :: "imp2_ids \<Rightarrow> imp2_funcs \<Rightarrow> imp_prog"      ("program { global _ ; _ }")
  "_funcs_nil"   :: imp2_funcs                                    ("")
  "_funcs_cons0" :: "id_position \<Rightarrow> imp2_stmts_opt \<Rightarrow> imp2_funcs \<Rightarrow> imp2_funcs"  ("void _'(') { _ } _")
  "_funcs_cons"  :: "id_position \<Rightarrow> imp2_formals \<Rightarrow> imp2_stmts_opt \<Rightarrow> imp2_funcs \<Rightarrow> imp2_funcs"  ("void _'( _ ') { _ } _")

parse_translation \<open>
  let
    val c_proc_decl_ext = "VIMP_Proc.proc_decl.proc_decl_ext"
    val c_Unity   = "Product_Type.Unity"
    val c_imp_prog = "VIMP_Program.mk_program"
    val c_Pair    = "Product_Type.Pair"

    val K = Vimp_Grammar_Tr.K
    val c_SKIP   = Vimp_Grammar_Tr.c_SKIP
    val c_Seq    = Vimp_Grammar_Tr.c_Seq
    val c_Return = Vimp_Grammar_Tr.c_Return
    val c_Some   = Vimp_Grammar_Tr.c_Some
    val c_None   = Vimp_Grammar_Tr.c_None
    val c_Cons   = Vimp_Grammar_Tr.c_Cons
    val c_Nil    = Vimp_Grammar_Tr.c_Nil

    (* Bodies stay raw parse trees until has_return has inspected them;
       mk_body_ret translates afterwards. The procedure name reports
       Markup.skolem, the same category a call site to it reports. *)
    fun funcs_tr ctxt (Const ("_funcs_nil", _)) = []
      | funcs_tr ctxt (Const ("_funcs_cons0", _) $ f $ pbody $ rest) =
          (Vimp_Grammar_Tr.dest_id_position (SOME Markup.skolem) ctxt f, [], SOME pbody, NONE) :: funcs_tr ctxt rest
      | funcs_tr ctxt (Const ("_funcs_cons", _) $ f $ formals $ pbody $ rest) =
          (Vimp_Grammar_Tr.dest_id_position (SOME Markup.skolem) ctxt f, Vimp_Grammar_Tr.formals_of ctxt formals, SOME pbody, NONE) :: funcs_tr ctxt rest
      | funcs_tr _ t = raise TERM ("VIMP_Notation: funcs_tr", [t])

    (* A bare "return;" is a Const without argument, matched by neither the
       _stmt_return case nor the application/abstraction fallbacks. *)
    fun has_return (Const ("_stmt_return", _) $ _) = true
      | has_return (Const ("_stmt_return0", _)) = true
      | has_return (t $ u) = has_return t orelse has_return u
      | has_return (Abs (_, _, b)) = has_return b
      | has_return _ = false

    fun check_distinct kind xs =
      (case duplicates (op =) xs of
         [] => ()
       | ds => error ("VIMP program: duplicate " ^ kind ^ ": " ^ commas_quote ds))

    (* A formal's per-call binding and a global's cross-call persistence are
       incompatible storage classes for one name. *)
    fun check_no_global_formal_collision decls funcs =
      List.app (fn (n, formals, _, _) =>
        case filter (member (op =) decls) formals of
          [] => ()
        | bad => error ("VIMP program: " ^ quote n ^ " declares global(s) as formal(s): "
                         ^ commas_quote bad)) funcs

    fun mk_names [] = K c_Nil
      | mk_names (n :: ns) = K c_Cons $ HOLogic.mk_literal n $ mk_names ns

    (* A trailing "return e" becomes an explicit Return appended to the body. *)
    fun mk_body_ret ctxt NONE NONE = K c_SKIP
      | mk_body_ret ctxt (SOME c) NONE = Vimp_Grammar_Tr.stmts_opt_tr ctxt c
      | mk_body_ret ctxt NONE (SOME e) = K c_Return $ (K c_Some $ Vimp_Grammar_Tr.exp_tr ctxt e)
      | mk_body_ret ctxt (SOME c) (SOME e) =
          K c_Seq $ Vimp_Grammar_Tr.stmts_opt_tr ctxt c $ (K c_Return $ (K c_Some $ Vimp_Grammar_Tr.exp_tr ctxt e))

    fun mk_proc_rep ctxt [] = K c_Nil
      | mk_proc_rep ctxt ((p, formals, body, result) :: rest) =
          K c_Cons
            $ (K c_Pair $ HOLogic.mk_literal p
                $ (K c_proc_decl_ext $ mk_names formals $ mk_body_ret ctxt body result $ K c_Unity))
            $ mk_proc_rep ctxt rest

    (* dummyT constructors only; type inference runs after the translation. *)
    fun prog_tr ctxt decls funcs_t =
      let
        val funcs = funcs_tr ctxt funcs_t
        val _ = check_distinct "procedure" (map (fn (n, _, _, _) => n) funcs)
        val _ = check_distinct "declared global" decls
        val _ = List.app (fn (n, formals, _, _) =>
                  check_distinct ("formal parameter of " ^ quote n) formals) funcs
        val _ = check_no_global_formal_collision decls funcs
        val (mains, procs) = List.partition (fn (n, _, _, _) => n = "main") funcs
        val main_ast =
          (case mains of
             [("main", [], NONE, NONE)] => NONE
           | [("main", [], SOME body, NONE)] =>
               if has_return body then error "VIMP program: main may not return" else SOME body
           | [("main", _, _, SOME _)] => error "VIMP program: main may not return"
           | [("main", _, _, NONE)] => error "VIMP program: main must have no formals"
           | [] => error "VIMP program: missing 'void main() { ... }'"
           | _  => error "VIMP program: more than one 'void main()'")
        val proc_rep = mk_proc_rep ctxt procs
        val main = mk_body_ret ctxt main_ast NONE
        val decl_globals = mk_names decls
      in K c_imp_prog $ proc_rep $ main $ decl_globals end
  in
    [("_IMP2", fn ctxt => fn [t] => Vimp_Grammar_Tr.stmts_opt_tr ctxt t | _ => raise Match),
     ("_PROGKW0", fn ctxt => fn [fs] => prog_tr ctxt [] fs | _ => raise Match),
     ("_PROGKW", fn ctxt => fn [g, fs] => prog_tr ctxt (Vimp_Grammar_Tr.names_of ctxt g) fs | _ => raise Match)]
  end
\<close>

subsection \<open>Smoke tests\<close>

value "imp \<lbrakk> if (x < 10) { x := 0 } else { x := 1 } \<rbrakk>"
value "imp \<lbrakk> __voblint_check(!(x == 0)) \<rbrakk>"
value "program { global Gx; void ping() { Gx := Gx + 1 } void main() { ping() } } :: imp_prog"
value "program { void add(a, b) { skip; return a + b } void main() { r := add(1, 2) } } :: imp_prog"

end

