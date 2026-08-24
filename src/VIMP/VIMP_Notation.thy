theory VIMP_Notation
  imports VIMP_Grammar_Generated
begin

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
\<close>

text \<open>
  Whole-program form.  \<open>program { void f(..) { .. } void main() { .. } }\<close>
  bundles every procedure -- including the distinguished entry \<open>main\<close> -- into
  one \<open>imp_prog\<close> record, ready for
  \<open>compile_prog (prog_table p) (prog_procs p) mnm (prog_main p)\<close>.
\<close>

text \<open>   \<open>declared_global_vars \<close> is the program's declared-global list,
  exactly as the source wrote it.  Program-context concrete operations use
  this list through  \<open>declared_global \<close>; generic interfaces take any
  classifier of type  \<open>vname => bool \<close> as an explicit argument instead of a
  fixed instance.

  A list, not a set: the field is finite by its type, not by an assumption
  that would otherwise have to be threaded through every lemma about
  \<open>imp_prog\<close>.
\<close>

record imp_prog =
  proc_rep :: "(pname * proc_decl) list"
  declared_global_vars :: "vname list"
  declared_kinds :: "typed_var list"

lemma declared_global_vars_finite [simp]:
  "finite (set (declared_global_vars p))"
  by simp

text \<open>
  \<open>declared_global\<close> is the program-relative classifier: a name is
  declared-global exactly when it is in the program's declared list.
  The program-context concrete operations below use this classifier.
\<close>

definition declared_global :: "imp_prog \<Rightarrow> vname \<Rightarrow> bool" where
  "declared_global p x \<longleftrightarrow> x \<in> set (declared_global_vars p)"

lemma declared_global_iff [simp]:
  "declared_global p x \<longleftrightarrow> x \<in> set (declared_global_vars p)"
  by (simp add: declared_global_def)
definition storage_of :: "imp_prog => pname => vname => source_location" where
  "storage_of p owner x =
    (if declared_global p x then GlobalVar else LocalVar owner)"

definition storage_global :: "imp_prog => pname => vname => bool" where
  "storage_global p owner x =
    (case storage_of p owner x of GlobalVar => True | LocalVar _ => False)"

lemma storage_of_global_iff [simp]:
  "storage_of p owner x = GlobalVar \<longleftrightarrow> declared_global p x"
  by (simp add: storage_of_def)

lemma storage_of_implicit_local [simp]:
  "\<not> declared_global p x \<Longrightarrow> storage_of p owner x = LocalVar owner"
  by (simp add: storage_of_def)

lemma storage_global_iff [simp]:
  "storage_global p owner x \<longleftrightarrow> declared_global p x"
  by (simp add: storage_global_def storage_of_def)


lemma storage_of_local_iff [simp]:
  "storage_of p owner x = LocalVar q
    \<longleftrightarrow> \<not> declared_global p x \<and> owner = q"
  by (auto simp: storage_of_def split: if_splits)



text \<open>
  \<open>prog_main_name\<close> is the entry procedure's name.  The \<open>program\<close> parser identifies the
  entry by exactly this name and rejects formals on it, so it is fixed by construction.
\<close>

definition prog_main_name :: pname where
  "prog_main_name = STR ''main''"

text \<open>
  \<open>prog_procs\<close> is the non-entry declared names: every \<open>proc_rep\<close> key except the
  distinguished entry.  This is exactly the complement \<open>wf_compile_input\<close> asks for --
  the entry is declared in \<open>prog_table\<close>, and this list is everything else.
\<close>

definition prog_procs :: "imp_prog => pname list" where
  "prog_procs p = filter (%n. n ~= prog_main_name) (map fst (proc_rep p))"

text \<open>
  \<open>prog_table\<close> is the declaration environment read directly off \<open>proc_rep\<close>: \<open>main\<close> is
  an ordinary entry now, not a field folded in separately, so a program whose \<open>proc_rep\<close>
  omits \<open>prog_main_name\<close> is a legal (if not well-formed) \<^typ>\<open>imp_prog\<close> value.
\<close>

definition prog_table :: "imp_prog => proc_table" where
  "prog_table p = map_of (proc_rep p)"

text \<open>
  \<open>prog_main\<close> reads the entry's body back out of \<open>proc_rep\<close>.  It stays total by
  \<open>the\<close>'s convention on an absent entry; \<open>wf_source_program\<close>'s
  \<open>\<Pi> mnm = Some (proc_decl_of [] main)\<close> conjunct is what makes that lookup meaningful,
  not the record's shape.
\<close>

definition prog_main :: "imp_prog => com" where
  "prog_main p = body (the (prog_table p prog_main_name))"

text \<open>
  \<open>mk_program\<close> is the constructor every caller actually wants: procedure list, entry
  body, declared globals -- the same three arguments \<open>imp_prog\<close> took before \<open>main\<close>
  moved into \<open>proc_rep\<close>.  It conses the entry onto \<open>proc_rep\<close> so a program built
  through it satisfies \<open>wf_source_program\<close>'s entry conjunct unconditionally, matching
  \<open>program\<close> syntax's own contract that \<open>ps\<close> excludes \<open>main\<close> by construction.
\<close>

definition mk_program_typed ::
    "(pname * proc_decl) list => com => vname list => typed_var list => imp_prog" where
  "mk_program_typed ps m gv ks =
     imp_prog.make ((prog_main_name, proc_decl_of [] m) # ps) gv ks"

text \<open>
  \<open>mk_program\<close> is the kind-free special case: a program whose every
  variable has the default kind. Existing callers and the \<open>imp\<close>-level
  examples build through it unchanged.
\<close>

definition mk_program :: "(pname * proc_decl) list => com => vname list => imp_prog" where
  "mk_program ps m gv = mk_program_typed ps m gv []"

text \<open>
  The finite variable scope of an activation contains every declared global, the
  activation's formals and body occurrences, and the reserved return location.
\<close>

definition scope_vnames :: "imp_prog => pname => vname set" where
  "scope_vnames p owner =
    set (declared_global_vars p) \<union> {ret_var} \<union>
    (case prog_table p owner of
      None => {} |
      Some decl => set (formals decl) \<union> com_vnames (body decl))"

lemma finite_scope_vnames [simp]: "finite (scope_vnames p owner)"
  unfolding scope_vnames_def
  by (auto split: option.splits)

definition scope_vnames_list :: "imp_prog => pname => vname list" where
  "scope_vnames_list p owner = sorted_list_of_set (scope_vnames p owner)"

lemma set_scope_vnames_list [simp]:
  "set (scope_vnames_list p owner) = scope_vnames p owner"
  unfolding scope_vnames_list_def
  by simp


definition wf_program_source :: "imp_prog => bool" where
  "wf_program_source p \<longleftrightarrow>
    wf_source_program (storage_global p prog_main_name) (prog_table p)
      prog_main_name (prog_main p)"

lemma wf_program_sourceD:
  "wf_program_source p \<Longrightarrow>
    wf_source_program (storage_global p prog_main_name) (prog_table p)
      prog_main_name (prog_main p)"
  by (simp add: wf_program_source_def)
text \<open>Program-context concrete operations classify each variable through the program declaration.  Identifiers absent from the global declaration are implicitly local to the supplied owner.\<close>

definition prog_enter_state :: "imp_prog => store => store" where
  "prog_enter_state p s = enter_state (storage_global p prog_main_name) s"

definition prog_combine_env :: "imp_prog => store => store => store" where
  "prog_combine_env p s t =
    combine_env (storage_global p prog_main_name) s t"

text \<open>A program's typing environment: each declared kind by name, and the
  default kind \<open>I32\<close> for every undeclared variable \<comment> \<open>an
  unannotated declaration contributes no entry, so it means \<open>int\<close>.\<close>\<close>

definition prog_tyenv :: "imp_prog => tyenv" where
  "prog_tyenv p = tv_env (declared_kinds p)"

definition prog_pstep ::
    "imp_prog => (com \<times> store \<times> frame list \<times> ikind) =>
      (com \<times> store \<times> frame list \<times> ikind) => bool" where
  "prog_pstep p =
    pstep (prog_tyenv p) (storage_global p prog_main_name) (prog_table p)"

definition prog_pcompletes ::
    "imp_prog => com => store => store => ikind => bool" where
  "prog_pcompletes p =
    pcompletes (prog_tyenv p) (storage_global p prog_main_name) (prog_table p)"

definition prog_restrict_local :: "imp_prog => pname => store => store" where
  "prog_restrict_local p owner s =
    (%x. if storage_global p owner x then 0 else s x)"

definition prog_restrict_global :: "imp_prog => store => store" where
  "prog_restrict_global p s =
    (%x. if storage_global p prog_main_name x then s x else 0)"

lemma prog_procs_make_typed [simp]:
  "prog_main_name ~: set (map fst ps)
   ==> prog_procs (mk_program_typed ps m gv ks) = map fst ps"
  by (force simp: prog_procs_def mk_program_typed_def imp_prog.make_def filter_id_conv)

lemma prog_procs_make [simp]:
  "prog_main_name ~: set (map fst ps) ==> prog_procs (mk_program ps m gv) = map fst ps"
  by (simp add: mk_program_def)

lemma prog_table_make_typed [simp]:
  "prog_table (mk_program_typed ps m gv ks)
     = (map_of ps)(prog_main_name |-> proc_decl_of [] m)"
  by (simp add: prog_table_def mk_program_typed_def imp_prog.make_def)

lemma prog_table_make [simp]:
  "prog_table (mk_program ps m gv) = (map_of ps)(prog_main_name |-> proc_decl_of [] m)"
  by (simp add: mk_program_def)

lemma prog_main_make_typed [simp]: "prog_main (mk_program_typed ps m gv ks) = m"
  by (simp add: prog_main_def proc_decl_of_def)

lemma prog_main_make [simp]: "prog_main (mk_program ps m gv) = m"
  by (simp add: mk_program_def)

lemma declared_global_vars_make_typed [simp]:
  "declared_global_vars (mk_program_typed ps m gv ks) = gv"
  by (simp add: mk_program_typed_def imp_prog.make_def)

lemma declared_global_vars_make [simp]: "declared_global_vars (mk_program ps m gv) = gv"
  by (simp add: mk_program_def)

lemma declared_kinds_make_typed [simp]:
  "declared_kinds (mk_program_typed ps m gv ks) = ks"
  by (simp add: mk_program_typed_def imp_prog.make_def)

lemma declared_kinds_make [simp]: "declared_kinds (mk_program ps m gv) = []"
  by (simp add: mk_program_def)

lemma prog_tyenv_make [simp]: "prog_tyenv (mk_program ps m gv) = default_tyenv"
  by (simp add: prog_tyenv_def default_tyenv_def fun_eq_iff)

text \<open>
  Whole-program syntax (\<open>program { ... }\<close>) and its \<open>imp_prog\<close>-specific
  lowering stay hand-written here, matching \<^verbatim>\<open>grammar/vimp.yaml\<close>'s
  \<open>special: program_structure\<close> boundary: every other nonterminal, syntax
  production, and lowering function comes from \<^verbatim>\<open>VIMP_Grammar_Generated\<close>,
  imported above, whose \<open>Vimp_Grammar_Tr\<close> ML structure this theory calls
  into directly (\<open>stmts_opt_tr\<close>, \<open>exp_tr\<close>, \<open>formals_of\<close>, \<open>names_of\<close>).
\<close>

nonterminal imp2_funcs and imp2_gdecl and imp2_gdecls

syntax
  "_IMP2"        :: "imp2_stmts_opt \<Rightarrow> VIMP_Proc.com"        ("imp \<lbrakk> _ \<rbrakk>")

  "_PROGKW0"    :: "imp2_funcs \<Rightarrow> imp_prog"                ("program { _ }")
  "_PROGKW"     :: "imp2_gdecls \<Rightarrow> imp2_funcs \<Rightarrow> imp_prog"  ("program { _ _ }")
  "_gdecl"      :: "imp2_ids \<Rightarrow> imp2_gdecl"                 ("global _ ;")
  "_gdecl_ty"   :: "imp2_ty \<Rightarrow> imp2_ids \<Rightarrow> imp2_gdecl"      ("global _ _ ;")
  "_gdecls_one"  :: "imp2_gdecl \<Rightarrow> imp2_gdecls"             ("_")
  "_gdecls_cons" :: "imp2_gdecl \<Rightarrow> imp2_gdecls \<Rightarrow> imp2_gdecls" ("_ _")
  "_funcs_nil"   :: imp2_funcs                                    ("")
  "_funcs_cons0" :: "id_position \<Rightarrow> imp2_stmts_opt \<Rightarrow> imp2_funcs \<Rightarrow> imp2_funcs"  ("void _'(') { _ } _")
  "_funcs_cons"  :: "id_position \<Rightarrow> imp2_formals \<Rightarrow> imp2_stmts_opt \<Rightarrow> imp2_funcs \<Rightarrow> imp2_funcs"  ("void _'( _ ') { _ } _")

parse_translation \<open>
  let
    val c_proc_decl_of = "VIMP_Proc.proc_decl_of"
    val c_imp_prog = "VIMP_Notation.mk_program_typed"
    val c_Pair    = "Product_Type.Pair"
    val c_TV      = "VIMP_Typing.typed_var.TV"

    val K = Vimp_Grammar_Tr.K
    val c_SKIP   = Vimp_Grammar_Tr.c_SKIP
    val c_Seq    = Vimp_Grammar_Tr.c_Seq
    val c_Return = Vimp_Grammar_Tr.c_Return
    val c_Some   = Vimp_Grammar_Tr.c_Some
    val c_Cons   = Vimp_Grammar_Tr.c_Cons
    val c_Nil    = Vimp_Grammar_Tr.c_Nil

    (* `_funcs_cons0`/`_funcs_cons`'s body argument is already a bare
       imp2_stmts_opt term (no separate imp2_pbody wrapper): the parsed
       `pbody` is used directly, as (SOME pbody, NONE) -- a procedure never
       has a separate trailing-return result field, so the second
       component is always NONE. Bodies stay untranslated raw parse trees
       until program validation (has_return, which walks this raw tree
       directly) has inspected them: mk_body_ret translates via
       Vimp_Grammar_Tr.stmts_opt_tr only once that's done. *)
    (* The procedure name reports Markup.skolem, matching the callee color
       a call site to this same name reports (Vimp_Grammar_Tr.stmt_tr) --
       a declaration and its call sites read as the same category, not
       Markup.free's variable color. *)
    (* A formal is a (name, kind-term option) pair (Vimp_Grammar_Tr.formal_tr):
       the names build the proc_decl; the annotated kinds join the program's
       declared-kind list below. *)
    fun funcs_tr ctxt (Const ("_funcs_nil", _)) = []
      | funcs_tr ctxt (Const ("_funcs_cons0", _) $ f $ pbody $ rest) =
          (Vimp_Grammar_Tr.dest_id_position (SOME Markup.skolem) ctxt f, [], SOME pbody, NONE) :: funcs_tr ctxt rest
      | funcs_tr ctxt (Const ("_funcs_cons", _) $ f $ formals $ pbody $ rest) =
          (Vimp_Grammar_Tr.dest_id_position (SOME Markup.skolem) ctxt f, Vimp_Grammar_Tr.formals_of ctxt formals, SOME pbody, NONE) :: funcs_tr ctxt rest
      | funcs_tr _ t = raise TERM ("VIMP_Notation: funcs_tr", [t])

    (* A `global` line lowers to (name, kind option) pairs, one per listed
       name; a kind annotation applies to every name on its line. *)
    fun gdecl_tr ctxt (Const ("_gdecl", _) $ ids) =
          map (fn n => (n, NONE)) (Vimp_Grammar_Tr.names_of ctxt ids)
      | gdecl_tr ctxt (Const ("_gdecl_ty", _) $ k $ ids) =
          let val kt = Vimp_Grammar_Tr.ty_tr ctxt k
          in map (fn n => (n, SOME kt)) (Vimp_Grammar_Tr.names_of ctxt ids) end
      | gdecl_tr _ t = raise TERM ("VIMP_Notation: gdecl_tr", [t])

    fun gdecls_tr ctxt (Const ("_gdecls_one", _) $ d) = gdecl_tr ctxt d
      | gdecls_tr ctxt (Const ("_gdecls_cons", _) $ d $ rest) =
          gdecl_tr ctxt d @ gdecls_tr ctxt rest
      | gdecls_tr _ t = raise TERM ("VIMP_Notation: gdecls_tr", [t])

    (* Explicit _stmt_return0 case: a bare Const with no argument matches
       neither the specific _stmt_return case (needs "$ _") nor the generic
       `t $ u`/Abs fallbacks (it's neither an application nor an
       abstraction), so without this case a bare "return;" would silently
       read as "does not return" -- would have let `main` end with a bare
       return despite "main may not return" below. *)
    fun has_return (Const ("_stmt_return", _) $ _) = true
      | has_return (Const ("_stmt_return0", _)) = true
      | has_return (t $ u) = has_return t orelse has_return u
      | has_return (Abs (_, _, b)) = has_return b
      | has_return _ = false

    fun check_distinct kind xs =
      (case duplicates (op =) xs of
         [] => ()
       | ds => error ("VIMP program: duplicate " ^ kind ^ ": " ^ commas_quote ds))

    (* A name cannot be both declared global and a procedure formal: the
       formal's per-call binding and the global's cross-call persistence are
       incompatible storage classes for one name. *)
    fun check_no_global_formal_collision decl_names funcs =
      List.app (fn (n, formals, _, _) =>
        case filter (member (op =) decl_names) (map fst formals) of
          [] => ()
        | bad => error ("VIMP program: " ^ quote n ^ " declares global(s) as formal(s): "
                         ^ commas_quote bad)) funcs

    fun mk_names [] = K c_Nil
      | mk_names (n :: ns) = K c_Cons $ HOLogic.mk_literal n $ mk_names ns

    fun mk_kinds [] = K c_Nil
      | mk_kinds ((n, k) :: rest) =
          K c_Cons $ (K c_TV $ HOLogic.mk_literal n $ k) $ mk_kinds rest

    (* A trailing "return e" becomes an explicit Return command appended to the body;
       the procedure declaration carries no separate result field. *)
    fun mk_body_ret ctxt NONE NONE = K c_SKIP
      | mk_body_ret ctxt (SOME c) NONE = Vimp_Grammar_Tr.stmts_opt_tr ctxt c
      | mk_body_ret ctxt NONE (SOME e) = K c_Return $ (K c_Some $ Vimp_Grammar_Tr.exp_tr ctxt e)
      | mk_body_ret ctxt (SOME c) (SOME e) =
          K c_Seq $ Vimp_Grammar_Tr.stmts_opt_tr ctxt c $ (K c_Return $ (K c_Some $ Vimp_Grammar_Tr.exp_tr ctxt e))

    fun mk_proc_rep ctxt [] = K c_Nil
      | mk_proc_rep ctxt ((p, formals, body, result) :: rest) =
          K c_Cons
            $ (K c_Pair $ HOLogic.mk_literal p
                $ ((K c_proc_decl_of $ mk_names (map fst formals)) $ mk_body_ret ctxt body result))
            $ mk_proc_rep ctxt rest

    (* dummyT constructors only; type inference runs after the translation. *)
    fun prog_tr ctxt decls funcs_t =
      let
        val funcs = funcs_tr ctxt funcs_t
        val decl_names = map fst decls
        val _ = check_distinct "procedure" (map (fn (n, _, _, _) => n) funcs)
        val _ = check_distinct "declared global" decl_names
        val _ = List.app (fn (n, formals, _, _) =>
                  check_distinct ("formal parameter of " ^ quote n) (map fst formals)) funcs
        val _ = check_no_global_formal_collision decl_names funcs
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
        val decl_globals = mk_names decl_names
        val kind_entries =
          List.mapPartial (fn (n, k) => Option.map (fn k => (n, k)) k)
            (decls @ List.concat (map (fn (_, formals, _, _) => formals) funcs))
      in K c_imp_prog $ proc_rep $ main $ decl_globals $ mk_kinds kind_entries end
  in
    [("_IMP2", fn ctxt => fn [t] => Vimp_Grammar_Tr.stmts_opt_tr ctxt t | _ => raise Match),
     ("_PROGKW0", fn ctxt => fn [fs] => prog_tr ctxt [] fs | _ => raise Match),
     ("_PROGKW", fn ctxt => fn [g, fs] => prog_tr ctxt (gdecls_tr ctxt g) fs | _ => raise Match)]
  end
\<close>

subsection \<open>Executable examples\<close>

value "imp \<lbrakk> x := 0 \<rbrakk>"
value "imp \<lbrakk> x := 0; y := 1 \<rbrakk>"
value "imp \<lbrakk> x := f() \<rbrakk>"
value "imp \<lbrakk> if (x < 10) { x := 0 } else { x := 1 } \<rbrakk>"
value "imp \<lbrakk> while (x < 10) { x := x + 1 } \<rbrakk>"
value "imp \<lbrakk> return 7 \<rbrakk>"
value "(program {
  global Gx;
  void f() { if (Gx < 0) { return 1 } else { skip } }
  void main() { f() }
} :: imp_prog)"

(* zero-arg baseline *)
value "(program { void main() { skip } } :: imp_prog)"
value "(program { global Gx; void ping() { Gx := Gx + 1 } void main() { ping() } } :: imp_prog)"

text \<open>
  \<open>declared_global_vars\<close> is preserved from the source declaration, not
  re-derived from spelling: a declared non-\<open>G\<close> name is faithfully recorded,
  in declaration order.
\<close>

lemma declared_global_vars_ping_example [simp]:
  "declared_global_vars (program { global Gx; void ping() { Gx := Gx + 1 } void main() { ping() } })
     = [STR ''Gx'']"
  by simp

lemma declared_global_vars_two_names [simp]:
  "declared_global_vars (program { global total, x; void main() { total := x } })
     = [STR ''total'', STR ''x'']"
  by simp

text \<open>   \<open>declared_global \<close> checkpoint: a declared non- \<open>G \<close> name reads as global, an
  undeclared name --  \<open>G \<close>-spelled or not -- reads as local.  This is exactly
  the discrimination a name-spelling classifier cannot make, since it
  classifies by name spelling alone rather than by declaration.
\<close>

lemma declared_global_two_names_examples:
  "declared_global (program { global total, x; void main() { total := x } }) (STR ''total'')"
  "declared_global (program { global total, x; void main() { total := x } }) (STR ''x'')"
  "\<not> declared_global (program { global total, x; void main() { total := x } }) (STR ''y'')"
  "\<not> declared_global (program { global total, x; void main() { total := x } }) (STR ''Gy'')"
  by simp_all

value "declared_global_vars (program { void main() { skip } } :: imp_prog)"

(* parameter passing, no return *)
value "(program { void ping(x) { skip } void main() { ping(3) } } :: imp_prog)"
value "(program { void ping(a, b) { skip } void main() { ping(1, 2) } } :: imp_prog)"

(* parameter + return value, called with return assignment *)
value "(program { void inc(x) { return x + 1 } void main() { r := inc(5) } } :: imp_prog)"
value "(program { void add(a, b) { skip; return a + b } void main() { r := add(1, 2) } } :: imp_prog)"

(* zero-arg callee returning a value *)
value "(program { void get() { return 42 } void main() { r := get() } } :: imp_prog)"

text \<open>
  A typed program: a declared global, a formal, and a local all carry an
  explicit kind. Untyped declarations coexist on the same lines/programs
  and default to \<open>I32\<close> (\<open>declared_kinds\<close> records only the
  annotated entries; \<open>prog_tyenv\<close> falls back to \<open>I32\<close> for
  everything else).
\<close>

value "(program {
  global uint8 total;
  void add(int16 delta) { total := total + delta }
  void main() { add(3) }
} :: imp_prog)"

lemma typed_example_declared_kinds [simp]:
  "declared_kinds (program {
     global uint8 total;
     void add(int16 delta) { total := total + delta }
     void main() { add(3) }
   }) = [TV (STR ''total'') U8, TV (STR ''delta'') I16]"
  by simp

lemma typed_example_prog_tyenv [simp]:
  "prog_tyenv (program {
     global uint8 total;
     void add(int16 delta) { total := total + delta }
     void main() { add(3) }     }) = (\<lambda>_. I32)(STR ''total'' := U8, STR ''delta'' := I16)"
  by (simp add: prog_tyenv_def default_tyenv_def fun_eq_iff)

(* proc-table entry: formals + result wired through *)
value "the (prog_table (program { void inc(x) { return x + 1 } void main() { r := inc(5) } }) (STR ''inc''))"

(* boolean negation*)
value "imp \<lbrakk> __voblint_check(!(x == 0)) \<rbrakk>"

end
