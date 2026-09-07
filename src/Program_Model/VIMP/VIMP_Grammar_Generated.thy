theory VIMP_Grammar_Generated
  imports VIMP_Proc
begin

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>grammar/vimp.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_vimp_isabelle.py\<close>. Regenerate with the generator rather
  than hand-editing; a CI drift check compares regenerated output against
  this file.

  Owns the grammar-level nonterminals, syntax, and lowering (\<open>Vimp_Grammar_Tr\<close>)
  shared by every VIMP quotation: expressions, statements, statement lists,
  actuals, and the two identifier-list shapes (\<open>formals\<close>/\<open>ids\<close>). Does not
  register \<open>imp \<lbrakk> ... \<rbrakk>\<close> or the whole-program \<open>program { ... }\<close> quotation
  itself, and has no notion of \<open>imp_prog\<close> -- those are \<^verbatim>\<open>VIMP_Notation\<close>'s
  concern (main-selection, \<open>proc_rep\<close> construction, and everything else specific
  to that record shape), which imports this theory and calls into
  \<open>Vimp_Grammar_Tr\<close> for the pieces that are the same regardless of what the
  surrounding quotation ultimately builds.

  Two lowering rules stay hand-written inside \<open>Vimp_Grammar_Tr\<close> rather than
  being generated from \<open>grammar/vimp.yaml\<close> directly: Isabelle's binary
  \<open>Num\<close> literal decoding (\<open>dest_num\<close>/\<open>read_num_const\<close>, no Menhir analogue)
  and the compositional unary-minus rule (folds a numeral operand into a
  negative \<open>N\<close>, otherwise \<open>Minus (N 0) x\<close> -- deliberately does NOT cancel a
  nested unary minus; \<open>--x\<close> lowers to \<open>Minus (N 0) (Minus (N 0) (V x))\<close>,
  matching the shipped CLI frontend, not to \<open>x\<close>). \<open>_exp_zero\<close>/\<open>_exp_one\<close>
  and \<open>_stmt_call0\<close>/\<open>_stmt_callret0\<close> are Isabelle-target realizations of a
  canonical rule that Isabelle's own mixfix grammar cannot express directly:
  \<open>num_const\<close> has no derivation for the literal \<open>0\<close> or \<open>1\<close> (\<open>Num.num\<close>'s
  \<open>One\<close>/\<open>Bit0\<close>/\<open>Bit1\<close> encoding has no zero, and \<open>1\<close> is the unwrapped base
  case), and mixfix lists have no empty derivation at all -- both confirmed
  empirically, not just by inspection: an isolation load test with only the
  generic \<open>actuals\<close> production failed to parse \<open>f()\<close>.
\<close>

nonterminal imp2_exp
nonterminal imp2_stmt
nonterminal imp2_stmts
nonterminal imp2_stmts_opt
nonterminal imp2_actuals
nonterminal imp2_formals
nonterminal imp2_ids

syntax
  "_exp_var" :: "id_position => imp2_exp" ("_" 1000)
  "_exp_num" :: "num_const => imp2_exp" ("_" 1000)
  "_exp_uminus" :: "imp2_exp => imp2_exp" ("- _" [80] 80)
  "_exp_plus" :: "imp2_exp => imp2_exp => imp2_exp" ("_ + _" [60, 61] 60)
  "_exp_minus" :: "imp2_exp => imp2_exp => imp2_exp" ("_ - _" [60, 61] 60)
  "_exp_times" :: "imp2_exp => imp2_exp => imp2_exp" ("_ * _" [70, 71] 70)
  "_exp_true" :: imp2_exp ("true" 1000)
  "_exp_false" :: imp2_exp ("false" 1000)
  "_exp_less" :: "imp2_exp => imp2_exp => imp2_exp" ("_ < _" [51, 50] 50)
  "_exp_eq" :: "imp2_exp => imp2_exp => imp2_exp" ("_ == _" [51, 50] 50)
  "_exp_not" :: "imp2_exp => imp2_exp" ("! _" [80] 80)
  "_exp_and" :: "imp2_exp => imp2_exp => imp2_exp" ("_ && _" [40, 41] 40)
  "_exp_or" :: "imp2_exp => imp2_exp => imp2_exp" ("_ || _" [30, 31] 30)
  "_exp_paren" :: "imp2_exp => imp2_exp" ("'( _ ')" [0] 1000)
  "_stmt_skip" :: imp2_stmt ("skip" 61)
  "_stmt_assign" :: "id_position => imp2_exp => imp2_stmt" ("_ := _" [900, 0] 61)
  "_stmt_return" :: "imp2_exp => imp2_stmt" ("return _" [0] 61)
  "_stmt_return0" :: imp2_stmt ("return" 61)
  "_stmt_check" :: "imp2_exp => imp2_stmt" ("'_'_voblint'_check '( _ ')" [0] 61)
  "_stmt_if" :: "imp2_exp => imp2_stmts_opt => imp2_stmts_opt => imp2_stmt" ("if '( _ ') { _ } else { _ }" [0, 0, 0] 61)
  "_stmt_while" :: "imp2_exp => imp2_stmts_opt => imp2_stmt" ("while '( _ ') { _ }" [0, 0] 61)
  "_stmt_call" :: "id_position => imp2_actuals => imp2_stmt" ("_'( _ ')" [1000, 0] 61)
  "_stmt_callret" :: "id_position => id_position => imp2_actuals => imp2_stmt" ("_ := _'( _ ')" [900, 1000, 0] 61)
  "_stmts_one" :: "imp2_stmt => imp2_stmts" ("_" 61)
  "_stmts_seq" :: "imp2_stmts => imp2_stmt => imp2_stmts" ("_; _" [61, 61] 61)
  "_stmts_opt_none" :: imp2_stmts_opt ("")
  "_stmts_opt_some" :: "imp2_stmts => imp2_stmts_opt" ("_")
  "_actuals_one" :: "imp2_exp => imp2_actuals" ("_")
  "_actuals_cons" :: "imp2_exp => imp2_actuals => imp2_actuals" ("_, _")
  "_formals_one" :: "id_position => imp2_formals" ("_")
  "_formals_cons" :: "id_position => imp2_formals => imp2_formals" ("_, _")
  "_ids_one" :: "id_position => imp2_ids" ("_")
  "_ids_cons" :: "id_position => imp2_ids => imp2_ids" ("_, _")
  "_exp_zero" :: imp2_exp ("0" 1000)
  "_exp_one" :: imp2_exp ("1" 1000)
  "_stmt_call0" :: "id_position => imp2_stmt" ("_'(')" [1000] 61)
  "_stmt_callret0" :: "id_position => id_position => imp2_stmt" ("_ := _'(')" [900, 1000] 61)

ML \<open>
structure Vimp_Grammar_Tr =
struct
  val c_N      = "VIMP_Syntax.N"
  val c_V      = "VIMP_Syntax.V"
  val c_Plus   = "VIMP_Syntax.exp.Plus"
  val c_Minus  = "VIMP_Syntax.exp.Minus"
  val c_Times  = "VIMP_Syntax.exp.Times"

  val c_Less   = "VIMP_Syntax.exp.Less"
  val c_Eq     = "VIMP_Syntax.exp.Eq"
  val c_Not    = "VIMP_Syntax.exp.Not"
  val c_And    = "VIMP_Syntax.exp.And"
  val c_Or     = "VIMP_Syntax.exp.Or"

  val c_SKIP   = "VIMP_Proc.com.SKIP"
  val c_Assign = "VIMP_Proc.com.Assign"
  val c_Seq    = "VIMP_Proc.com.Seq"
  val c_If     = "VIMP_Proc.com.If"
  val c_While  = "VIMP_Proc.com.While"
  val c_Call   = "VIMP_Proc.com.Call"
  val c_Return = "VIMP_Proc.com.Return"
  val c_Check  = "VIMP_Proc.com.Check"

  val c_None   = "Option.option.None"
  val c_Some   = "Option.option.Some"
  val c_Cons   = "List.list.Cons"
  val c_Nil    = "List.list.Nil"

  fun K name = Const (name, dummyT)

  (* Decode Isabelle's Num binary structure: One=1, Bit0 n=2n, Bit1 n=2n+1.
     Leaf may also be a decimal-string Const (e.g. Const("20",_)) from the
     raw lexer. *)
  fun dest_num (Const (c, _)) =
        let val name = Long_Name.base_name c
        in if name = "One" then 1
           else case Int.fromString name of
                  SOME n => n
                | NONE => raise TERM ("Vimp_Grammar_Tr: not a num leaf", [Const (c, dummyT)])
        end
    | dest_num (Const (c, _) $ t) =
        let val name = Long_Name.base_name c
            val n    = dest_num t
        in if name = "Bit0" then 2 * n
           else if name = "Bit1" then 2 * n + 1
           else raise TERM ("Vimp_Grammar_Tr: not a num constructor", [Const (c, dummyT) $ t])
        end
    | dest_num t = raise TERM ("Vimp_Grammar_Tr: dest_num catchall", [t])

  fun read_num_const (Const ("_constify", _) $ t) = read_num_const t
    | read_num_const (Const ("_position", _) $ t) = read_num_const t
    | read_num_const ((Const ("_constrain", _) $ t) $ _) = read_num_const t
    | read_num_const (Free (s, _)) =
        (case Int.fromString s of
           SOME n => n
         | NONE => raise TERM ("Vimp_Grammar_Tr: not a numeral", [Free (s, dummyT)]))
    | read_num_const (Const (s, _)) =
        (case Int.fromString (Long_Name.base_name s) of
           SOME n => n
         | NONE => raise TERM ("Vimp_Grammar_Tr: not a numeral", [Const (s, dummyT)]))
    | read_num_const t = dest_num t

  fun neg_num n = K c_N $ HOLogic.mk_number HOLogic.intT (~ n)

  fun dest_id_position report_markup ctxt (Const ("_constrain", _) $ Free (s, _) $ m) =
        (case (report_markup, Term_Position.decode_position m) of
           (SOME markup, SOME (ps, _)) =>
             (List.app (fn p => Context_Position.report ctxt (#pos p) markup) ps; s)
         | _ => s)
    | dest_id_position _ _ (Free (s, _)) = s
    | dest_id_position _ _ t = raise TERM ("Vimp_Grammar_Tr: dest_id_position", [t])

  fun exp_tr ctxt t =
        (case Term.strip_comb t of
           (Const ("_exp_num", _), [n]) =>
             K c_N $ HOLogic.mk_number HOLogic.intT (read_num_const n)
         | (Const ("_exp_uminus", _), [a]) =>
             (case Term.strip_comb a of
                (Const ("_exp_num", _), [n]) => neg_num (read_num_const n)
              | (Const ("_exp_zero", _), []) =>
                  K c_N $ HOLogic.mk_number HOLogic.intT 0
              | (Const ("_exp_one", _), []) => neg_num 1
              | _ =>
                  K c_Minus $ (K c_N $ HOLogic.mk_number HOLogic.intT 0) $ exp_tr ctxt a)
         | (Const ("_exp_zero", _), []) => K c_N $ HOLogic.mk_number HOLogic.intT 0
         | (Const ("_exp_one", _), []) => K c_N $ HOLogic.mk_number HOLogic.intT 1
         | (Const ("_exp_var", _), [x0]) => K c_V $ (HOLogic.mk_literal (dest_id_position (SOME Markup.free) ctxt x0))
         | (Const ("_exp_plus", _), [a0, a2]) => K c_Plus $ (exp_tr ctxt a0) $ (exp_tr ctxt a2)
         | (Const ("_exp_minus", _), [a0, a2]) => K c_Minus $ (exp_tr ctxt a0) $ (exp_tr ctxt a2)
         | (Const ("_exp_times", _), [a0, a2]) => K c_Times $ (exp_tr ctxt a0) $ (exp_tr ctxt a2)
         | (Const ("_exp_true", _), []) => K c_N $ (HOLogic.mk_number HOLogic.intT 1)
         | (Const ("_exp_false", _), []) => K c_N $ (HOLogic.mk_number HOLogic.intT 0)
         | (Const ("_exp_less", _), [a0, a2]) => K c_Less $ (exp_tr ctxt a0) $ (exp_tr ctxt a2)
         | (Const ("_exp_eq", _), [a0, a2]) => K c_Eq $ (exp_tr ctxt a0) $ (exp_tr ctxt a2)
         | (Const ("_exp_not", _), [a1]) => K c_Not $ (exp_tr ctxt a1)
         | (Const ("_exp_and", _), [a0, a2]) => K c_And $ (exp_tr ctxt a0) $ (exp_tr ctxt a2)
         | (Const ("_exp_or", _), [a0, a2]) => K c_Or $ (exp_tr ctxt a0) $ (exp_tr ctxt a2)
         | (Const ("_exp_paren", _), [a1]) => exp_tr ctxt a1
         | _ => raise TERM ("Vimp_Grammar_Tr: exp_tr", [t]))

  fun actuals_tr ctxt (Const ("_actuals_one", _) $ x) = K c_Cons $ (exp_tr ctxt x) $ K c_Nil
    | actuals_tr ctxt (Const ("_actuals_cons", _) $ x $ rest) = K c_Cons $ (exp_tr ctxt x) $ (actuals_tr ctxt rest)
    | actuals_tr _ t = raise TERM ("Vimp_Grammar_Tr: actuals_tr", [t])

  fun stmts_tr ctxt (Const ("_stmts_one", _) $ x) = stmt_tr ctxt x
    | stmts_tr ctxt (Const ("_stmts_seq", _) $ xs $ x) = K c_Seq $ (stmts_tr ctxt xs) $ (stmt_tr ctxt x)
    | stmts_tr _ t = raise TERM ("Vimp_Grammar_Tr: stmts_tr", [t])
  and stmts_opt_tr ctxt (Const ("_stmts_opt_none", _)) = K c_SKIP
    | stmts_opt_tr ctxt (Const ("_stmts_opt_some", _) $ s) = stmts_tr ctxt s
    | stmts_opt_tr _ t = raise TERM ("Vimp_Grammar_Tr: stmts_opt_tr", [t])
  and stmt_tr ctxt t =
        (case Term.strip_comb t of
           (Const ("_stmt_call0", _), [x0]) => K c_Call $ (K c_None) $ (HOLogic.mk_literal (dest_id_position (SOME Markup.skolem) ctxt x0)) $ K c_Nil
         | (Const ("_stmt_callret0", _), [x0, x2]) => K c_Call $ ((K c_Some $ (HOLogic.mk_literal (dest_id_position (SOME Markup.free) ctxt x0)))) $ (HOLogic.mk_literal (dest_id_position (SOME Markup.skolem) ctxt x2)) $ K c_Nil
         | (Const ("_stmt_skip", _), []) => K c_SKIP
         | (Const ("_stmt_assign", _), [x0, a2]) => K c_Assign $ (HOLogic.mk_literal (dest_id_position (SOME Markup.free) ctxt x0)) $ (exp_tr ctxt a2)
         | (Const ("_stmt_return", _), [a1]) => K c_Return $ ((K c_Some $ (exp_tr ctxt a1)))
         | (Const ("_stmt_return0", _), []) => K c_Return $ (K c_None)
         | (Const ("_stmt_check", _), [a2]) => K c_Check $ (exp_tr ctxt a2)
         | (Const ("_stmt_if", _), [a2, a5, a9]) => K c_If $ (exp_tr ctxt a2) $ (stmts_opt_tr ctxt a5) $ (stmts_opt_tr ctxt a9)
         | (Const ("_stmt_while", _), [a2, a5]) => K c_While $ (exp_tr ctxt a2) $ (stmts_opt_tr ctxt a5)
         | (Const ("_stmt_call", _), [x0, a2]) => K c_Call $ (K c_None) $ (HOLogic.mk_literal (dest_id_position (SOME Markup.skolem) ctxt x0)) $ (actuals_tr ctxt a2)
         | (Const ("_stmt_callret", _), [x0, x2, a4]) => K c_Call $ ((K c_Some $ (HOLogic.mk_literal (dest_id_position (SOME Markup.free) ctxt x0)))) $ (HOLogic.mk_literal (dest_id_position (SOME Markup.skolem) ctxt x2)) $ (actuals_tr ctxt a4)
         | _ => raise TERM ("Vimp_Grammar_Tr: stmt_tr", [t]))

  fun formals_of ctxt (Const ("_formals_one", _) $ x) = [dest_id_position (SOME Markup.free) ctxt x]
    | formals_of ctxt (Const ("_formals_cons", _) $ x $ rest) = dest_id_position (SOME Markup.free) ctxt x :: formals_of ctxt rest
    | formals_of _ t = raise TERM ("Vimp_Grammar_Tr: formals_of", [t])

  fun names_of ctxt (Const ("_ids_one", _) $ x) = [dest_id_position (SOME Markup.bound) ctxt x]
    | names_of ctxt (Const ("_ids_cons", _) $ x $ rest) = dest_id_position (SOME Markup.bound) ctxt x :: names_of ctxt rest
    | names_of _ t = raise TERM ("Vimp_Grammar_Tr: names_of", [t])
end
\<close>

end
