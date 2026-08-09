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
  matching the shipped CLI frontend, not to \<open>x\<close>). \<open>_aexp_zero\<close>/\<open>_aexp_one\<close>
  and \<open>_stmt_call0\<close>/\<open>_stmt_callret0\<close> are Isabelle-target realizations of a
  canonical rule that Isabelle's own mixfix grammar cannot express directly:
  \<open>num_const\<close> has no derivation for the literal \<open>0\<close> or \<open>1\<close> (\<open>Num.num\<close>'s
  \<open>One\<close>/\<open>Bit0\<close>/\<open>Bit1\<close> encoding has no zero, and \<open>1\<close> is the unwrapped base
  case), and mixfix lists have no empty derivation at all -- both confirmed
  empirically, not just by inspection: an isolation load test with only the
  generic \<open>actuals\<close> production failed to parse \<open>f()\<close>.
\<close>

nonterminal imp2_aexp
nonterminal imp2_bexp
nonterminal imp2_stmt
nonterminal imp2_stmts
nonterminal imp2_stmts_opt
nonterminal imp2_actuals
nonterminal imp2_formals
nonterminal imp2_ids

syntax
  "_aexp_var" :: "id => imp2_aexp" ("_" 1000)
  "_aexp_num" :: "num_const => imp2_aexp" ("_" 1000)
  "_aexp_uminus" :: "imp2_aexp => imp2_aexp" ("- _" [80] 80)
  "_aexp_plus" :: "imp2_aexp => imp2_aexp => imp2_aexp" ("_ + _" [60, 61] 60)
  "_aexp_minus" :: "imp2_aexp => imp2_aexp => imp2_aexp" ("_ - _" [60, 61] 60)
  "_aexp_times" :: "imp2_aexp => imp2_aexp => imp2_aexp" ("_ * _" [70, 71] 70)
  "_aexp_paren" :: "imp2_aexp => imp2_aexp" ("'( _ ')" [0] 1000)
  "_bexp_true" :: imp2_bexp ("true" 1000)
  "_bexp_false" :: imp2_bexp ("false" 1000)
  "_bexp_less" :: "imp2_aexp => imp2_aexp => imp2_bexp" ("_ < _" 50)
  "_bexp_eq" :: "imp2_aexp => imp2_aexp => imp2_bexp" ("_ == _" 50)
  "_bexp_paren" :: "imp2_bexp => imp2_bexp" ("'( _ ')" [0] 1000)
  "_bexp_not" :: "imp2_bexp => imp2_bexp" ("! _" [80] 80)
  "_bexp_and" :: "imp2_bexp => imp2_bexp => imp2_bexp" ("_ && _" [40, 41] 40)
  "_bexp_or" :: "imp2_bexp => imp2_bexp => imp2_bexp" ("_ || _" [30, 31] 30)
  "_stmt_skip" :: imp2_stmt ("skip" 61)
  "_stmt_assign" :: "id => imp2_aexp => imp2_stmt" ("_ := _" [900, 0] 61)
  "_stmt_random" :: "id => imp2_stmt" ("_ := random'(')" [900] 61)
  "_stmt_return" :: "imp2_aexp => imp2_stmt" ("return _" [0] 61)
  "_stmt_return0" :: imp2_stmt ("return" 61)
  "_stmt_check" :: "imp2_bexp => imp2_stmt" ("'_'_voblint'_check '( _ ')" [0] 61)
  "_stmt_if" :: "imp2_bexp => imp2_stmts_opt => imp2_stmts_opt => imp2_stmt" ("if '( _ ') { _ } else { _ }" [0, 0, 0] 61)
  "_stmt_while" :: "imp2_bexp => imp2_stmts_opt => imp2_stmt" ("while '( _ ') { _ }" [0, 0] 61)
  "_stmt_call" :: "id => imp2_actuals => imp2_stmt" ("_'( _ ')" [1000, 0] 61)
  "_stmt_callret" :: "id => id => imp2_actuals => imp2_stmt" ("_ := _'( _ ')" [900, 1000, 0] 61)
  "_stmts_one" :: "imp2_stmt => imp2_stmts" ("_" 61)
  "_stmts_seq" :: "imp2_stmts => imp2_stmt => imp2_stmts" ("_; _" [61, 61] 61)
  "_stmts_opt_none" :: imp2_stmts_opt ("")
  "_stmts_opt_some" :: "imp2_stmts => imp2_stmts_opt" ("_")
  "_actuals_one" :: "imp2_aexp => imp2_actuals" ("_")
  "_actuals_cons" :: "imp2_aexp => imp2_actuals => imp2_actuals" ("_, _")
  "_formals_one" :: "id => imp2_formals" ("_")
  "_formals_cons" :: "id => imp2_formals => imp2_formals" ("_, _")
  "_ids_one" :: "id => imp2_ids" ("_")
  "_ids_cons" :: "id => imp2_ids => imp2_ids" ("_, _")
  "_aexp_zero" :: imp2_aexp ("0" 1000)
  "_aexp_one" :: imp2_aexp ("1" 1000)
  "_stmt_call0" :: "id => imp2_stmt" ("_'(')" [1000] 61)
  "_stmt_callret0" :: "id => id => imp2_stmt" ("_ := _'(')" [900, 1000] 61)

ML \<open>
structure Vimp_Grammar_Tr =
struct
  val c_N      = "VIMP_Syntax.N"
  val c_V      = "VIMP_Syntax.V"
  val c_Plus   = "VIMP_Syntax.aexp.Plus"
  val c_Minus  = "VIMP_Syntax.aexp.Minus"
  val c_Times  = "VIMP_Syntax.aexp.Times"

  val c_Bc     = "VIMP_Syntax.Bc"
  val c_Less   = "VIMP_Syntax.bexp.Less"
  val c_Eq     = "VIMP_Syntax.bexp.Eq"
  val c_Not    = "VIMP_Syntax.bexp.Not"
  val c_And    = "VIMP_Syntax.bexp.And"
  val c_Or     = "VIMP_Syntax.bexp.Or"

  val c_SKIP   = "VIMP_Proc.com.SKIP"
  val c_Assign = "VIMP_Proc.com.Assign"
  val c_Seq    = "VIMP_Proc.com.Seq"
  val c_If     = "VIMP_Proc.com.If"
  val c_While  = "VIMP_Proc.com.While"
  val c_Call   = "VIMP_Proc.com.Call"
  val c_Return = "VIMP_Proc.com.Return"
  val c_Random = "VIMP_Proc.com.Random"
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

  fun aexp_tr t =
        (case Term.strip_comb t of
           (Const ("_aexp_num", _), [n]) =>
             K c_N $ HOLogic.mk_number HOLogic.intT (read_num_const n)
         | (Const ("_aexp_uminus", _), [a]) =>
             (case Term.strip_comb a of
                (Const ("_aexp_num", _), [n]) => neg_num (read_num_const n)
              | (Const ("_aexp_zero", _), []) =>
                  K c_N $ HOLogic.mk_number HOLogic.intT 0
              | (Const ("_aexp_one", _), []) => neg_num 1
              | _ =>
                  K c_Minus $ (K c_N $ HOLogic.mk_number HOLogic.intT 0) $ aexp_tr a)
         | (Const ("_aexp_zero", _), []) => K c_N $ HOLogic.mk_number HOLogic.intT 0
         | (Const ("_aexp_one", _), []) => K c_N $ HOLogic.mk_number HOLogic.intT 1
         | (Const ("_aexp_var", _), [Free (x0, _)]) => K c_V $ (HOLogic.mk_literal x0)
         | (Const ("_aexp_plus", _), [a0, a2]) => K c_Plus $ (aexp_tr a0) $ (aexp_tr a2)
         | (Const ("_aexp_minus", _), [a0, a2]) => K c_Minus $ (aexp_tr a0) $ (aexp_tr a2)
         | (Const ("_aexp_times", _), [a0, a2]) => K c_Times $ (aexp_tr a0) $ (aexp_tr a2)
         | (Const ("_aexp_paren", _), [a1]) => aexp_tr a1
         | _ => raise TERM ("Vimp_Grammar_Tr: aexp_tr", [t]))

  fun bexp_tr t =
        (case Term.strip_comb t of
           (Const ("_bexp_true", _), []) => K c_Bc $ (@{term True})
         | (Const ("_bexp_false", _), []) => K c_Bc $ (@{term False})
         | (Const ("_bexp_less", _), [a0, a2]) => K c_Less $ (aexp_tr a0) $ (aexp_tr a2)
         | (Const ("_bexp_eq", _), [a0, a2]) => K c_Eq $ (aexp_tr a0) $ (aexp_tr a2)
         | (Const ("_bexp_paren", _), [a1]) => bexp_tr a1
         | (Const ("_bexp_not", _), [a1]) => K c_Not $ (bexp_tr a1)
         | (Const ("_bexp_and", _), [a0, a2]) => K c_And $ (bexp_tr a0) $ (bexp_tr a2)
         | (Const ("_bexp_or", _), [a0, a2]) => K c_Or $ (bexp_tr a0) $ (bexp_tr a2)
         | _ => raise TERM ("Vimp_Grammar_Tr: bexp_tr", [t]))

  fun actuals_tr (Const ("_actuals_one", _) $ x) = K c_Cons $ (aexp_tr x) $ K c_Nil
    | actuals_tr (Const ("_actuals_cons", _) $ x $ rest) = K c_Cons $ (aexp_tr x) $ (actuals_tr rest)
    | actuals_tr t = raise TERM ("Vimp_Grammar_Tr: actuals_tr", [t])

  fun stmts_tr (Const ("_stmts_one", _) $ x) = stmt_tr x
    | stmts_tr (Const ("_stmts_seq", _) $ xs $ x) = K c_Seq $ (stmts_tr xs) $ (stmt_tr x)
    | stmts_tr t = raise TERM ("Vimp_Grammar_Tr: stmts_tr", [t])
  and stmts_opt_tr (Const ("_stmts_opt_none", _)) = K c_SKIP
    | stmts_opt_tr (Const ("_stmts_opt_some", _) $ s) = stmts_tr s
    | stmts_opt_tr t = raise TERM ("Vimp_Grammar_Tr: stmts_opt_tr", [t])
  and stmt_tr t =
        (case Term.strip_comb t of
           (Const ("_stmt_call0", _), [Free (x0, _)]) => K c_Call $ (K c_None) $ (HOLogic.mk_literal x0) $ K c_Nil
         | (Const ("_stmt_callret0", _), [Free (x0, _), Free (x2, _)]) => K c_Call $ ((K c_Some $ (HOLogic.mk_literal x0))) $ (HOLogic.mk_literal x2) $ K c_Nil
         | (Const ("_stmt_skip", _), []) => K c_SKIP
         | (Const ("_stmt_assign", _), [Free (x0, _), a2]) => K c_Assign $ (HOLogic.mk_literal x0) $ (aexp_tr a2)
         | (Const ("_stmt_random", _), [Free (x0, _)]) => K c_Random $ (HOLogic.mk_literal x0)
         | (Const ("_stmt_return", _), [a1]) => K c_Return $ ((K c_Some $ (aexp_tr a1)))
         | (Const ("_stmt_return0", _), []) => K c_Return $ (K c_None)
         | (Const ("_stmt_check", _), [a2]) => K c_Check $ (bexp_tr a2)
         | (Const ("_stmt_if", _), [a2, a5, a9]) => K c_If $ (bexp_tr a2) $ (stmts_opt_tr a5) $ (stmts_opt_tr a9)
         | (Const ("_stmt_while", _), [a2, a5]) => K c_While $ (bexp_tr a2) $ (stmts_opt_tr a5)
         | (Const ("_stmt_call", _), [Free (x0, _), a2]) => K c_Call $ (K c_None) $ (HOLogic.mk_literal x0) $ (actuals_tr a2)
         | (Const ("_stmt_callret", _), [Free (x0, _), Free (x2, _), a4]) => K c_Call $ ((K c_Some $ (HOLogic.mk_literal x0))) $ (HOLogic.mk_literal x2) $ (actuals_tr a4)
         | _ => raise TERM ("Vimp_Grammar_Tr: stmt_tr", [t]))

  fun formals_of (Const ("_formals_one", _) $ Free (x, _)) = [x]
    | formals_of (Const ("_formals_cons", _) $ Free (x, _) $ rest) = x :: formals_of rest
    | formals_of t = raise TERM ("Vimp_Grammar_Tr: formals_of", [t])

  fun names_of (Const ("_ids_one", _) $ Free (x, _)) = [x]
    | names_of (Const ("_ids_cons", _) $ Free (x, _) $ rest) = x :: names_of rest
    | names_of t = raise TERM ("Vimp_Grammar_Tr: names_of", [t])
end
\<close>

end
