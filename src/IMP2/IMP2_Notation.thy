theory IMP2_Notation
  imports IMP2_Proc
begin

text \<open>
  Tier-3 IMP2 quotation bracket: @{text "IMP { \<dots> }"} produces an
  @{type IMP2_Proc.com} without HOL string quotes or qualified constructor names.

  Inside the bracket, bare identifiers become @{const V} literals (HOL string literals via @{type vname});
  numerals become @{const N}; @{text "_ + _ / _ - _ / _ * _"} map to
  @{const Plus}/@{const Minus}/@{const Times}; @{text "_ < _ / _ == _"} to
  @{const Less}/@{const Eq}; @{text "true/false"} to @{const Bc}.

  Example:
  @{verbatim [display]
   "definition loop_prog :: IMP2_Proc.com where
      \"loop_prog = IMP {
         x := 0;
         while x < 20 { x := x + 1 }
       }\""}
\<close>

nonterminal imp2_com
nonterminal imp2_aexp
nonterminal imp2_bexp

syntax
  "_IMP2"        :: "imp2_com \<Rightarrow> IMP2_Proc.com"              ("IMP { _ }")

  "_imp2_skip"   :: imp2_com                                  ("skip")
  "_imp2_assign" :: "id \<Rightarrow> imp2_aexp \<Rightarrow> imp2_com"            ("_ := _"                 [900, 61] 61)
  "_imp2_seq"    :: "imp2_com \<Rightarrow> imp2_com \<Rightarrow> imp2_com"       ("_; _"                   [60, 61] 60)
  "_imp2_if"     :: "imp2_bexp \<Rightarrow> imp2_com \<Rightarrow> imp2_com \<Rightarrow> imp2_com"
                                                               ("if _ { _ } else { _ }" [0, 0, 61] 61)
  "_imp2_while"  :: "imp2_bexp \<Rightarrow> imp2_com \<Rightarrow> imp2_com"      ("while _ { _ }"          [0, 61] 61)
  "_imp2_scope"  :: "imp2_com \<Rightarrow> imp2_com"                   ("scope { _ }"            [61] 61)
  "_imp2_call"   :: "id \<Rightarrow> imp2_com"                         ("call _"                 [1000] 61)

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
  in
    [("_IMP2", fn _ => fn [t] => com_tr t | _ => raise Match)]
  end
\<close>

end
