theory VIMP_Special
  imports VIMP_Expr VIMP_Globals VIMP_Typing
begin

section \<open>Special-call classification vocabulary\<close>

text \<open>
  \<open>special_call\<close> classifies analyzer-recognized special functions, the VIMP
  analogue of Goblint's library-function dispatch: a closed, VIMP-scoped
  enumeration (unlike Goblint's open library-function table) of the special
  operations VIMP source programs can invoke, kept separate from ordinary
  procedure calls so their abstract semantics need not simulate \<open>enter\<close>/
  \<open>body\<close>/\<open>return\<close>/\<open>combine_env\<close>/\<open>combine_assign\<close> for an operation that isn't
  a real activation.

  Classification is two-level, mirroring Goblint's name-to-descriptor-to-typed-
  value dispatch: \<open>special_table\<close> resolves a callee name to a \<open>special_desc\<close>
  (an arity/shape descriptor only, independent of any call site), and
  \<open>classify_special\<close> applies that descriptor to a call's actual arguments,
  producing the typed, argument-carrying \<open>special_call\<close> value or rejecting a
  shape mismatch. Consumers downstream of classification (the small-step
  semantics, the CFG compiler, each domain's abstract transfer) see the
  already-classified \<open>Min a b\<close> rather than re-deriving it from a name and a
  raw argument list, and never perform their own arity checks.

  \<open>Nondet_Int\<close> is an unconstrained nondeterministic integer, written to its
  destination. \<open>Min\<close>/\<open>Max\<close> are two-argument, value-producing operations whose
  arguments are evaluated in the caller's store at the call site, exactly like
  an ordinary procedure call's actuals.
\<close>

datatype special_desc = SD_Nondet_Int | SD_Min | SD_Max

datatype special_call =
    Nondet_Int
  | Min exp exp
  | Max exp exp

instance special_call :: countable
  by countable_datatype

fun classify_special :: "special_desc => exp list => special_call option" where
  "classify_special SD_Nondet_Int [] = Some Nondet_Int"
| "classify_special SD_Min [a, b] = Some (Min a b)"
| "classify_special SD_Max [a, b] = Some (Max a b)"
| "classify_special _ _ = None"

text \<open>
  \<open>special_result\<close> gives the concrete result value(s) of a classified special
  call in a store, shared by the source small-step semantics (\<open>pstep\<close>'s
  \<open>Special\<close> rule, in \<open>VIMP_Proc\<close>) and the compiled CFG's concrete semantics
  (\<open>special_step\<close>, in the CFG session), so the two concrete semantics cannot
  drift apart on what a special call computes. \<open>Nondet_Int\<close> admits every
  integer; \<open>Min\<close>/\<open>Max\<close> admit exactly one, the evaluated arithmetic
  minimum/maximum of their two arguments.
\<close>
fun special_result :: "tyenv => special_call => store => int => bool" where
  "special_result \<Gamma> Nondet_Int s v = True"
| "special_result \<Gamma> (Min a b) s v =
     (let k = opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))
      in v = min (taval \<Gamma> k a s) (taval \<Gamma> k b s))"
| "special_result \<Gamma> (Max a b) s v =
     (let k = opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))
      in v = max (taval \<Gamma> k a s) (taval \<Gamma> k b s))"

lemma special_result_ex [simp]: "\<exists>v. special_result \<Gamma> sc s v"
  by (cases sc) (auto simp: Let_def)

text \<open>
  \<open>special_mentions_global\<close> is \<open>special_call\<close>'s analogue of \<open>exp_mentions_global\<close>:
  whether evaluating the classified operation could read a global variable,
  needed wherever a special call's locality is at stake (mirroring how an
  ordinary assignment's RHS needs \<open>exp_mentions_global\<close>). \<open>Nondet_Int\<close> reads
  nothing, so it never mentions a global; \<open>Min\<close>/\<open>Max\<close> read exactly their two
  argument expressions.
\<close>
fun special_mentions_global :: "(vname => bool) => special_call => bool" where
  "special_mentions_global gs Nondet_Int = False"
| "special_mentions_global gs (Min a b) =
     (exp_mentions_global gs a \<or> exp_mentions_global gs b)"
| "special_mentions_global gs (Max a b) =
     (exp_mentions_global gs a \<or> exp_mentions_global gs b)"

text \<open>
  \<open>special_table\<close> is VIMP's closed analogue of Goblint's open library-function
  classification: a name-based lookup from a call's callee to its special
  descriptor, checked at the same point Goblint's own frontend recognizes a
  call target as special rather than a declared procedure -- not a dedicated
  keyword or AST constructor. Ordinary call syntax parses
  \<open>x := __voblint_nondet_int()\<close> or \<open>x := min(a, b)\<close> exactly like any other
  call; classification happens here, downstream of parsing, and resolves only
  the name to a descriptor -- \<open>classify_special\<close> above then applies that
  descriptor to the call's actuals. Every \<open>special_pname_*\<close> below is an
  ordinary lexable identifier (unlike VIMP_Proc's \<open>ret_var\<close>), so a source
  program could otherwise declare a colliding procedure of the same name --
  program well-formedness (\<open>wf_source_program\<close>, in \<open>VIMP_Proc\<close>) rejects that
  explicitly rather than letting a declared procedure be silently shadowed by
  special-call semantics.
\<close>
definition special_pname_nondet_int :: pname where
  "special_pname_nondet_int = STR ''__voblint_nondet_int''"

definition special_pname_min :: pname where
  "special_pname_min = STR ''min''"

definition special_pname_max :: pname where
  "special_pname_max = STR ''max''"

definition special_table :: "pname => special_desc option" where
  "special_table p =
     (if p = special_pname_nondet_int then Some SD_Nondet_Int
      else if p = special_pname_min then Some SD_Min
      else if p = special_pname_max then Some SD_Max
      else None)"

end
