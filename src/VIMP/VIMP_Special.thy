theory VIMP_Special
  imports VIMP_Expr VIMP_Globals VIMP_Typing VIMP_Elaborated
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

text \<open>
  A classified special call is already elaborated: its operands are
  \<^typ>\<open>texp\<close>s and it carries the \<^typ>\<open>ikind\<close> its destination was
  declared at, so every consumer downstream of classification -- the source
  small-step semantics, the compiled CFG's own step, each domain's abstract
  transfer -- reproduces the whole write, destination conversion included,
  with no typing environment in hand. This matches the \<open>EA_Ret\<close> design the
  CFG session already uses for a return kind: the kind is resolved once,
  where the source declaration is in scope, and baked in.
\<close>

datatype special_call =
    Nondet_Int (special_dest_kind: ikind)
  | Min (special_dest_kind: ikind) texp texp
  | Max (special_dest_kind: ikind) texp texp

instance special_call :: countable
  by countable_datatype

text \<open>
  \<open>classify_special \<Gamma> dk\<close> applies a descriptor to a call's actual
  arguments at destination kind \<open>dk\<close>. \<open>Min\<close>/\<open>Max\<close> elaborate both operands
  at the one kind the comparison relates them at (\<^const>\<open>kjoin\<close> of the two
  synthesized kinds, exactly as \<^const>\<open>taval\<close> types a \<open>Less\<close>), and the
  destination kind is kept separately because the conversion applies to the
  \<open>min\<close>/\<open>max\<close> result, not to either operand.
\<close>

definition special_arg_kind :: "tyenv => exp => exp => ikind" where
  "special_arg_kind \<Gamma> a b = opk (kjoin (esyn \<Gamma> a) (esyn \<Gamma> b))"

fun classify_special :: "tyenv => ikind => special_desc => exp list => special_call option" where
  "classify_special \<Gamma> dk SD_Nondet_Int [] = Some (Nondet_Int dk)"
| "classify_special \<Gamma> dk SD_Min [a, b] =
     Some (Min dk (elaborate \<Gamma> (special_arg_kind \<Gamma> a b) a)
                  (elaborate \<Gamma> (special_arg_kind \<Gamma> a b) b))"
| "classify_special \<Gamma> dk SD_Max [a, b] =
     Some (Max dk (elaborate \<Gamma> (special_arg_kind \<Gamma> a b) a)
                  (elaborate \<Gamma> (special_arg_kind \<Gamma> a b) b))"
| "classify_special \<Gamma> dk _ _ = None"

text \<open>
  Whether a descriptor accepts a call's actual-argument list is a pure arity
  question, independent of any typing environment or destination kind, so
  well-formedness checks go through \<open>special_arity_ok\<close> rather than through
  \<^const>\<open>classify_special\<close> itself.
\<close>

fun special_arity_ok :: "special_desc => exp list => bool" where
  "special_arity_ok SD_Nondet_Int [] = True"
| "special_arity_ok SD_Min [a, b] = True"
| "special_arity_ok SD_Max [a, b] = True"
| "special_arity_ok _ _ = False"

lemma classify_special_None_iff [simp]:
  "classify_special \<Gamma> dk desc es = None \<longleftrightarrow> \<not> special_arity_ok desc es"
  by (rule classify_special.induct[of "\<lambda>_ _ d e. classify_special \<Gamma> dk d e = None
        \<longleftrightarrow> \<not> special_arity_ok d e" \<Gamma> dk desc es]) simp_all

lemma special_arity_okD:
  "special_arity_ok desc es \<Longrightarrow> \<exists>sc. classify_special \<Gamma> dk desc es = Some sc"
  by (cases "classify_special \<Gamma> dk desc es") simp_all

text \<open>
  \<open>special_result\<close> gives the concrete result value(s) of a classified special
  call in a store, shared by the source small-step semantics (\<open>pstep\<close>'s
  \<open>Special\<close> rule, in \<open>VIMP_Proc\<close>) and the compiled CFG's concrete semantics
  (\<open>special_step\<close>, in the CFG session), so the two concrete semantics cannot
  drift apart on what a special call computes. It ranges over the value
  actually stored, destination conversion included.
\<close>
fun special_result :: "special_call => store => int => bool" where
  "special_result (Nondet_Int k) s v = (v \<in> ik_range k)"
| "special_result (Min k a b) s v = (v = ik_norm k (min (teval a s) (teval b s)))"
| "special_result (Max k a b) s v = (v = ik_norm k (max (teval a s) (teval b s)))"

text \<open>\<open>Nondet_Int\<close> admits exactly the destination kind's representable
  values -- the image of \<^const>\<open>ik_norm\<close> at that kind, so no narrower than
  an unconstrained integer normed on the way in -- and \<open>Min\<close>/\<open>Max\<close> admit
  exactly one, their converted arithmetic minimum/maximum.\<close>

lemma special_result_ex [simp]: "\<exists>v. special_result sc s v"
proof (cases sc)
  case (Nondet_Int k)
  have "special_result sc s 0" using Nondet_Int by simp
  then show ?thesis ..
qed auto

lemma special_result_in_range:
  "special_result sc s v \<Longrightarrow> v \<in> ik_range (special_dest_kind sc)"
  by (cases sc) auto

text \<open>
  A classified call's destination kind is the one classification was handed,
  so a special write lands in the destination variable's declared range --
  the store-typedness step \<open>pstep\<close>'s \<open>Special\<close> rule needs now that
  the conversion is inside \<^const>\<open>special_result\<close> rather than applied
  afterwards.
\<close>

lemma classify_special_dest_kind:
  "classify_special \<Gamma> dk desc es = Some sc \<Longrightarrow> special_dest_kind sc = dk"
  by (induction \<Gamma> dk desc es rule: classify_special.induct) auto

lemma special_result_dest_range:
  assumes "classify_special \<Gamma> dk desc es = Some sc" and "special_result sc s v"
  shows "v \<in> ik_range dk"
  using assms special_result_in_range classify_special_dest_kind by fastforce

lemma styped_update_special [intro]:
  assumes "styped \<Gamma> s"
    and "classify_special \<Gamma> (\<Gamma> x) desc es = Some sc"
    and "special_result sc s v"
  shows "styped \<Gamma> (s(x := v))"
  using assms by (blast intro: styped_update special_result_dest_range)

text \<open>
  \<open>special_mentions_global\<close> is \<open>special_call\<close>'s analogue of \<open>exp_mentions_global\<close>:
  whether evaluating the classified operation could read a global variable,
  needed wherever a special call's locality is at stake (mirroring how an
  ordinary assignment's RHS needs \<open>exp_mentions_global\<close>). \<open>Nondet_Int\<close> reads
  nothing, so it never mentions a global; \<open>Min\<close>/\<open>Max\<close> read exactly their two
  argument expressions.
\<close>
fun special_mentions_global :: "(vname => bool) => special_call => bool" where
  "special_mentions_global gs (Nondet_Int _) = False"
| "special_mentions_global gs (Min _ a b) =
     (texp_mentions_global gs a \<or> texp_mentions_global gs b)"
| "special_mentions_global gs (Max _ a b) =
     (texp_mentions_global gs a \<or> texp_mentions_global gs b)"

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
