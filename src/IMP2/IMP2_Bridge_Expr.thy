theory IMP2_Bridge_Expr
  imports IMP2_Proc "IMP2.Semantics"
begin

section \<open>Expression and state embedding into AFP IMP2\<close>

text \<open>
  One-way bridge: our structural expressions and store embed into AFP IMP2.
  The direction is strict (structural \<open>\<rightarrow>\<close> IMP2); we never read IMP2's
  reflected \<open>int => int => int\<close> operators back, so the analyzer stays
  executable.

  Two structural gaps are bridged here:
  \<^enum> Operators: our tags Plus/Minus/Times/Less/Eq/And/Or map forward to
    IMP2's reflected \<open>Binop (+)\<close>, \<open>Cmpop (<)\<close>, \<open>BBinop conj\<close>, ...
  \<^enum> State: our scalar store \<open>vname => int\<close> embeds into IMP2's array state
    \<open>vname => int => int\<close> as an index-agnostic constant array. Our expressions
    never index, so the array dimension is inert and the default scalar index
    (IMP2 uses \<open>N 0\<close>) never matters.

  Qualified names disambiguate three layers:
  \<^item> ours     : \<open>IMP2_Syntax.aexp/bexp\<close>, \<open>IMP2_Expr.aval/bval\<close>
  \<^item> Nipkow   : \<open>AExp.aexp/aval\<close>, \<open>BExp.bexp/bval\<close> (wrapped under BaseN/BaseB)
  \<^item> AFP IMP2 : \<open>Syntax.aexp/bexp\<close>, \<open>Semantics.aval/bval/state\<close>
\<close>

subsection \<open>State embedding and projection\<close>

(* Scalar store as an index-agnostic constant array. *)
definition embed :: "store => (vname => int => int)" where
  "embed s = (%x i. s x)"

(* State projection: read every array back at the default index. *)
definition proj0 :: "(vname => int => int) => store" where
  "proj0 S = (%x. S x 0)"

lemma proj0_embed: "proj0 (embed s) = s"
  by (simp add: proj0_def embed_def)

subsection \<open>Nipkow leaf expressions into AFP IMP2\<close>

(* BaseN/BaseB wrap whole Nipkow subtrees. *)
fun nip_aexp :: "AExp.aexp => Syntax.aexp" where
  "nip_aexp (AExp.N n)      = Syntax.N n"
| "nip_aexp (AExp.V x)      = Syntax.Vidx x (Syntax.N 0)"
| "nip_aexp (AExp.Plus a b) = Syntax.Binop (+) (nip_aexp a) (nip_aexp b)"

lemma aval_nip: "AExp.aval a s = Semantics.aval (nip_aexp a) (embed s)"
  by (induction a) (simp_all add: embed_def)

fun nip_bexp :: "BExp.bexp => Syntax.bexp" where
  "nip_bexp (BExp.Bc v)      = Syntax.Bc v"
| "nip_bexp (BExp.Not b)     = Syntax.Not (nip_bexp b)"
| "nip_bexp (BExp.And b1 b2) = Syntax.BBinop conj (nip_bexp b1) (nip_bexp b2)"
| "nip_bexp (BExp.Less a b)  = Syntax.Cmpop (<) (nip_aexp a) (nip_aexp b)"

lemma bval_nip: "BExp.bval b s = Semantics.bval (nip_bexp b) (embed s)"
  by (induction b) (simp_all add: aval_nip)

subsection \<open>Our extended expressions into AFP IMP2\<close>

fun to_imp2_aexp :: "IMP2_Syntax.aexp => Syntax.aexp" where
  "to_imp2_aexp (BaseN a)              = nip_aexp a"
| "to_imp2_aexp (IMP2_Syntax.Plus a b) = Syntax.Binop (+) (to_imp2_aexp a) (to_imp2_aexp b)"
| "to_imp2_aexp (Minus a b)            = Syntax.Binop (-) (to_imp2_aexp a) (to_imp2_aexp b)"
| "to_imp2_aexp (Times a b)            = Syntax.Binop times (to_imp2_aexp a) (to_imp2_aexp b)"

lemma aval_to_imp2: "IMP2_Expr.aval e s = Semantics.aval (to_imp2_aexp e) (embed s)"
  by (induction e) (simp_all add: aval_nip)

fun to_imp2_bexp :: "IMP2_Syntax.bexp => Syntax.bexp" where
  "to_imp2_bexp (BaseB b)              = nip_bexp b"
| "to_imp2_bexp (IMP2_Syntax.Not b)    = Syntax.Not (to_imp2_bexp b)"
| "to_imp2_bexp (IMP2_Syntax.And b1 b2) = Syntax.BBinop conj (to_imp2_bexp b1) (to_imp2_bexp b2)"
| "to_imp2_bexp (Or b1 b2)             = Syntax.BBinop disj (to_imp2_bexp b1) (to_imp2_bexp b2)"
| "to_imp2_bexp (IMP2_Syntax.Less a b) = Syntax.Cmpop (<) (to_imp2_aexp a) (to_imp2_aexp b)"
| "to_imp2_bexp (Eq a b)               = Syntax.Cmpop (=) (to_imp2_aexp a) (to_imp2_aexp b)"

lemma bval_to_imp2: "IMP2_Expr.bval e s = Semantics.bval (to_imp2_bexp e) (embed s)"
  by (induction e) (simp_all add: aval_to_imp2 bval_nip)

subsection \<open>Expression agreement under projection\<close>

text \<open>
  embed is not preserved by IMP2 array assignment: an assignment writes only
  index 0, so after one write the array is no longer the constant array embed
  produces. The right invariant for a command simulation is therefore the
  weaker projection relation \<open>proj0 S = s\<close>, not strict \<open>S = embed s\<close>.

  Our translated expressions only ever read index 0 (\<open>Vidx x (N 0)\<close>), so
  expression agreement holds under the projection relation alone. These
  generalise aval_to_imp2 / bval_to_imp2 (recovered by proj0_embed) and are the
  reusable core for a command/collecting simulation.
\<close>

lemma aval_nip_sim:
  "proj0 S = s ==> Semantics.aval (nip_aexp a) S = AExp.aval a s"
  by (induction a) (auto simp: proj0_def fun_eq_iff)

lemma aval_to_imp2_sim:
  "proj0 S = s ==> Semantics.aval (to_imp2_aexp e) S = IMP2_Expr.aval e s"
  by (induction e) (simp_all add: aval_nip_sim)

lemma bval_nip_sim:
  "proj0 S = s ==> Semantics.bval (nip_bexp b) S = BExp.bval b s"
  by (induction b) (simp_all add: aval_nip_sim)

lemma bval_to_imp2_sim:
  "proj0 S = s ==> Semantics.bval (to_imp2_bexp e) S = IMP2_Expr.bval e s"
  by (induction e) (simp_all add: aval_to_imp2_sim bval_nip_sim)

subsection \<open>Locals/globals split agrees with IMP2\<close>

text \<open>
  Our is_global (IMP2_Globals) matches AFP IMP2's is_global (Syntax) exactly:
  the empty name and names starting with 'G' are global, all others local.
  Hence combine_states / enter_state correspond on the nose under proj0, with no
  side condition on variable names.
\<close>

lemma is_global_eq: "Syntax.is_global x = IMP2_Globals.is_global x"
  by (cases x rule: Syntax.is_global.cases) (auto simp: is_global_def)

(* Projecting an IMP2 state combination at index 0 is our state combination. *)
lemma proj0_combine_states:
  "proj0 (Semantics.combine_states S T)
     = IMP2_Globals.combine_states (proj0 S) (proj0 T)"
  by (rule ext)
     (simp add: proj0_def Semantics.combine_states_def is_global_eq)

(* Projecting IMP2's scope-entry state recovers our enter_state. *)
lemma proj0_null_combine:
  "proj0 (Semantics.combine_states Semantics.null_state s) = enter_state (proj0 s)"
  by (rule ext)
     (simp add: proj0_def Semantics.combine_states_def Semantics.null_state_def
                enter_state_def is_global_eq)

subsection \<open>Executable examples\<close>

value "embed (\<lambda>_. 5::int) ''x'' 0"
value "proj0 (\<lambda>v (n::int). 7::int) ''x''"

end
