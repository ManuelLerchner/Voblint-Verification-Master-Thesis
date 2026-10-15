theory Core_Exp
  imports Var_Id
begin

section \<open>Typed expressions\<close>

text \<open>
  The untyped evaluator \<^const>\<open>src_aval\<close> computes over mathematical integers. Under
  machine kinds an expression's value depends on the kind each operation computes at:
  \<open>200 + 100 < 250\<close> holds over \<^typ>\<open>int\<close> but fails when the sum wraps at an
  8-bit kind. This theory states that meaning twice. \<open>src_eval\<close> reads it off a source
  expression and a kind for every name, in the shape the C standard describes it.
  \<open>eval\<close> evaluates a typed expression whose nodes already carry their kinds, which
  is what an analyzer consumes. Elaboration translates the first into the second, and
  @{text eval_elaborate} shows that it preserves the meaning.
\<close>

subsection \<open>Operators\<close>

datatype aop = AAdd | ASub | AMul | ADiv | AMod
datatype cop = CLt | CLe | CGt | CGe | CEq | CNe

text \<open>Division and remainder keep VIMP's total conventions for a zero divisor
  (@{const c_div}, @{const c_mod}). On a nonzero divisor they truncate toward zero, as
  C does, and on the nonnegative values of an unsigned kind they are floor division.\<close>

fun aop_eval :: "aop \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "aop_eval AAdd a b = a + b"
| "aop_eval ASub a b = a - b"
| "aop_eval AMul a b = a * b"
| "aop_eval ADiv a b = c_div a b"
| "aop_eval AMod a b = c_mod a b"

fun cop_eval :: "cop \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "cop_eval CLt a b = (a < b)"
| "cop_eval CLe a b = (a \<le> b)"
| "cop_eval CGt a b = (a > b)"
| "cop_eval CGe a b = (a \<ge> b)"
| "cop_eval CEq a b = (a = b)"
| "cop_eval CNe a b = (a \<noteq> b)"

lemma ik_norm_bool [simp]: "ik_norm ik (if P then 1 else 0) = (if P then 1 else 0)"
  by simp

subsection \<open>The source-level typed semantics\<close>

text \<open>
  An unsuffixed decimal constant takes the first of \<^const>\<open>I32\<close> and
  \<^const>\<open>I64\<close> that represents its magnitude (ISO/IEC 9899 6.4.4.1p5); the frontend
  folds a sign into the literal, and C types the unsigned token. A literal outside
  \<^const>\<open>I64\<close> has no type in that list, and well-formedness rejects it
  (\<^const>\<open>lits_fit\<close>). \<open>esyn\<close> is the kind an expression has of its own accord: a
  variable's kind, a literal's kind, the usual arithmetic conversion of an arithmetic
  operator's operands, and \<^const>\<open>I32\<close> for the truth value of a comparison or a
  logical operator.
\<close>

definition ik_of_lit :: "int \<Rightarrow> ikind" where
  "ik_of_lit n = (if \<bar>n\<bar> \<le> ik_max I32 then I32 else I64)"

fun esyn :: "(vname \<Rightarrow> ikind) \<Rightarrow> src_exp \<Rightarrow> ikind" where
  "esyn \<Gamma> (N n) = ik_of_lit n"
| "esyn \<Gamma> (V x) = \<Gamma> x"
| "esyn \<Gamma> (Plus a b) = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b)"
| "esyn \<Gamma> (Minus a b) = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b)"
| "esyn \<Gamma> (Times a b) = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b)"
| "esyn \<Gamma> (Div a b) = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b)"
| "esyn \<Gamma> (Mod a b) = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b)"
| "esyn \<Gamma> (Less a b) = I32"
| "esyn \<Gamma> (LessEq a b) = I32"
| "esyn \<Gamma> (Greater a b) = I32"
| "esyn \<Gamma> (GreaterEq a b) = I32"
| "esyn \<Gamma> (NotEq a b) = I32"
| "esyn \<Gamma> (Eq a b) = I32"
| "esyn \<Gamma> (Not a) = I32"
| "esyn \<Gamma> (And a b) = I32"
| "esyn \<Gamma> (Or a b) = I32"
| "esyn \<Gamma> (Cast ik a) = ik"

text \<open>
  \<open>src_eval \<Gamma> ik e s\<close> is the value of \<open>e\<close> converted to kind \<open>ik\<close>. An arithmetic
  operator converts both operands to their common kind \<open>k\<close>, computes there with
  wraparound, and only then converts to \<open>ik\<close>. A comparison converts its operands
  the same way and yields \<open>0\<close> or \<open>1\<close>. A logical operator tests each operand at its
  own kind. Computing an inner operation at the context's kind instead would give
  \<open>4294967295 < u + 1\<close> the wrong value for an unsigned 32-bit \<open>u\<close>: the comparison
  agrees on 64 bits, but the sum wraps at 32 bits before the comparison sees it.
\<close>

definition arith_at :: "ikind \<Rightarrow> ikind \<Rightarrow> aop \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "arith_at ik k op a b = ik_norm ik (ik_norm k (aop_eval op a b))"

fun src_eval :: "(vname \<Rightarrow> ikind) \<Rightarrow> ikind \<Rightarrow> src_exp \<Rightarrow> src_store \<Rightarrow> int" where
  "src_eval \<Gamma> ik (N n) s = ik_norm ik n"
| "src_eval \<Gamma> ik (V x) s = ik_norm ik (ik_norm (\<Gamma> x) (s x))"
| "src_eval \<Gamma> ik (Plus a b) s = (let k = esyn \<Gamma> (Plus a b) in
     arith_at ik k AAdd (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s))"
| "src_eval \<Gamma> ik (Minus a b) s = (let k = esyn \<Gamma> (Minus a b) in
     arith_at ik k ASub (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s))"
| "src_eval \<Gamma> ik (Times a b) s = (let k = esyn \<Gamma> (Times a b) in
     arith_at ik k AMul (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s))"
| "src_eval \<Gamma> ik (Div a b) s = (let k = esyn \<Gamma> (Div a b) in
     arith_at ik k ADiv (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s))"
| "src_eval \<Gamma> ik (Mod a b) s = (let k = esyn \<Gamma> (Mod a b) in
     arith_at ik k AMod (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s))"
| "src_eval \<Gamma> ik (Less a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CLt (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s) then 1 else 0)"
| "src_eval \<Gamma> ik (LessEq a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CLe (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s) then 1 else 0)"
| "src_eval \<Gamma> ik (Greater a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CGt (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s) then 1 else 0)"
| "src_eval \<Gamma> ik (GreaterEq a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CGe (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s) then 1 else 0)"
| "src_eval \<Gamma> ik (NotEq a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CNe (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s) then 1 else 0)"
| "src_eval \<Gamma> ik (Eq a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CEq (src_eval \<Gamma> k a s) (src_eval \<Gamma> k b s) then 1 else 0)"
| "src_eval \<Gamma> ik (Not a) s = (if truthy (src_eval \<Gamma> (esyn \<Gamma> a) a s) then 0 else 1)"
| "src_eval \<Gamma> ik (And a b) s =
     (if truthy (src_eval \<Gamma> (esyn \<Gamma> a) a s) \<and> truthy (src_eval \<Gamma> (esyn \<Gamma> b) b s) then 1 else 0)"
| "src_eval \<Gamma> ik (Or a b) s =
     (if truthy (src_eval \<Gamma> (esyn \<Gamma> a) a s) \<or> truthy (src_eval \<Gamma> (esyn \<Gamma> b) b s) then 1 else 0)"
| "src_eval \<Gamma> ik (Cast k a) s = ik_norm ik (ik_norm k (src_eval \<Gamma> (esyn \<Gamma> a) a s))"

subsection \<open>Typed expressions and their evaluator\<close>

text \<open>
  A typed expression carries the kind each arithmetic node computes at and names
  variables by identity. \<open>TCast\<close>, the one node without a source counterpart, is a
  conversion, in the role of CIL's \<open>CastE\<close>. \<open>eval\<close> needs no kind environment: every
  kind it uses is on the node. A variable read does not convert, because a typed store
  already holds a value of the variable's kind.
\<close>

datatype exp =
    TN ikind int
  | TVar ikind var_id
  | TArith ikind aop exp exp
  | TCast ikind exp
  | TCmp cop exp exp
  | TNot exp
  | TAnd exp exp
  | TOr exp exp

derive linorder aop
derive linorder cop
derive linorder exp

fun eval :: "exp \<Rightarrow> store \<Rightarrow> int" where
  "eval (TN ik n) t = ik_norm ik n"
| "eval (TVar ik v) t = t v"
| "eval (TArith ik op a b) t = ik_norm ik (aop_eval op (eval a t) (eval b t))"
| "eval (TCast ik a) t = ik_norm ik (eval a t)"
| "eval (TCmp op a b) t = (if cop_eval op (eval a t) (eval b t) then 1 else 0)"
| "eval (TNot a) t = (if truthy (eval a t) then 0 else 1)"
| "eval (TAnd a b) t = (if truthy (eval a t) \<and> truthy (eval b t) then 1 else 0)"
| "eval (TOr a b) t = (if truthy (eval a t) \<or> truthy (eval b t) then 1 else 0)"

text \<open>The kind a node produces: the one an arithmetic or literal node carries, the
  target of a conversion, and \<^const>\<open>I32\<close> for a truth value.\<close>

fun exp_kind :: "exp \<Rightarrow> ikind" where
  "exp_kind (TN ik _) = ik"
| "exp_kind (TVar ik _) = ik"
| "exp_kind (TArith ik _ _ _) = ik"
| "exp_kind (TCast ik _) = ik"
| "exp_kind (TCmp _ _ _) = I32"
| "exp_kind (TNot _) = I32"
| "exp_kind (TAnd _ _) = I32"
| "exp_kind (TOr _ _) = I32"

text \<open>A typed expression is well-typed when its kinds agree with each other and with
  the environment: an arithmetic node's operands carry its kind, a comparison's two
  operands share one, and a variable read carries the variable's kind. Abstract
  transfers that read an operand's kind off the operand rely on exactly this.\<close>

fun wt_exp :: "kenv \<Rightarrow> exp \<Rightarrow> bool" where
  "wt_exp \<kappa> (TN ik n) \<longleftrightarrow> True"
| "wt_exp \<kappa> (TVar ik v) \<longleftrightarrow> \<kappa> v = ik"
| "wt_exp \<kappa> (TArith ik op a b) \<longleftrightarrow>
     exp_kind a = ik \<and> exp_kind b = ik \<and> wt_exp \<kappa> a \<and> wt_exp \<kappa> b"
| "wt_exp \<kappa> (TCast ik a) \<longleftrightarrow> wt_exp \<kappa> a"
| "wt_exp \<kappa> (TCmp op a b) \<longleftrightarrow> exp_kind a = exp_kind b \<and> wt_exp \<kappa> a \<and> wt_exp \<kappa> b"
| "wt_exp \<kappa> (TNot a) \<longleftrightarrow> wt_exp \<kappa> a"
| "wt_exp \<kappa> (TAnd a b) \<longleftrightarrow> wt_exp \<kappa> a \<and> wt_exp \<kappa> b"
| "wt_exp \<kappa> (TOr a b) \<longleftrightarrow> wt_exp \<kappa> a \<and> wt_exp \<kappa> b"

theorem eval_in_range:
  assumes "wt_exp \<kappa> e" and "all_in_kinds \<kappa> t"
  shows "eval e t \<in> ik_range (exp_kind e)"
  using assms by (cases e) (auto dest: all_in_kindsD simp del: ik_range_iff)

subsection \<open>Elaboration\<close>

text \<open>
  \<open>elaborate \<rho> \<kappa> ik e\<close> translates a source expression of one procedure, whose names
  \<open>\<rho>\<close> resolves, into a typed expression whose value has kind \<open>ik\<close>. It follows
  \<^const>\<open>src_eval\<close> node for node and inserts a conversion only where a value reaches a
  context at another kind. A conversion to the kind a value already has is left out:
  it would change no value, but a domain without magnitudes, such as Sign, could only
  answer top for it.
\<close>

definition cast_to :: "ikind \<Rightarrow> ikind \<Rightarrow> exp \<Rightarrow> exp" where
  "cast_to ik k a = (if ik = k then a else TCast ik a)"

fun elaborate :: "(vname \<Rightarrow> var_id) \<Rightarrow> kenv \<Rightarrow> ikind \<Rightarrow> src_exp \<Rightarrow> exp" where
  "elaborate \<rho> \<kappa> ik (N n) = TN ik n"
| "elaborate \<rho> \<kappa> ik (V x) = cast_to ik (\<kappa> (\<rho> x)) (TVar (\<kappa> (\<rho> x)) (\<rho> x))"
| "elaborate \<rho> \<kappa> ik (Plus a b) = (let k = esyn (\<kappa> \<circ> \<rho>) (Plus a b) in
     cast_to ik k (TArith k AAdd (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Minus a b) = (let k = esyn (\<kappa> \<circ> \<rho>) (Minus a b) in
     cast_to ik k (TArith k ASub (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Times a b) = (let k = esyn (\<kappa> \<circ> \<rho>) (Times a b) in
     cast_to ik k (TArith k AMul (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Div a b) = (let k = esyn (\<kappa> \<circ> \<rho>) (Div a b) in
     cast_to ik k (TArith k ADiv (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Mod a b) = (let k = esyn (\<kappa> \<circ> \<rho>) (Mod a b) in
     cast_to ik k (TArith k AMod (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Less a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     cast_to ik I32 (TCmp CLt (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (LessEq a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     cast_to ik I32 (TCmp CLe (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Greater a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     cast_to ik I32 (TCmp CGt (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (GreaterEq a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     cast_to ik I32 (TCmp CGe (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (NotEq a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     cast_to ik I32 (TCmp CNe (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Eq a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     cast_to ik I32 (TCmp CEq (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Not a) =
     cast_to ik I32 (TNot (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) a) a))"
| "elaborate \<rho> \<kappa> ik (And a b) = cast_to ik I32
     (TAnd (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) a) a) (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) b) b))"
| "elaborate \<rho> \<kappa> ik (Or a b) = cast_to ik I32
     (TOr (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) a) a) (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) b) b))"
| "elaborate \<rho> \<kappa> ik (Cast k a) =
     cast_to ik k (TCast k (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) a) a))"

text \<open>A context without a kind of its own, such as a branch condition, evaluates an
  expression at the kind it synthesizes.\<close>

definition elaborate_syn :: "(vname \<Rightarrow> var_id) \<Rightarrow> kenv \<Rightarrow> src_exp \<Rightarrow> exp" where
  "elaborate_syn \<rho> \<kappa> e = elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) e) e"

lemma exp_kind_cast_to [simp]:
  "exp_kind (cast_to ik k a) = (if ik = k then exp_kind a else ik)"
  by (simp add: cast_to_def)

lemma exp_kind_elaborate [simp]: "exp_kind (elaborate \<rho> \<kappa> ik e) = ik"
  by (cases e) (simp_all add: Let_def)

theorem wt_exp_elaborate: "wt_exp \<kappa> (elaborate \<rho> \<kappa> ik e)"
  by (induction e arbitrary: ik) (simp_all add: Let_def cast_to_def)

text \<open>
  Elaboration preserves the meaning. The typed store \<open>t\<close> holds a value for every
  identity, and the procedure sees it through its resolution, as \<open>t \<circ> \<rho>\<close>. The premise
  that \<open>t\<close> is typed is used at one place: \<^const>\<open>src_eval\<close> reads a variable at its own
  kind, \<^const>\<open>eval\<close> reads the stored value directly, and the two agree because the
  stored value already lies in that kind's range.
\<close>

theorem eval_elaborate:
  assumes "all_in_kinds \<kappa> t"
  shows "eval (elaborate \<rho> \<kappa> ik e) t = src_eval (\<kappa> \<circ> \<rho>) ik e (t \<circ> \<rho>)"
proof -
  have var: "ik_norm (\<kappa> v) (t v) = t v" for v
    by (rule ik_norm_id [OF all_in_kindsD [OF assms]])
  show ?thesis
    by (induction e arbitrary: ik) (simp_all add: Let_def cast_to_def arith_at_def var)
qed

corollary eval_elaborate_syn:
  assumes "all_in_kinds \<kappa> t"
  shows "eval (elaborate_syn \<rho> \<kappa> e) t = src_eval (\<kappa> \<circ> \<rho>) (esyn (\<kappa> \<circ> \<rho>) e) e (t \<circ> \<rho>)"
  using eval_elaborate [OF assms] by (simp add: elaborate_syn_def)

text \<open>The identities a typed expression reads.\<close>

fun exp_vars :: "exp \<Rightarrow> var_id set" where
  "exp_vars (TN _ _) = {}"
| "exp_vars (TVar _ v) = {v}"
| "exp_vars (TArith _ _ a b) = exp_vars a \<union> exp_vars b"
| "exp_vars (TCast _ a) = exp_vars a"
| "exp_vars (TCmp _ a b) = exp_vars a \<union> exp_vars b"
| "exp_vars (TNot a) = exp_vars a"
| "exp_vars (TAnd a b) = exp_vars a \<union> exp_vars b"
| "exp_vars (TOr a b) = exp_vars a \<union> exp_vars b"

lemma exp_vars_elaborate: "exp_vars (elaborate \<rho> \<kappa> ik e) \<subseteq> range \<rho>"
  by (induction e arbitrary: ik) (auto simp: Let_def cast_to_def)

text \<open>A conversion to a kind whose range contains the source kind's range changes no
  value.\<close>

definition ik_widens :: "ikind \<Rightarrow> ikind \<Rightarrow> bool" where
  "ik_widens k ik \<longleftrightarrow> ik_min ik \<le> ik_min k \<and> ik_max k \<le> ik_max ik"

subsection \<open>Erasure\<close>

text \<open>
  Erasure drops the kinds and the conversions and names every identity by its source
  name. It recovers the expression elaboration started from. It belongs to no
  semantics: \<^const>\<open>eval\<close> and \<^const>\<open>src_aval\<close> differ wherever a kind wraps, so the
  untyped meaning of the erased expression is not the typed meaning of the original.
\<close>

fun aop_exp :: "aop \<Rightarrow> src_exp \<Rightarrow> src_exp \<Rightarrow> src_exp" where
  "aop_exp AAdd = Plus" | "aop_exp ASub = Minus" | "aop_exp AMul = Times"
| "aop_exp ADiv = Div" | "aop_exp AMod = Mod"

fun cop_exp :: "cop \<Rightarrow> src_exp \<Rightarrow> src_exp \<Rightarrow> src_exp" where
  "cop_exp CLt = Less" | "cop_exp CLe = LessEq" | "cop_exp CGt = Greater"
| "cop_exp CGe = GreaterEq" | "cop_exp CEq = Eq" | "cop_exp CNe = NotEq"

fun exp_erase :: "exp \<Rightarrow> src_exp" where
  "exp_erase (TN _ n) = N n"
| "exp_erase (TVar _ v) = V (var_name v)"
| "exp_erase (TArith _ op a b) = aop_exp op (exp_erase a) (exp_erase b)"
| "exp_erase (TCast _ a) = exp_erase a"
| "exp_erase (TCmp op a b) = cop_exp op (exp_erase a) (exp_erase b)"
| "exp_erase (TNot a) = Not (exp_erase a)"
| "exp_erase (TAnd a b) = And (exp_erase a) (exp_erase b)"
| "exp_erase (TOr a b) = Or (exp_erase a) (exp_erase b)"

text \<open>Erasure drops every conversion, including one the source wrote, so it recovers
  an expression without explicit casts.\<close>

fun cast_free :: "src_exp \<Rightarrow> bool" where
  "cast_free (Cast _ _) \<longleftrightarrow> False"
| "cast_free (Plus a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (Minus a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (Times a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (Div a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (Mod a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (Less a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (LessEq a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (Greater a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (GreaterEq a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (NotEq a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (Eq a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (Not a) \<longleftrightarrow> cast_free a"
| "cast_free (And a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free (Or a b) \<longleftrightarrow> cast_free a \<and> cast_free b"
| "cast_free _ \<longleftrightarrow> True"

theorem exp_erase_elaborate:
  assumes "\<And>x. var_name (\<rho> x) = x" and "cast_free e"
  shows "exp_erase (elaborate \<rho> \<kappa> ik e) = e"
  using assms(2) by (induction e arbitrary: ik) (simp_all add: Let_def cast_to_def assms(1))

end
