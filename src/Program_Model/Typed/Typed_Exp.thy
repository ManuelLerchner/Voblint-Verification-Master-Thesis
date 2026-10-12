theory Typed_Exp
  imports Var_Id
begin

section \<open>Typed expressions\<close>

text \<open>
  The untyped evaluator \<^const>\<open>aval\<close> computes over mathematical integers. Under
  machine kinds an expression's value depends on the kind each operation computes at:
  \<open>200 + 100 < 250\<close> holds over \<^typ>\<open>int\<close> but fails when the sum wraps at an
  8-bit kind. This theory states that meaning twice. \<open>taval\<close> reads it off a source
  expression and a kind for every name, in the shape the C standard describes it.
  \<open>teval\<close> evaluates a typed expression whose nodes already carry their kinds, which
  is what an analyzer consumes. Elaboration translates the first into the second, and
  @{text teval_elaborate} shows that it preserves the meaning.
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
  folds a sign into the literal, and C types the unsigned token. \<open>esyn\<close> is the kind
  an expression has of its own accord: a variable's kind, a literal's kind, the usual
  arithmetic conversion of an arithmetic operator's operands, and \<^const>\<open>I32\<close> for
  the truth value of a comparison or a logical operator.
\<close>

definition ik_of_lit :: "int \<Rightarrow> ikind" where
  "ik_of_lit n = (if \<bar>n\<bar> \<le> ik_max I32 then I32 else I64)"

fun esyn :: "(vname \<Rightarrow> ikind) \<Rightarrow> exp \<Rightarrow> ikind" where
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
  \<open>taval \<Gamma> ik e s\<close> is the value of \<open>e\<close> converted to kind \<open>ik\<close>. An arithmetic
  operator converts both operands to their common kind \<open>k\<close>, computes there with
  wraparound, and only then converts to \<open>ik\<close>. A comparison converts its operands
  the same way and yields \<open>0\<close> or \<open>1\<close>. A logical operator tests each operand at its
  own kind. Computing an inner operation at the context's kind instead would give
  \<open>4294967295 < u + 1\<close> the wrong value for an unsigned 32-bit \<open>u\<close>: the comparison
  agrees on 64 bits, but the sum wraps at 32 bits before the comparison sees it.
\<close>

definition arith_at :: "ikind \<Rightarrow> ikind \<Rightarrow> aop \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "arith_at ik k op a b = ik_norm ik (ik_norm k (aop_eval op a b))"

fun taval :: "(vname \<Rightarrow> ikind) \<Rightarrow> ikind \<Rightarrow> exp \<Rightarrow> store \<Rightarrow> int" where
  "taval \<Gamma> ik (N n) s = ik_norm ik n"
| "taval \<Gamma> ik (V x) s = ik_norm ik (ik_norm (\<Gamma> x) (s x))"
| "taval \<Gamma> ik (Plus a b) s = (let k = esyn \<Gamma> (Plus a b) in
     arith_at ik k AAdd (taval \<Gamma> k a s) (taval \<Gamma> k b s))"
| "taval \<Gamma> ik (Minus a b) s = (let k = esyn \<Gamma> (Minus a b) in
     arith_at ik k ASub (taval \<Gamma> k a s) (taval \<Gamma> k b s))"
| "taval \<Gamma> ik (Times a b) s = (let k = esyn \<Gamma> (Times a b) in
     arith_at ik k AMul (taval \<Gamma> k a s) (taval \<Gamma> k b s))"
| "taval \<Gamma> ik (Div a b) s = (let k = esyn \<Gamma> (Div a b) in
     arith_at ik k ADiv (taval \<Gamma> k a s) (taval \<Gamma> k b s))"
| "taval \<Gamma> ik (Mod a b) s = (let k = esyn \<Gamma> (Mod a b) in
     arith_at ik k AMod (taval \<Gamma> k a s) (taval \<Gamma> k b s))"
| "taval \<Gamma> ik (Less a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CLt (taval \<Gamma> k a s) (taval \<Gamma> k b s) then 1 else 0)"
| "taval \<Gamma> ik (LessEq a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CLe (taval \<Gamma> k a s) (taval \<Gamma> k b s) then 1 else 0)"
| "taval \<Gamma> ik (Greater a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CGt (taval \<Gamma> k a s) (taval \<Gamma> k b s) then 1 else 0)"
| "taval \<Gamma> ik (GreaterEq a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CGe (taval \<Gamma> k a s) (taval \<Gamma> k b s) then 1 else 0)"
| "taval \<Gamma> ik (NotEq a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CNe (taval \<Gamma> k a s) (taval \<Gamma> k b s) then 1 else 0)"
| "taval \<Gamma> ik (Eq a b) s = (let k = usual_kind (esyn \<Gamma> a) (esyn \<Gamma> b) in
     if cop_eval CEq (taval \<Gamma> k a s) (taval \<Gamma> k b s) then 1 else 0)"
| "taval \<Gamma> ik (Not a) s = (if truthy (taval \<Gamma> (esyn \<Gamma> a) a s) then 0 else 1)"
| "taval \<Gamma> ik (And a b) s =
     (if truthy (taval \<Gamma> (esyn \<Gamma> a) a s) \<and> truthy (taval \<Gamma> (esyn \<Gamma> b) b s) then 1 else 0)"
| "taval \<Gamma> ik (Or a b) s =
     (if truthy (taval \<Gamma> (esyn \<Gamma> a) a s) \<or> truthy (taval \<Gamma> (esyn \<Gamma> b) b s) then 1 else 0)"
| "taval \<Gamma> ik (Cast k a) s = ik_norm ik (ik_norm k (taval \<Gamma> (esyn \<Gamma> a) a s))"

subsection \<open>Typed expressions and their evaluator\<close>

text \<open>
  A typed expression carries the kind each arithmetic node computes at and names
  variables by identity. \<open>TCast\<close>, the one node without a source counterpart, is a
  conversion, in the role of CIL's \<open>CastE\<close>. \<open>teval\<close> needs no kind environment: every
  kind it uses is on the node. A variable read does not convert, because a typed store
  already holds a value of the variable's kind.
\<close>

datatype texp =
    TN ikind int
  | TVar ikind var_id
  | TArith ikind aop texp texp
  | TCast ikind texp
  | TCmp cop texp texp
  | TNot texp
  | TAnd texp texp
  | TOr texp texp

fun teval :: "texp \<Rightarrow> tstore \<Rightarrow> int" where
  "teval (TN ik n) t = ik_norm ik n"
| "teval (TVar ik v) t = t v"
| "teval (TArith ik op a b) t = ik_norm ik (aop_eval op (teval a t) (teval b t))"
| "teval (TCast ik a) t = ik_norm ik (teval a t)"
| "teval (TCmp op a b) t = (if cop_eval op (teval a t) (teval b t) then 1 else 0)"
| "teval (TNot a) t = (if truthy (teval a t) then 0 else 1)"
| "teval (TAnd a b) t = (if truthy (teval a t) \<and> truthy (teval b t) then 1 else 0)"
| "teval (TOr a b) t = (if truthy (teval a t) \<or> truthy (teval b t) then 1 else 0)"

text \<open>The kind a node produces: the one an arithmetic or literal node carries, the
  target of a conversion, and \<^const>\<open>I32\<close> for a truth value.\<close>

fun texp_kind :: "texp \<Rightarrow> ikind" where
  "texp_kind (TN ik _) = ik"
| "texp_kind (TVar ik _) = ik"
| "texp_kind (TArith ik _ _ _) = ik"
| "texp_kind (TCast ik _) = ik"
| "texp_kind (TCmp _ _ _) = I32"
| "texp_kind (TNot _) = I32"
| "texp_kind (TAnd _ _) = I32"
| "texp_kind (TOr _ _) = I32"

text \<open>A typed expression is well-typed when its kinds agree with each other and with
  the environment: an arithmetic node's operands carry its kind, a comparison's two
  operands share one, and a variable read carries the variable's kind. Abstract
  transfers that read an operand's kind off the operand rely on exactly this.\<close>

fun wt_texp :: "kenv \<Rightarrow> texp \<Rightarrow> bool" where
  "wt_texp \<kappa> (TN ik n) \<longleftrightarrow> True"
| "wt_texp \<kappa> (TVar ik v) \<longleftrightarrow> \<kappa> v = ik"
| "wt_texp \<kappa> (TArith ik op a b) \<longleftrightarrow>
     texp_kind a = ik \<and> texp_kind b = ik \<and> wt_texp \<kappa> a \<and> wt_texp \<kappa> b"
| "wt_texp \<kappa> (TCast ik a) \<longleftrightarrow> wt_texp \<kappa> a"
| "wt_texp \<kappa> (TCmp op a b) \<longleftrightarrow> texp_kind a = texp_kind b \<and> wt_texp \<kappa> a \<and> wt_texp \<kappa> b"
| "wt_texp \<kappa> (TNot a) \<longleftrightarrow> wt_texp \<kappa> a"
| "wt_texp \<kappa> (TAnd a b) \<longleftrightarrow> wt_texp \<kappa> a \<and> wt_texp \<kappa> b"
| "wt_texp \<kappa> (TOr a b) \<longleftrightarrow> wt_texp \<kappa> a \<and> wt_texp \<kappa> b"

theorem teval_in_range:
  assumes "wt_texp \<kappa> e" and "styped \<kappa> t"
  shows "teval e t \<in> ik_range (texp_kind e)"
  using assms by (cases e) (auto dest: stypedD simp del: ik_range_iff)

subsection \<open>Elaboration\<close>

text \<open>
  \<open>elaborate \<rho> \<kappa> ik e\<close> translates a source expression of one procedure, whose names
  \<open>\<rho>\<close> resolves, into a typed expression whose value has kind \<open>ik\<close>. It follows
  \<^const>\<open>taval\<close> node for node and inserts a conversion only where a value reaches a
  context at another kind. A conversion to the kind a value already has is left out:
  it would change no value, but a domain without magnitudes, such as Sign, could only
  answer top for it.
\<close>

definition tcast_to :: "ikind \<Rightarrow> ikind \<Rightarrow> texp \<Rightarrow> texp" where
  "tcast_to ik k a = (if ik = k then a else TCast ik a)"

fun elaborate :: "(vname \<Rightarrow> var_id) \<Rightarrow> kenv \<Rightarrow> ikind \<Rightarrow> exp \<Rightarrow> texp" where
  "elaborate \<rho> \<kappa> ik (N n) = TN ik n"
| "elaborate \<rho> \<kappa> ik (V x) = tcast_to ik (\<kappa> (\<rho> x)) (TVar (\<kappa> (\<rho> x)) (\<rho> x))"
| "elaborate \<rho> \<kappa> ik (Plus a b) = (let k = esyn (\<kappa> \<circ> \<rho>) (Plus a b) in
     tcast_to ik k (TArith k AAdd (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Minus a b) = (let k = esyn (\<kappa> \<circ> \<rho>) (Minus a b) in
     tcast_to ik k (TArith k ASub (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Times a b) = (let k = esyn (\<kappa> \<circ> \<rho>) (Times a b) in
     tcast_to ik k (TArith k AMul (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Div a b) = (let k = esyn (\<kappa> \<circ> \<rho>) (Div a b) in
     tcast_to ik k (TArith k ADiv (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Mod a b) = (let k = esyn (\<kappa> \<circ> \<rho>) (Mod a b) in
     tcast_to ik k (TArith k AMod (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Less a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     tcast_to ik I32 (TCmp CLt (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (LessEq a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     tcast_to ik I32 (TCmp CLe (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Greater a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     tcast_to ik I32 (TCmp CGt (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (GreaterEq a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     tcast_to ik I32 (TCmp CGe (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (NotEq a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     tcast_to ik I32 (TCmp CNe (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Eq a b) = (let k = usual_kind (esyn (\<kappa> \<circ> \<rho>) a) (esyn (\<kappa> \<circ> \<rho>) b) in
     tcast_to ik I32 (TCmp CEq (elaborate \<rho> \<kappa> k a) (elaborate \<rho> \<kappa> k b)))"
| "elaborate \<rho> \<kappa> ik (Not a) =
     tcast_to ik I32 (TNot (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) a) a))"
| "elaborate \<rho> \<kappa> ik (And a b) = tcast_to ik I32
     (TAnd (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) a) a) (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) b) b))"
| "elaborate \<rho> \<kappa> ik (Or a b) = tcast_to ik I32
     (TOr (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) a) a) (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) b) b))"
| "elaborate \<rho> \<kappa> ik (Cast k a) =
     tcast_to ik k (TCast k (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) a) a))"

text \<open>A context without a kind of its own, such as a branch condition, evaluates an
  expression at the kind it synthesizes.\<close>

definition elaborate_syn :: "(vname \<Rightarrow> var_id) \<Rightarrow> kenv \<Rightarrow> exp \<Rightarrow> texp" where
  "elaborate_syn \<rho> \<kappa> e = elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) e) e"

lemma texp_kind_tcast_to [simp]:
  "texp_kind (tcast_to ik k a) = (if ik = k then texp_kind a else ik)"
  by (simp add: tcast_to_def)

lemma texp_kind_elaborate [simp]: "texp_kind (elaborate \<rho> \<kappa> ik e) = ik"
  by (cases e) (simp_all add: Let_def)

theorem wt_texp_elaborate: "wt_texp \<kappa> (elaborate \<rho> \<kappa> ik e)"
  by (induction e arbitrary: ik) (simp_all add: Let_def tcast_to_def)

text \<open>
  Elaboration preserves the meaning. The typed store \<open>t\<close> holds a value for every
  identity, and the procedure sees it through its resolution, as \<open>t \<circ> \<rho>\<close>. The premise
  that \<open>t\<close> is typed is used at one place: \<^const>\<open>taval\<close> reads a variable at its own
  kind, \<^const>\<open>teval\<close> reads the stored value directly, and the two agree because the
  stored value already lies in that kind's range.
\<close>

theorem teval_elaborate:
  assumes "styped \<kappa> t"
  shows "teval (elaborate \<rho> \<kappa> ik e) t = taval (\<kappa> \<circ> \<rho>) ik e (t \<circ> \<rho>)"
proof -
  have var: "ik_norm (\<kappa> v) (t v) = t v" for v
    by (rule ik_norm_id [OF stypedD [OF assms]])
  show ?thesis
    by (induction e arbitrary: ik) (simp_all add: Let_def tcast_to_def arith_at_def var)
qed

corollary teval_elaborate_syn:
  assumes "styped \<kappa> t"
  shows "teval (elaborate_syn \<rho> \<kappa> e) t = taval (\<kappa> \<circ> \<rho>) (esyn (\<kappa> \<circ> \<rho>) e) e (t \<circ> \<rho>)"
  using teval_elaborate [OF assms] by (simp add: elaborate_syn_def)

subsection \<open>Erasure\<close>

text \<open>
  Erasure drops the kinds and the conversions and names every identity by its source
  name. It recovers the expression elaboration started from. It belongs to no
  semantics: \<^const>\<open>teval\<close> and \<^const>\<open>aval\<close> differ wherever a kind wraps, so the
  untyped meaning of the erased expression is not the typed meaning of the original.
\<close>

fun aop_exp :: "aop \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp" where
  "aop_exp AAdd = Plus" | "aop_exp ASub = Minus" | "aop_exp AMul = Times"
| "aop_exp ADiv = Div" | "aop_exp AMod = Mod"

fun cop_exp :: "cop \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp" where
  "cop_exp CLt = Less" | "cop_exp CLe = LessEq" | "cop_exp CGt = Greater"
| "cop_exp CGe = GreaterEq" | "cop_exp CEq = Eq" | "cop_exp CNe = NotEq"

fun texp_erase :: "texp \<Rightarrow> exp" where
  "texp_erase (TN _ n) = N n"
| "texp_erase (TVar _ v) = V (var_name v)"
| "texp_erase (TArith _ op a b) = aop_exp op (texp_erase a) (texp_erase b)"
| "texp_erase (TCast _ a) = texp_erase a"
| "texp_erase (TCmp op a b) = cop_exp op (texp_erase a) (texp_erase b)"
| "texp_erase (TNot a) = Not (texp_erase a)"
| "texp_erase (TAnd a b) = And (texp_erase a) (texp_erase b)"
| "texp_erase (TOr a b) = Or (texp_erase a) (texp_erase b)"

text \<open>Erasure drops every conversion, including one the source wrote, so it recovers
  an expression without explicit casts.\<close>

fun cast_free :: "exp \<Rightarrow> bool" where
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

theorem texp_erase_elaborate:
  assumes "\<And>x. var_name (\<rho> x) = x" and "cast_free e"
  shows "texp_erase (elaborate \<rho> \<kappa> ik e) = e"
  using assms(2) by (induction e arbitrary: ik) (simp_all add: Let_def tcast_to_def assms(1))

end
