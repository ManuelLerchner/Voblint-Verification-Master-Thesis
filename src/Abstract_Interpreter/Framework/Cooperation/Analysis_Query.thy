theory Analysis_Query
  imports "Voblint_VIMP.VIMP_Expr" "Voblint_Domain.Query_Lift" "Voblint_Domain.Int_Lattice"
begin

unbundle lattice_syntax

section \<open>Queries one analysis answers for another\<close>

text \<open>
  An analysis in a combination may ask its partners a question about the stores the
  current state describes, as a Goblint transfer asks \<open>man.ask\<close>. What an answer
  claims is fixed by one relation, \<open>answer_holds q a s\<close>: answer \<open>a\<close> to query \<open>q\<close>
  is true of store \<open>s\<close>. Answers form a meet-semilattice with top, as Goblint's
  per-query result lattices do (\<open>queries.ml\<close> at \<open>5320a6b7\<close>): \<open>\<top>\<close> claims
  nothing, and \<open>\<sqinter>\<close> combines what several analyses answered. The two laws below
  are all a combination needs to trust a combined answer; associativity and
  commutativity of the combination come from the class.
\<close>

locale query_algebra =
  fixes answer_holds :: "'q \<Rightarrow> 'r::{semilattice_inf, order_top} \<Rightarrow> store \<Rightarrow> bool"
  assumes top_sound: "answer_holds q \<top> s"
    and inf_sound: "answer_holds q a s \<Longrightarrow> answer_holds q b s \<Longrightarrow> answer_holds q (a \<sqinter> b) s"
begin

text \<open>
  An oracle answers every query. It holds at a store when each of its answers
  is true there. Component transfers are proved against this predicate, never
  against a particular partner.
\<close>

definition oracle_holds :: "('q \<Rightarrow> 'r) \<Rightarrow> store \<Rightarrow> bool" where
  "oracle_holds ask s \<longleftrightarrow> (\<forall>q. answer_holds q (ask q) s)"

lemma oracle_holdsD: "oracle_holds ask s \<Longrightarrow> answer_holds q (ask q) s"
  by (simp add: oracle_holds_def)

lemma oracle_holds_top [simp, intro]: "oracle_holds (\<lambda>_. \<top>) s"
  by (simp add: oracle_holds_def top_sound)

lemma oracle_holds_inf [intro]:
  "oracle_holds a s \<Longrightarrow> oracle_holds b s \<Longrightarrow> oracle_holds (\<lambda>q. a q \<sqinter> b q) s"
  by (simp add: oracle_holds_def inf_sound)

end

section \<open>The value of an expression\<close>

text \<open>
  Version 1 has one query kind, Goblint's \<open>EvalInt\<close>: which integers an
  expression may evaluate to (\<open>queries.ml\<close> line 108 at \<open>0dc12d355\<close>). Goblint
  answers it in \<open>Lattice.Lift(IntDomTuple)\<close>, and so does Voblint: the answer
  is an \<^typ>\<open>int_dom\<close> under \<^typ>\<open>'a query_lift\<close>. A comparison or logical
  operator evaluates to \<open>0\<close> or \<open>1\<close>, so its truth is the exact answer \<open>1\<close> or
  \<open>0\<close>; Goblint derives its former \<open>MustBeEqual\<close> and \<open>MayBeLess\<close> queries from
  \<open>EvalInt\<close> the same way (lines 528 to 539). The query is a constructor
  rather than a bare \<^typ>\<open>exp\<close> so that a later kind extends the datatype.
\<close>

datatype query = EvalInt exp

type_synonym answer = "int_dom query_lift"

text \<open>
  An answer claims that the expression evaluates into its concretization.
  \<open>QTop\<close> claims nothing: an analysis that does not understand the question
  declines with it. \<open>QBot\<close> admits no value, so a sound handler returns it
  only for a state that represents no concrete store. The meet combines two
  answers about one expression, and since the \<^typ>\<open>int_dom\<close> meet is exact,
  two sound analyses whose answers do not overlap describe no store in common.
\<close>

fun eval_holds :: "query \<Rightarrow> answer \<Rightarrow> store \<Rightarrow> bool" where
  "eval_holds (EvalInt e) a s \<longleftrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> gamma_query_lift gamma_int_dom a"

interpretation eval_query: query_algebra eval_holds
proof
  fix q :: query and a b :: answer and s
  show "eval_holds q \<top> s"
    by (cases q) simp
  show "eval_holds q a s \<Longrightarrow> eval_holds q b s \<Longrightarrow> eval_holds q (a \<sqinter> b) s"
    by (cases q) (simp add: gamma_query_lift_inf[OF gamma_inf_int_dom])
qed

declare eval_query.top_sound [simp]

text \<open>
  The exact answer for a known integer, and a known integer read back from
  an answer, as Goblint's \<open>ID.of_int\<close> and \<open>ID.to_int\<close>. A consumer that reads
  \<open>n\<close> back may use it for the expression at every store the answer holds at.
\<close>

definition answer_of_int :: "int \<Rightarrow> answer" where
  "answer_of_int n = QLifted (int_dom_of_int n)"

lemma gamma_answer_of_int [simp]:
  "gamma_query_lift gamma_int_dom (answer_of_int n) = {n}"
  by (simp add: answer_of_int_def)

fun answer_const :: "answer \<Rightarrow> int option" where
  "answer_const (QLifted d) = int_dom_constant d"
| "answer_const _ = None"

lemma eval_holds_constD:
  assumes "eval_holds (EvalInt e) a s" and "answer_const a = Some n"
  shows "\<lbrakk>e\<rbrakk>\<^sub>e s = n"
  using assms gamma_int_dom_constant_subset
  by (cases a rule: answer_const.cases) auto

lemma answer_const_of_int [simp]: "answer_const (answer_of_int n) = Some n"
  by (simp add: answer_of_int_def int_dom_of_int_def int_dom_constant_def
      top_int_dom_ext_def)

text \<open>
  An interval analysis knows only the interval component; the others stay at
  their top, so the answer claims exactly what the interval does.
\<close>

definition answer_of_ivl :: "ivl \<Rightarrow> answer" where
  "answer_of_ivl i = QLifted ((\<top> :: int_dom)\<lparr>int_ivl := i\<rparr>)"

lemma gamma_answer_of_ivl [simp]:
  "gamma_query_lift gamma_int_dom (answer_of_ivl i) = gamma_ivl i"
  by (simp add: answer_of_ivl_def top_int_dom_ext_def top_sign_def top_parity_def
      gamma_int_dom_def)

end
