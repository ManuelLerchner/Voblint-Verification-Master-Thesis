theory Analysis_Query
  imports "Voblint_VIMP.VIMP_Expr" "Voblint_Domain.Interval_Lattice"
begin

unbundle lattice_syntax

section \<open>Queries one analysis answers for another\<close>

text \<open>
  An analysis in a product may ask its partners a question about the stores the
  current state describes, as a Goblint transfer asks \<open>man.ask\<close>. What an answer
  claims is fixed by one relation, \<open>answer_holds q a s\<close>: answer \<open>a\<close> to query \<open>q\<close>
  is true of store \<open>s\<close>. Answers form a meet-semilattice with top, as Goblint's
  per-query result lattices do (\<open>queries.ml\<close> at \<open>5320a6b7\<close>): \<open>\<top>\<close> claims
  nothing, and \<open>\<sqinter>\<close> combines what several analyses answered. The two laws below
  are all a product needs to trust a combined answer; associativity and
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
  expression may evaluate to. The answer is an interval, as Goblint answers
  \<open>EvalInt\<close> in its integer domain (\<open>queries.ml\<close> line 108 at \<open>0dc12d355\<close>). A
  comparison or logical operator evaluates to \<open>0\<close> or \<open>1\<close>, so its truth is the
  answer \<open>[1,1]\<close> or \<open>[0,0]\<close>; Goblint derives its former \<open>MustBeEqual\<close> and
  \<open>MayBeLess\<close> queries from \<open>EvalInt\<close> the same way (lines 528 to 539). The query
  is a constructor rather than a bare \<^typ>\<open>exp\<close> so that a later kind extends
  the datatype.
\<close>

datatype query = EvalInt exp

text \<open>
  An answer claims that the expression evaluates into the interval's
  concretization. The full interval claims nothing and is the top, and the
  meet combines two answers about one expression. An empty answer admits no
  value, so a sound handler returns it only for a state that represents no
  concrete store: two sound analyses whose answers do not overlap describe no
  store in common.
\<close>

fun eval_holds :: "query \<Rightarrow> ivl \<Rightarrow> store \<Rightarrow> bool" where
  "eval_holds (EvalInt e) i s \<longleftrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> gamma_ivl i"

interpretation eval_query: query_algebra eval_holds
proof
  fix q :: query and a b :: ivl and s
  show "eval_holds q \<top> s"
    by (cases q) (simp add: top_ivl_def gamma_ivl_top)
  show "eval_holds q a s \<Longrightarrow> eval_holds q b s \<Longrightarrow> eval_holds q (a \<sqinter> b) s"
    by (cases q) (simp only: eval_holds.simps meet_ivl_gamma)
qed

lemma eval_holds_top [simp]: "eval_holds q \<top> s"
  by (rule eval_query.top_sound)

text \<open>
  The answer \<open>[n,n]\<close> fixes the value. \<open>ivl_const\<close> reads that value back, and
  a consumer that finds one may use \<open>n\<close> for the expression at every store the
  answer holds at.
\<close>

fun ivl_const :: "ivl \<Rightarrow> int option" where
  "ivl_const (Ivl (Fin l) (Fin u)) = (if l = u then Some l else None)"
| "ivl_const _ = None"

lemma ivl_const_SomeD: "ivl_const i = Some n \<Longrightarrow> i = ivl_of_int n"
  by (cases i rule: ivl_const.cases) (auto split: if_splits)

lemma eval_holds_constD:
  assumes "eval_holds (EvalInt e) i s" and "ivl_const i = Some n"
  shows "\<lbrakk>e\<rbrakk>\<^sub>e s = n"
  using assms ivl_const_SomeD[OF assms(2)] by simp

end
