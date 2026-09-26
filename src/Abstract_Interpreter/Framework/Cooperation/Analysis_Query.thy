theory Analysis_Query
  imports "Voblint_VIMP.VIMP_Expr"
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

section \<open>The truth of an expression\<close>

text \<open>
  Version 1 has one query kind, whether an expression is true. It is a
  constructor rather than a bare \<^typ>\<open>exp\<close> so that a later kind extends the
  datatype.
\<close>

datatype query = EvalBool exp

text \<open>
  An answer to \<open>EvalBool e\<close> is the set of truth values it admits for \<open>e\<close>.
  \<open>UNIV\<close> claims nothing and is the top; \<open>{b}\<close> claims the value \<open>b\<close>; \<open>{}\<close> says
  no store is described. Order and meet are inclusion and intersection, so two
  analyses that answer \<open>{True}\<close> and \<open>{False}\<close> combine to \<open>{}\<close>. Unlike
  \<^typ>\<open>bool option\<close>, the four sets are closed under meet. That is why the
  answers are sets and not the three-valued type of \<open>Three_Valued\<close>: its
  connectives combine the truth of two different expressions, whereas the meet
  combines two answers about one.
\<close>

fun truth_holds :: "query \<Rightarrow> bool set \<Rightarrow> store \<Rightarrow> bool" where
  "truth_holds (EvalBool e) A s \<longleftrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) \<in> A"

interpretation truth_query: query_algebra truth_holds
proof
  fix q :: query and A B :: "bool set" and s
  show "truth_holds q \<top> s" by (cases q) simp
  show "truth_holds q A s \<Longrightarrow> truth_holds q B s \<Longrightarrow> truth_holds q (A \<sqinter> B) s"
    by (cases q) simp
qed

text \<open>
  A domain's check query answers with \<^typ>\<open>bool option\<close>, \<open>None\<close> meaning
  unknown. Embedding it as the set of admitted values keeps its soundness
  statement as it is.
\<close>

fun admitted :: "bool option \<Rightarrow> bool set" where
  "admitted None = UNIV"
| "admitted (Some b) = {b}"

lemma truth_holds_admitted:
  assumes "\<And>b. r = Some b \<Longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) = b"
  shows "truth_holds (EvalBool e) (admitted r) s"
  using assms by (cases r) auto

end
