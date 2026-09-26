theory Oracle_Local_Spec
  imports "Voblint_Framework.DG_Spec_Sound" Analysis_Query
begin

section \<open>A local specification that may ask\<close>

text \<open>
  A component of a product is a local-only specification whose
  intraprocedural transfers take an oracle as their first argument, the
  counterpart of a Goblint transfer receiving \<open>man\<close> with its \<open>ask\<close>. Its
  obligations are those of \<^locale>\<open>sound_local_dg_spec\<close>, with the edge step
  weakened to the stores at which the oracle holds. The oracle is quantified,
  never fixed, so the proof of a component cannot depend on who answers.
  \<open>enter\<close> and \<open>combine\<close> take no oracle in this version.
\<close>

locale oracle_local_spec = query_algebra answer_holds
  for answer_holds :: "'q \<Rightarrow> 'r::{semilattice_inf, order_top} \<Rightarrow> store \<Rightarrow> bool" +
  fixes sk :: "('q \<Rightarrow> 'r) \<Rightarrow> 'D::bounded_semilattice_sup_bot \<Rightarrow> 'D"
    and asn :: "('q \<Rightarrow> 'r) \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D"
    and sp :: "('q \<Rightarrow> 'r) \<Rightarrow> special_call \<Rightarrow> vname \<Rightarrow> 'D \<Rightarrow> 'D"
    and br :: "('q \<Rightarrow> 'r) \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> 'D \<Rightarrow> 'D"
    and bd :: "('q \<Rightarrow> 'r) \<Rightarrow> pname \<Rightarrow> 'D \<Rightarrow> 'D"
    and rt :: "('q \<Rightarrow> 'r) \<Rightarrow> exp option \<Rightarrow> pname \<Rightarrow> 'D \<Rightarrow> 'D"
    and en :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D enter_result list"
    and ev :: "('q \<Rightarrow> 'r) \<Rightarrow> analysis_event \<Rightarrow> 'D \<Rightarrow> 'D"
    and ce :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D"
    and ca :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D"
    and gammaD :: "'D \<Rightarrow> store set"
    and \<G> :: "vname \<Rightarrow> bool"
  assumes gammaD_mono: "d \<le> d' \<Longrightarrow> gammaD d \<subseteq> gammaD d'"
    and step_sound_oracle:
      "edge_collect a (gammaD d \<inter> Collect (oracle_holds ask))
         \<subseteq> gammaD (local_spec_step (sk ask) (asn ask) (sp ask) (br ask) (bd ask) (rt ask)
                     (ev ask) a d)"
    and enter_sound_local:
      "s \<in> gammaD d \<Longrightarrow>
         entry_pairs_cover gammaD s
           (call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           (en ci d)"
    and combine_sound_local:
      "\<lbrakk>s \<in> gammaD dc; t \<in> gammaD de\<rbrakk> \<Longrightarrow>
        combine_collect \<G> (ci_dst ci) s t \<in> gammaD (ca ci (ce ci dc de) de)"

text \<open>
  A query handler answers from a component's own state and never asks, which
  is what keeps version 1 free of Goblint's query recursion. It is sound when
  every answer holds at every store the state describes.
\<close>

locale sound_query_handler = query_algebra answer_holds
  for answer_holds :: "'q \<Rightarrow> 'r::{semilattice_inf, order_top} \<Rightarrow> store \<Rightarrow> bool" +
  fixes qry :: "'D \<Rightarrow> 'q \<Rightarrow> 'r"
    and gammaD :: "'D \<Rightarrow> store set"
  assumes qry_sound: "s \<in> gammaD d \<Longrightarrow> answer_holds q (qry d q) s"
begin

lemma oracle_holds_qry: "s \<in> gammaD d \<Longrightarrow> oracle_holds (qry d) s"
  by (simp add: oracle_holds_def qry_sound)

end

text \<open>A component is both: transfers proved against any sound oracle, and a
  handler for its own state.\<close>

locale oracle_component =
  oracle_local_spec answer_holds sk asn sp br bd rt en ev ce ca gammaD \<G>
  + sound_query_handler answer_holds qry gammaD
  for answer_holds :: "'q \<Rightarrow> 'r::{semilattice_inf, order_top} \<Rightarrow> store \<Rightarrow> bool"
    and sk asn sp br bd rt en ev ce ca
    and gammaD :: "'D::bounded_semilattice_sup_bot \<Rightarrow> store set"
    and \<G> qry

section \<open>Closing a component\<close>

text \<open>
  Closing supplies the component's own handler as the oracle, evaluated at the
  state the edge starts from. It is the only place an oracle is built. Closing
  a product therefore hands the combined answer of every component to every
  component, however the product is parenthesized.
\<close>

definition close_step :: "('D \<Rightarrow> 'q \<Rightarrow> 'r) \<Rightarrow> (('q \<Rightarrow> 'r) \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> 'D \<Rightarrow> 'D" where
  "close_step qry f d = f (qry d) d"

lemma local_spec_step_close:
  "local_spec_step (close_step qry sk) (\<lambda>x e. close_step qry (\<lambda>ask. asn ask x e))
     (\<lambda>c x. close_step qry (\<lambda>ask. sp ask c x)) (\<lambda>b pol. close_step qry (\<lambda>ask. br ask b pol))
     (\<lambda>p. close_step qry (\<lambda>ask. bd ask p)) (\<lambda>e p. close_step qry (\<lambda>ask. rt ask e p))
     (\<lambda>v. close_step qry (\<lambda>ask. ev ask v)) a d
   = local_spec_step (sk (qry d)) (asn (qry d)) (sp (qry d)) (br (qry d)) (bd (qry d))
       (rt (qry d)) (ev (qry d)) a d"
  by (cases a) (simp_all add: close_step_def)

theorem (in oracle_component) close_component:
  "sound_local_dg_spec (close_step qry sk) (\<lambda>x e. close_step qry (\<lambda>ask. asn ask x e))
     (\<lambda>c x. close_step qry (\<lambda>ask. sp ask c x)) (\<lambda>b pol. close_step qry (\<lambda>ask. br ask b pol))
     (\<lambda>p. close_step qry (\<lambda>ask. bd ask p)) (\<lambda>e p. close_step qry (\<lambda>ask. rt ask e p))
     en (\<lambda>v. close_step qry (\<lambda>ask. ev ask v)) ce ca gammaD \<G>"
proof (unfold_locales, goal_cases)
  case (1 d d')
  then show ?case by (rule gammaD_mono)
next
  case (2 a d)
  have "gammaD d \<inter> Collect (oracle_holds (qry d)) = gammaD d"
    using oracle_holds_qry by blast
  then show ?case
    using step_sound_oracle[of a d "qry d"] by (simp add: local_spec_step_close)
next
  case (3 s d ci)
  then show ?case by (rule enter_sound_local)
next
  case (4 s dc t de ci)
  then show ?case by (rule combine_sound_local)
qed

text \<open>The closed component as the specification the equation generator reads,
  and the contract it carries.\<close>

definition closed_local_spec ::
  "('D \<Rightarrow> 'q \<Rightarrow> 'r) \<Rightarrow> (('q \<Rightarrow> 'r) \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (('q \<Rightarrow> 'r) \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (('q \<Rightarrow> 'r) \<Rightarrow> special_call \<Rightarrow> vname \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (('q \<Rightarrow> 'r) \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (('q \<Rightarrow> 'r) \<Rightarrow> pname \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (('q \<Rightarrow> 'r) \<Rightarrow> exp option \<Rightarrow> pname \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (call_info \<Rightarrow> 'D \<Rightarrow> 'D enter_result list) \<Rightarrow> (('q \<Rightarrow> 'r) \<Rightarrow> analysis_event \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> (call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> ('x,'k,'v,'D,'G) dg_spec"
where
  "closed_local_spec qry sk asn sp br bd rt en ev ce ca =
     local_dg_spec (close_step qry sk) (\<lambda>x e. close_step qry (\<lambda>ask. asn ask x e))
       (\<lambda>c x. close_step qry (\<lambda>ask. sp ask c x)) (\<lambda>b pol. close_step qry (\<lambda>ask. br ask b pol))
       (\<lambda>p. close_step qry (\<lambda>ask. bd ask p)) (\<lambda>e p. close_step qry (\<lambda>ask. rt ask e p))
       en (\<lambda>v. close_step qry (\<lambda>ask. ev ask v)) ce ca"

theorem (in oracle_component) closed_contract:
  "analysis_contract (closed_local_spec qry sk asn sp br bd rt en ev ce ca) (\<lambda>d g. gammaD d) \<G>"
  unfolding closed_local_spec_def by (rule sound_local_dg_spec.local_spec_contract[OF close_component])

section \<open>Every existing local specification is a component\<close>

text \<open>
  A specification that never asks is a component whose transfers ignore the
  oracle. It may still answer queries: any sound handler for its own states
  turns it into a component. With the handler that answers \<open>\<top>\<close> to every query
  it is the counterpart of an analysis inheriting Goblint's \<open>DefaultSpec.query\<close>.
\<close>

lemma (in sound_local_dg_spec) oracle_component_of_handler:
  assumes "sound_query_handler answer_holds qry gammaD"
  shows "oracle_component answer_holds (\<lambda>_. sk) (\<lambda>_. asn) (\<lambda>_. sp) (\<lambda>_. br) (\<lambda>_. bd)
           (\<lambda>_. rt) en (\<lambda>_. ev) ce ca gammaD \<G> qry"
proof -
  interpret sound_query_handler answer_holds qry gammaD by (fact assms)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case (1 d d')
    then show ?case by (rule gammaD_mono)
  next
    case (2 a d ask)
    show ?case using step_sound_local[of a d] edge_collect_mono by blast
  next
    case (3 s d ci)
    then show ?case by (rule enter_sound_local)
  next
    case (4 s dc t de ci)
    then show ?case by (rule combine_sound_local)
  qed
qed

lemma (in sound_local_dg_spec) oracle_component_default:
  assumes "query_algebra answer_holds"
  shows "oracle_component answer_holds (\<lambda>_. sk) (\<lambda>_. asn) (\<lambda>_. sp) (\<lambda>_. br) (\<lambda>_. bd)
           (\<lambda>_. rt) en (\<lambda>_. ev) ce ca gammaD \<G> (\<lambda>_ _. \<top>)"
proof -
  interpret query_algebra answer_holds by (fact assms)
  show ?thesis
    by (rule oracle_component_of_handler) (unfold_locales, rule top_sound)
qed

end
