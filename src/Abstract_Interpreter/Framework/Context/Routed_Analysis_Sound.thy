theory Routed_Analysis_Sound
  imports DG_Analysis_Adapter Routed_Context_Unit
begin

section \<open>Reading a solved routed system as an analysis result\<close>

text \<open>
  A routed analysis is assembled from two independent choices: which abstract
  domain it computes in, and which context policy it routes calls by. This
  theory is the composition step that does not depend on either. It takes a
  solved routed equation system and derives the analysis-level soundness
  statement, so a concrete analysis supplies its domain facts and its policy
  facts and interprets this once, rather than repeating the derivation per
  (domain, policy) pair.

  \<open>solved_local_reader\<close> is the one reader every instance uses: at a
  covered unknown it hands back the solution's local half, and elsewhere
  \<open>bot\<close>. Reading a global key gives \<open>bot\<close> too -- the routed seed keys carry
  entry contributions, not program-point values, and a result table never
  reads them.
\<close>

definition solved_local_reader ::
  "(pp \<times> 'c) set \<Rightarrow> (pp \<times> 'c + 'k \<Rightarrow> ('D::bounded_semilattice_sup_bot, 'G) dg_state)
   \<Rightarrow> pp \<times> 'c + 'k \<Rightarrow> 'D"
where
  "solved_local_reader vars sigma k =
     (case k of Inl vc \<Rightarrow> (if vc \<in> vars then dg_local (sigma (Inl vc)) else bot)
              | Inr _ \<Rightarrow> bot)"

lemma solved_local_reader_covered [simp]:
  "vc \<in> vars \<Longrightarrow> solved_local_reader vars sigma (Inl vc) = dg_local (sigma (Inl vc))"
  by (simp add: solved_local_reader_def)

lemma solved_local_reader_uncovered [simp]:
  "vc \<notin> vars \<Longrightarrow> solved_local_reader vars sigma (Inl vc) = bot"
  by (simp add: solved_local_reader_def)

lemma solved_local_reader_global [simp]:
  "solved_local_reader vars sigma (Inr k) = bot"
  by (simp add: solved_local_reader_def)

text \<open>
  The reader returns only the local half. The global half enters through the
  concretization the locale below pairs with it, which publishes each local
  value together with the solved global at \<open>Inr buffer_key\<close>. Under that
  pairing the two coverage obligations \<^locale>\<open>dg_context_activation\<close> asks for
  hold by construction, given \<open>gammaDG_rd\<close> and that the publication map takes
  \<open>bot\<close> to \<^const>\<open>Bot\<close>. Neither depends on the domain or the context policy,
  so no instance need prove them again.
\<close>

subsection \<open>The composition locale\<close>

text \<open>
  Everything a routed analysis needs above its solved system, in one place: the
  domain enters through \<open>S\<close> and \<open>\<gamma>\<^sub>D\<^sub>G\<close>, the context policy through \<open>route\<close>,
  \<open>adm\<close> and \<open>seed\<close>, and the solved system through \<open>sigma\<close>/\<open>vars\<close>. The
  fixed reader is \<^const>\<open>solved_local_reader\<close>, and its concretization reads
  the solved global at \<open>Inr buffer_key\<close> as the second argument of \<open>rd\<close>,
  so the two coverage obligations are the one-line lemmas above.

  An instance is then a single \<^theory_text>\<open>interpretation\<close>, and the theorems below are
  what it gets: a published result table, its per-node soundness, and the
  check report's proved/refuted verdicts.
\<close>

locale grouted_analysis =
  gdg_analysis_adapter ev rv conv glob S \<gamma>\<^sub>D\<^sub>G g buffer_key global_of route bot0 d\<^sub>0 g\<^sub>0 sigma
    vars x0 "solved_local_reader vars sigma" seed is_bot
    "\<lambda>d. gamma_lift \<gamma>\<^sub>V (rd d (genv global_of sigma))"
    adm rd \<gamma>\<^sub>V empty\<^sub>V classify
  for ev :: "'e::linorder \<Rightarrow> ('vr::linorder \<Rightarrow> int) \<Rightarrow> int" and rv :: 'vr
    and conv :: "'vr option \<Rightarrow> int \<Rightarrow> int" and glob :: "'vr \<Rightarrow> bool"
    and S :: "('vr, 'e, pp \<times> 'c, 'k, 'n, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) gdg_spec"
    and \<gamma>\<^sub>D\<^sub>G :: "'D \<Rightarrow> ('n \<Rightarrow> 'G) \<Rightarrow> ('vr \<Rightarrow> int) set"
    and g buffer_key and global_of :: "'n \<Rightarrow> 'k"
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> ('vr, 'e) gcall_action \<Rightarrow> 'c"
    and bot0 d\<^sub>0 :: 'D and g\<^sub>0 :: 'G
    and sigma :: "pp \<times> 'c + 'k \<Rightarrow> ('D, 'G) dg_state"
    and vars :: "(pp \<times> 'c) set"
    and x0 :: "pp \<times> 'c"
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and is_bot :: "'D \<Rightarrow> bool"
    and adm :: "('vr, 'e, 'c) gcontext_policy"
    and rd :: "'D \<Rightarrow> ('n \<Rightarrow> 'G) \<Rightarrow> 'v lifted"
    and \<gamma>\<^sub>V :: "'v \<Rightarrow> ('vr \<Rightarrow> int) set"
    and empty\<^sub>V :: "'v \<Rightarrow> bool"
    and classify :: "'e \<Rightarrow> 'v \<Rightarrow> check_result"

text \<open>The untyped composition locale, the instance at source names.\<close>

locale routed_analysis =
  dg_analysis_adapter S \<gamma>\<^sub>D\<^sub>G \<G> g buffer_key global_of route bot0 d\<^sub>0 g\<^sub>0 sigma vars x0
    "solved_local_reader vars sigma" seed is_bot
    "\<lambda>d. gamma_lift \<gamma>\<^sub>V (rd d (genv global_of sigma))"
    adm rd \<gamma>\<^sub>V empty\<^sub>V classify
  for S :: "(pp \<times> 'c, 'k, 'n, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and \<gamma>\<^sub>D\<^sub>G :: "'D \<Rightarrow> ('n \<Rightarrow> 'G) \<Rightarrow> store set"
    and \<G> :: "vname \<Rightarrow> bool"
    and g buffer_key and global_of :: "'n \<Rightarrow> 'k"
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c"
    and bot0 d\<^sub>0 :: 'D and g\<^sub>0 :: 'G
    and sigma :: "pp \<times> 'c + 'k \<Rightarrow> ('D, 'G) dg_state"
    and vars :: "(pp \<times> 'c) set"
    and x0 :: "pp \<times> 'c"
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and is_bot :: "'D \<Rightarrow> bool"
    and adm :: "'c context_policy"
    and rd :: "'D \<Rightarrow> ('n \<Rightarrow> 'G) \<Rightarrow> 'v lifted"
    and \<gamma>\<^sub>V :: "'v \<Rightarrow> store set"
    and empty\<^sub>V :: "'v \<Rightarrow> bool"
    and classify :: "exp \<Rightarrow> 'v \<Rightarrow> check_result"

sublocale routed_analysis \<subseteq>
  grouted_analysis aval ret_var "\<lambda>_ n. n" \<G> S \<gamma>\<^sub>D\<^sub>G g buffer_key global_of route bot0 d\<^sub>0 g\<^sub>0
    sigma vars x0 seed is_bot adm rd \<gamma>\<^sub>V empty\<^sub>V classify
  rewrites "cfg_transfer_sem.gedge_collect aval ret_var (\<lambda>_ n. n) = edge_collect"
    and "cfg_transfer_sem.gcombine_collect ret_var (\<lambda>_ n. n) \<G> = combine_collect \<G>"
    and "cfg_transfer_sem.gcall_enter aval (\<lambda>_ n. n) \<G> = call_enter \<G>"
    and "cfg_edge_sem.gedge_step aval ret_var (\<lambda>_ n. n) = edge_step"
    and "trace_sem.gvalid_activation_trace aval ret_var (\<lambda>_ n. n) \<G> = valid_activation_trace \<G>"
    and "ctx_sem.gadmits_call_context aval (\<lambda>_ n. n) \<G> = admits_call_context \<G>"
    and "ctx_sem.gactivation_context_rel aval (\<lambda>_ n. n) \<G> = activation_context_rel \<G>"
    and "ctx_sem.gcall_context_total_on aval (\<lambda>_ n. n) \<G> cover' adm' g' = call_context_total_on cover' adm' \<G> g'"
    and "ctx_sem.gactivation_collect aval ret_var (\<lambda>_ n. n) \<G> = activation_collect \<G>"
    and "collect_sem.gnode_collect aval ret_var (\<lambda>_ n. n) \<G> = node_collect \<G>"
  by unfold_locales
     (simp_all add: edge_collect_def combine_collect_def call_enter_def edge_step_def
       valid_activation_trace_def admits_call_context_def activation_context_rel_def
       call_context_total_on_def activation_collect_def node_collect_def)

end
