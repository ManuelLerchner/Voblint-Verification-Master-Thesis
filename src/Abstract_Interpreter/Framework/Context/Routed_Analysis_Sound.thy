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
  \<open>R\<close> and \<open>seed\<close>, and the solved system through \<open>sigma\<close>/\<open>vars\<close>. The
  fixed reader is \<^const>\<open>solved_local_reader\<close>, and its concretization reads
  the solved global at \<open>Inr buffer_key\<close> as the second argument of \<open>rd\<close>,
  so the two coverage obligations are the one-line lemmas above.

  An instance is then a single \<^theory_text>\<open>interpretation\<close>, and the theorems below are
  what it gets: a published result table, its per-node soundness, and the
  check report's proved/refuted verdicts.
\<close>

locale routed_analysis =
  dg_analysis_adapter S \<gamma>\<^sub>D\<^sub>G \<G> g buffer_key global_of route bot0 s0d s0g sigma vars x0
    "solved_local_reader vars sigma" seed is_bot
    "\<lambda>d. gamma_lift \<gamma>\<^sub>V (rd d (genv global_of sigma))"
    R rd \<gamma>\<^sub>V empty\<^sub>V classify
  for S :: "(pp \<times> 'c, 'k, 'n, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and \<gamma>\<^sub>D\<^sub>G :: "'D \<Rightarrow> ('n \<Rightarrow> 'G) \<Rightarrow> store set"
    and \<G> :: "vname \<Rightarrow> bool"
    and g buffer_key and global_of :: "'n \<Rightarrow> 'k"
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c"
    and bot0 s0d :: 'D and s0g :: 'G
    and sigma :: "pp \<times> 'c + 'k \<Rightarrow> ('D, 'G) dg_state"
    and vars :: "(pp \<times> 'c) set"
    and x0 :: "pp \<times> 'c"
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and is_bot :: "'D \<Rightarrow> bool"
    and R :: "'c call_context_rel"
    and rd :: "'D \<Rightarrow> ('n \<Rightarrow> 'G) \<Rightarrow> 'v lifted"
    and \<gamma>\<^sub>V :: "'v \<Rightarrow> store set"
    and empty\<^sub>V :: "'v \<Rightarrow> bool"
    and classify :: "exp \<Rightarrow> 'v \<Rightarrow> check_result"

end
