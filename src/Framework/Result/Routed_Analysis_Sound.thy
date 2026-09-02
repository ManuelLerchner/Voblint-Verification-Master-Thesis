theory Routed_Analysis_Sound
  imports DG_Analysis_Adapter
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

  \<open>solved_local_reader\<close> is the reader every instance was defining by hand: at a
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
     (case k of Inl vc \<Rightarrow> (if vc \<in> vars then locals (sigma (Inl vc)) else bot)
              | Inr _ \<Rightarrow> bot)"

lemma solved_local_reader_covered [simp]:
  "vc \<in> vars \<Longrightarrow> solved_local_reader vars sigma (Inl vc) = locals (sigma (Inl vc))"
  by (simp add: solved_local_reader_def)

lemma solved_local_reader_uncovered [simp]:
  "vc \<notin> vars \<Longrightarrow> solved_local_reader vars sigma (Inl vc) = bot"
  by (simp add: solved_local_reader_def)

lemma solved_local_reader_global [simp]:
  "solved_local_reader vars sigma (Inr k) = bot"
  by (simp add: solved_local_reader_def)

text \<open>
  The two coverage obligations \<^locale>\<open>dg_ctx_activation_base\<close> asks for hold for
  this reader by construction, given only that the joint concretization ignores
  its global argument (which is what \<open>gammaDG_rd\<close> already says) and that the
  readback takes \<open>bot\<close> to \<^const>\<open>Bot\<close>. Neither depends on the domain or the
  context policy, so no instance need prove them again.
\<close>

lemma solved_local_reader_sg_cov:
  assumes rd_eq: "\<And>d g'. gammaDG d g' = gamma_state_lift (rd d)"
    and cov: "(v, c) \<in> vars"
  shows "gamma_state_lift (rd (solved_local_reader vars sigma (Inl (v, c))))
           = gammaDG (locals (sigma (Inl (v, c)))) (globs (sigma (Inr gk0)))"
  by (simp add: cov rd_eq)

lemma solved_local_reader_sg_uncov:
  assumes rd_bot: "rd bot = Bot"
    and uncov: "(v, c) \<notin> vars"
  shows "gamma_state_lift (rd (solved_local_reader vars sigma (Inl (v, c)))) = {}"
  by (simp add: uncov rd_bot)

subsection \<open>The composition locale\<close>

text \<open>
  Everything a routed analysis needs above its solved system, in one place: the
  domain enters through \<open>S\<close> and \<open>gammaDG\<close>, the context policy through \<open>route\<close>,
  \<open>enterc\<close> and \<open>seed_key\<close>, and the solved system through \<open>sigma\<close>/\<open>vars\<close>. The
  reader is no longer an instance's own definition -- it is
  \<^const>\<open>solved_local_reader\<close> -- so its two coverage obligations are the
  one-line lemmas above rather than a per-instance proof.

  An instance is then a single \<^theory_text>\<open>interpretation\<close>, and the theorems below are
  what it gets: a published result table, its per-node soundness, and the
  check report's proved/refuted verdicts.
\<close>

locale routed_analysis_sound =
  dg_analysis_adapter S gammaDG gs g gk0 route bot0 s0d s0g sigma vars x0
    "solved_local_reader vars sigma" seed_key "\<lambda>d. gamma_state_lift (rd d)"
    enterc rd classify
  for S :: "(pp \<times> 'c, 'k, unit, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and g gk0
    and route :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> 'c"
    and bot0 s0d :: 'D and s0g :: 'G
    and sigma :: "pp \<times> 'c + 'k \<Rightarrow> ('D, 'G) dg_state"
    and vars :: "(pp \<times> 'c) set"
    and x0 :: "pp \<times> 'c"
    and seed_key :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and enterc :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
    and rd :: "'D \<Rightarrow> 'a::sound_domain abs_state lifted"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
begin

text \<open>The analysis-level endpoints, named without mentioning the sublocale so an
  instance cites them directly.\<close>

lemmas routed_result = analyse_result_def
lemmas routed_result_node_sound = analyse_result_node_sound
lemmas routed_report_proved_sound = analyse_report_ctx_proved_sound
lemmas routed_report_refuted_sound = analyse_report_ctx_refuted_sound
lemmas routed_activation_collect_sound = activation_collect_dg_sound

end

end

