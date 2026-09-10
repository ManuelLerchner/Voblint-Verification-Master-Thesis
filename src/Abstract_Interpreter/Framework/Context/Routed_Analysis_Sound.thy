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

subsection \<open>The composition locale\<close>

text \<open>
  Everything a routed analysis needs above its solved system, in one place: the
  domain enters through \<open>S\<close> and \<open>gammaDG\<close>, the context policy through \<open>route\<close>,
  \<open>R\<close> and \<open>seed_key\<close>, and the solved system through \<open>sigma\<close>/\<open>vars\<close>. The
  reader is no longer an instance's own definition -- it is
  \<^const>\<open>solved_local_reader\<close> -- so its two coverage obligations are the
  one-line lemmas above rather than a per-instance proof.

  An instance is then a single \<^theory_text>\<open>interpretation\<close>, and the theorems below are
  what it gets: a published result table, its per-node soundness, and the
  check report's proved/refuted verdicts.
\<close>

locale routed_analysis_sound =
  dg_analysis_adapter S gammaDG gs g gk0 route bot0 s0d s0g sigma vars x0
    "solved_local_reader vars sigma" seed_key is_bot "\<lambda>d. gamma_state_lift (rd d)"
    R rd classify
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
    and is_bot :: "'D \<Rightarrow> bool"
    and R :: "'c call_context_rel"
    and rd :: "'D \<Rightarrow> 'a::sound_domain abs_state lifted"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
begin

text \<open>The activation-collecting endpoint, named without mentioning the
  sublocale so an instance cites it directly.\<close>

lemmas routed_activation_collect_sound = activation_collect_dg_sound

end

section \<open>Publishing a unit-context run\<close>

text \<open>
  A unit-context producer already owns the equation-system and routing proof.
  Publishing it adds only the readback, classifier, and finite-key facts. This
  locale composes those facts once; concrete domains retain their routing and
  solver choices without replaying the inherited routed-context obligations.
\<close>

locale unit_analysis_sound =
  unit_routed_context S gammaDG gs g gk0 bot0 s0d s0g sigma vars x0
    "solved_local_reader vars sigma" seed_key is_bot
    "\<lambda>d. gamma_state_lift (rd d)"
  for S :: "(pp \<times> unit, 'k, unit, 'D::bounded_semilattice_sup_bot,
              'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and g :: cfg and gk0 :: 'k
    and bot0 s0d :: 'D and s0g :: 'G
    and sigma :: "pp \<times> unit + 'k \<Rightarrow> ('D, 'G) dg_state"
    and vars :: "(pp \<times> unit) set" and x0 :: "pp \<times> unit"
    and seed_key :: "pp \<Rightarrow> unit \<Rightarrow> 'k"
    and is_bot :: "'D \<Rightarrow> bool"
    and rd :: "'D \<Rightarrow> 'a::sound_domain abs_state lifted"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result" +
  assumes gammaDG_rd: "\<And>d g'. gammaDG d g' = gamma_state_lift (rd d)"
    and classify_proved:
      "\<And>c d s. classify c d = Check_Proved \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>
        \<Longrightarrow> truthy (aval c s)"
    and classify_refuted:
      "\<And>c d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>
        \<Longrightarrow> \<not> truthy (aval c s)"
    and vars_finite: "finite vars"
begin

sublocale adapter: routed_analysis_sound S gammaDG gs g gk0 route_unit
    bot0 s0d s0g sigma vars x0 seed_key is_bot
    "call_context_rel_of_fun enterc_unit" rd classify
proof (rule routed_analysis_sound.intro, rule dg_analysis_adapter.intro)
  show "routed_context_base_hetero S gammaDG gs g gk0 route_unit
      bot0 s0d s0g sigma vars x0 (solved_local_reader vars sigma) seed_key
      (static_resolve g) is_bot (\<lambda>d. gamma_state_lift (rd d))
      (call_context_rel_of_fun enterc_unit)"
    by (rule routed.routed_context_base_hetero_axioms)
  show "dg_analysis_adapter_axioms gammaDG vars rd classify"
  proof (rule dg_analysis_adapter_axioms.intro)
    show "\<And>d g'. gammaDG d g' = gamma_state_lift (rd d)"
      by (rule gammaDG_rd)
  next
    show "\<And>c d s. classify c d = Check_Proved \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>
        \<Longrightarrow> truthy (aval c s)"
      by (rule classify_proved)
  next
    show "\<And>c d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>
        \<Longrightarrow> \<not> truthy (aval c s)"
      by (rule classify_refuted)
  next
    show "finite vars" by (rule vars_finite)
  qed
qed

end

end

