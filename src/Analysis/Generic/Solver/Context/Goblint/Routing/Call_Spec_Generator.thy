theory Call_Spec_Generator
  imports Call_Spec Exec_Cmp_Bridge
begin

section \<open>Wiring the call specification to the concrete CMP generator (Stage 0)\<close>

text \<open>
  Connects the pure-semantic \<^theory>\<open>Voblint_Analysis.Call_Spec\<close> to the seeded CMP
  generator \<^const>\<open>side_cfg_T_eff_cmp_seed\<close>.  This is generator machinery
  (\<^const>\<open>map_gtree\<close> / \<^const>\<open>map_ltree\<close> / \<^const>\<open>etf_combine\<close>), deliberately kept out of the
  specification layer so that \<^theory>\<open>Voblint_Analysis.Call_Spec\<close> stays purely semantic.
  This theory \<^emph>\<open>imports\<close> both \<open>Call_Spec\<close> and \<open>Exec_Cmp_Bridge\<close>: they are its ancestors
  (\<open>Call_Spec\<close> \<open>\<rightarrow>\<close> \<open>Call_Spec_Generator\<close> \<open>\<leftarrow>\<close> \<open>Exec_Cmp_Bridge\<close>), and it joins the semantic
  contract to the generator machinery those two supply.
\<close>

context goblint_analysis_spec
begin

text \<open>
  The combine \<^emph>\<open>builder\<close> is derived from the transfer's semantic combine
  \<^const>\<open>etf_combine\<close> and the routing key \<open>gkey\<close> --- not an arbitrary parameter, so the
  specification and the generated equation system cannot silently diverge.
\<close>

definition spec_cmb ::
  "(unit, 'a) effectful_domain_transfer \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree"
where
  "spec_cmb etf ctx cc ex =
     map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (etf_combine etf cc ex))"

text \<open>
  Bridge (\<open>entry_seed\<close> \<open>\<rightarrow>\<close> generator \<open>frame_seed\<close>): the spec's equation system is the seeded
  CMP generator with \<open>frame_seed := entry_seed\<close> and the derived combine builder
  \<^const>\<open>spec_cmb\<close>.  No arbitrary combine parameter remains.
\<close>

definition spec_generator ::
  "cfg \<Rightarrow> (unit, 'a) effectful_domain_transfer \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "spec_generator g etf bot0 s0 =
     side_cfg_T_eff_cmp_seed gkey (spec_cmb etf) entry_seed g etf bot0 s0"

text \<open>
  Realization: the derived builder \<^const>\<open>spec_cmb\<close> discharges the generator's combine
  obligation \<^const>\<open>switching_combine_sound\<close> against the semantic \<^const>\<open>etf_combine\<close> ---
  the concrete combine \<open>\<langle>_|_\<rangle>\<close> that a Stage-0.5 \<open>return_merge\<close> would abstract.  Reuses
  \<open>fixed_combine_satisfies_switching_combine_sound\<close>; no new mathematics.

  Frame independence: \<^const>\<open>switching_combine_sound\<close> is stated over the fixed-frame
  generator \<^const>\<open>side_cfg_T_eff_cmp\<close> and is \<^emph>\<open>schematic in the frame\<close> \<open>fr\<close> --- it holds
  for \<^emph>\<open>every\<close> frame.  Hence the specific frame the seed generator \<^const>\<open>spec_generator\<close>
  installs (the context-dependent \<open>entry_seed\<close>, whose per-context values are frames of
  this same kind) cannot affect combine soundness: the combine bound never reads the
  frame.  The seed enters the run only through the entry / proc-entry premises of
  \<open>context_collecting_sound\<close>, not through the combine obligation.
\<close>

lemma spec_cmb_realizes_combine:
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
    and fr :: "'a abs_state"
  assumes "finite (combines g)"
  shows "switching_combine_sound gkey (spec_cmb etf) g etf fr bot0 s0"
  unfolding spec_cmb_def
  by (rule fixed_combine_satisfies_switching_combine_sound[OF assms])

end

end
