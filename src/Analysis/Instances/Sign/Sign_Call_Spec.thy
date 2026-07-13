theory Sign_Call_Spec
  imports "Voblint_Analysis.Call_Spec_Sound" "Voblint_Analysis.Split_Cmp_Gen"
    Sign_Side_Soundness
begin

section \<open>Sign instance of the Goblint-inspired call specification (Stage 0)\<close>

text \<open>
  The current CMP sign path as the first \<^locale>\<open>context_collecting_soundness\<close>
  interpretation: the unit-global, monovariant instance.  Contract fields:
  \<^item> \<open>entry_seed = (\<lambda>_. fresh_frame_sign)\<close> --- the CMP frame seed, context-independent
    (the constant is the degenerate unit-context case of \<open>'c \<Rightarrow> 'a abs_state\<close>);
  \<^item> \<open>gkey = (\<lambda>_. ())\<close>, \<open>gcmp = (\<lambda>_ _. True)\<close> --- the single unit global slot;
  \<^item> \<open>dg\<close>, \<open>cmp\<close>, \<open>entdg\<close> trivial for the unit context.

  The merge is fixed to \<open>combine_abs\<close> (an analysis-varied \<open>return_merge\<close> is deferred to
  Stage 0.5).  Every assumption is discharged trivially: \<open>reads_own_slot\<close> and the digest
  laws hold for the unit instance.
\<close>

interpretation Sign_spec:
  context_collecting_soundness
    "()"                       \<comment> \<open>start_context\<close>
    "\<lambda>_ s. s"                  \<comment> \<open>prep\<close>
    "\<lambda>_ _ _. ()"               \<comment> \<open>ctx_sel\<close>
    "\<lambda>_. ()"                   \<comment> \<open>entdg\<close>
    "\<lambda>_ _. True"               \<comment> \<open>cmp\<close>
    "\<lambda>_. fresh_frame_sign"     \<comment> \<open>entry_seed\<close>
    "\<lambda>_. ()"                   \<comment> \<open>gkey\<close>
    "\<lambda>_ _. True"               \<comment> \<open>gcmp\<close>
    "\<lambda>_. ()"                   \<comment> \<open>dg\<close>
  by unfold_locales simp_all

text \<open>
  The premise-level endpoint: \<open>context_collecting_soundness.context_collecting_sound\<close>
  specialised to the sign fields, for candidate solutions certified by the six premises
  directly (the digest-precise route).  Post-fixpoints of the configured generator use
  \<open>sign_spec_post_fixpoint_sound\<close> below instead, which needs none of the six.
\<close>

thm Sign_spec.context_collecting_sound

subsection \<open>The configured generator this instance runs\<close>

text \<open>
  Connecting the specification to the actual generator: the sign monovariant path's
  combine builder \<^const>\<open>Sign_spec.spec_cmb\<close> reduces --- via @{thm sign_etf_combine_tree}
  and the unit routing key --- to the concrete fixed unit combine over \<^const>\<open>sign_etf\<close>.
  So \<^const>\<open>Sign_spec.spec_generator\<close> is exactly the seeded CMP generator
  \<^const>\<open>side_cfg_T_eff_cmp_seed\<close> instantiated with the sign fields: unit routing key,
  this derived combine builder, and the constant frame seed \<^const>\<open>fresh_frame_sign\<close>.
  The specification wrapper and the configured equation system cannot diverge.
\<close>

lemma Sign_spec_cmb_eq:
  "Sign_spec.spec_cmb sign_etf
     = (\<lambda>ctx cc ex. map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ctx)) (unit_combine_tree cc ex)))"
  by (rule ext)+ (simp add: Sign_spec.spec_cmb_def sign_etf_combine_tree)

lemma Sign_spec_generator_eq:
  "Sign_spec.spec_generator g sign_etf bot0 s0
     = side_cfg_T_eff_cmp_seed (\<lambda>_. ())
         (\<lambda>ctx cc ex. map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ctx)) (unit_combine_tree cc ex)))
         (\<lambda>_. fresh_frame_sign) g sign_etf bot0 s0"
  by (simp add: Sign_spec.spec_generator_def Sign_spec_cmb_eq)

subsection \<open>The Stage-0.5 endpoint: soundness from a post-fixpoint alone\<close>

text \<open>
  The Sign instance of \<open>spec_post_fixpoint_collecting_sound\<close>: a post-fixpoint of the
  configured generator \<^const>\<open>Sign_spec.spec_generator\<close> (at the framed unit transfer
  \<^const>\<open>sign_etf_unit\<close>) yields collecting soundness with \<^emph>\<open>no\<close> restatement of the six
  candidate-solution premises.  The spec-level obligations are discharged once:
  \<^item> \<open>seed_const\<close> --- the interpretation's \<open>entry_seed\<close> is literally \<open>(\<lambda>_. fresh_frame_sign)\<close>;
  \<^item> transfer soundness --- @{thm [source] sign_sound_etf_unit_framed};
  routing rides on the locale's \<open>reads_own_slot\<close> (trivial for the unit key).
  What remains are the standard solution well-formedness side conditions
  (slot invariants, start cover, finiteness, variable covers).
\<close>

theorem sign_spec_post_fixpoint_sound:
  fixes sigma :: "pp \<times> unit + unit \<Rightarrow> sign abs_state"
  assumes pp: "part_post_solution (Sign_spec.spec_generator g sign_etf_unit bot0 s0) x sigma vars"
    and inr: "inr_slot_locals_bot_ctx sigma"
    and inl: "inl_slot_globals_bot_ctx sigma"
    and S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_comb: "\<And>cc ex ret. (cc, ex, ret) \<in> combines g \<Longrightarrow> (ret, ()) \<in> vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
  shows "cfg_collect_ctx (\<lambda>_. ()) (\<lambda>_ _. True) g S v0 ()
           \<le> \<lbrakk>side_env_cmp (\<lambda>_ _. True) sigma (v0, ())\<rbrakk>"
  by (rule Sign_spec.spec_post_fixpoint_collecting_sound
        [OF refl sign_sound_etf_unit_framed inr inl S_sound pp finE finC
            cover_edge cover_comb cover_entry])

subsection \<open>Stage 1B: the sign instance through the split-state generator\<close>

text \<open>
  The sign transfer packaged through the split-state tree factory of
  \<^theory>\<open>Voblint_Analysis.Split_Cmp_Gen\<close>.  It is \<^emph>\<open>equal\<close> to the unit
  record \<^const>\<open>sign_etf_unit\<close>, so the migrated generator
  \<^const>\<open>Sign_spec.spec_generator_split\<close> produces the same equation system,
  the same post-fixpoints, and the same executable results as the original
  \<^const>\<open>Sign_spec.spec_generator\<close> path.
\<close>

definition sign_etf_split :: "(unit, sign) effectful_domain_transfer" where
  "sign_etf_split = split_etf_of_transfer sign_tf"

lemma sign_etf_split_eq_unit: "sign_etf_split = sign_etf_unit"
  unfolding sign_etf_split_def sign_etf_unit_def
  by (rule split_etf_of_transfer_eq_unit)

theorem Sign_spec_generator_split_eq:
  "Sign_spec.spec_generator_split g sign_etf_split bot0 s0
   = Sign_spec.spec_generator g sign_etf_unit bot0 s0"
  by (simp add: Sign_spec.spec_generator_split_eq sign_etf_split_eq_unit)

text \<open>
  The Stage-0.5 endpoint restated through the migrated generator: identical
  premises, identical conclusion --- discharged by rewriting the post-fixpoint
  along the generator equality.
\<close>

theorem sign_spec_post_fixpoint_sound_split:
  fixes sigma :: "pp \<times> unit + unit \<Rightarrow> sign abs_state"
  assumes pp: "part_post_solution
                 (Sign_spec.spec_generator_split g sign_etf_split bot0 s0) x sigma vars"
    and inr: "inr_slot_locals_bot_ctx sigma"
    and inl: "inl_slot_globals_bot_ctx sigma"
    and S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_comb: "\<And>cc ex ret. (cc, ex, ret) \<in> combines g \<Longrightarrow> (ret, ()) \<in> vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
  shows "cfg_collect_ctx (\<lambda>_. ()) (\<lambda>_ _. True) g S v0 ()
           \<le> \<lbrakk>side_env_cmp (\<lambda>_ _. True) sigma (v0, ())\<rbrakk>"
  by (rule sign_spec_post_fixpoint_sound
        [OF pp[unfolded Sign_spec_generator_split_eq] inr inl S_sound finE finC
            cover_edge cover_comb cover_entry])

end
