theory Sign_Call_Spec
  imports "Voblint_Analysis.Call_Spec_Generator" Sign_Side_Soundness
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
  The delivered soundness endpoint for this instance: a post-fixpoint of the keyed
  generator over-approximates the context-sliced collecting semantics, given the six
  candidate-solution premises.  It is \<open>context_collecting_soundness.context_collecting_sound\<close>
  specialised to the sign fields.
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

end
