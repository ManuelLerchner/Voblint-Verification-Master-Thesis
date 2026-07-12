theory Sign_Call_Spec
  imports "Voblint_Analysis.Call_Spec" Sign_Side_Soundness
begin

section \<open>Sign instance of the Goblint-inspired call specification (Stage 0)\<close>

text \<open>
  The current CMP sign path as the first \<^locale>\<open>cmp_generator_soundness\<close> interpretation:
  the unit-global, monovariant instance.  Contract fields:
  \<^item> \<open>entry_seed = (\<lambda>_. fresh_frame_sign)\<close> --- the CMP frame seed, context-independent
    (the constant is the degenerate unit-context case of \<open>'c \<Rightarrow> 'a abs_state\<close>);
  \<^item> \<open>gkey = (\<lambda>_. ())\<close>, \<open>gcmp = (\<lambda>_ _. True)\<close> --- the single unit global slot;
  \<^item> \<open>dg\<close>, \<open>cmp\<close>, \<open>entdg\<close> trivial for the unit context.

  The merge is fixed to \<open>combine_abs\<close> (an analysis-varied \<open>return_merge\<close> is deferred to
  Stage 0.5).  Every assumption is discharged trivially: \<open>reads_own_slot\<close> and the digest
  laws hold for the unit instance.
\<close>

interpretation Sign_spec:
  cmp_generator_soundness
    "()"                       \<comment> \<open>start_context\<close>
    "\<lambda>_. id"                   \<comment> \<open>prep\<close>
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
  candidate-solution premises.  It is \<open>cmp_generator_soundness.cmp_generator_sound\<close>
  specialised to the sign fields.
\<close>

thm Sign_spec.cmp_generator_sound

end
