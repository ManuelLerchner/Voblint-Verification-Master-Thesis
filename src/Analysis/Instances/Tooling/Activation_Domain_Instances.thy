theory Activation_Domain_Instances
  imports
    "../../Generic/Solver/Context/Goblint/Routing/Support/Activation/Seeded_Activation_Sound"
    "../../Generic/Solver/Context/Goblint/Routing/Support/Activation/Activation_Witness_From"
    "../Sign/Sign_Transfer"
    "../Interval/Interval_Transfer"
begin

section \<open>Domain instances of the activation-aware seeded soundness theorem\<close>

text \<open>
  Stage 3: instantiate the generic \<open>seeded_activation_collecting_sound_cover\<close>
  (\<^theory>\<open>Voblint_Analysis.Seeded_Activation_Sound\<close>) for the two shipped domains.
  The locale-level theorem specialises to each concrete transfer through the domain's
  \<^locale>\<open>sound_transfer\<close> interpretation; the only remaining per-domain obligation is the
  \<^emph>\<open>zero point\<close> fact \<open>0 \<in> gamma pz\<close> that the covering seed uses to cover the zeroed
  callee-entry locals.  Both are one-liners: \<open>SZero\<close> / \<open>Ivl (Fin 0) (Fin 0)\<close> are the
  point abstractions of \<open>0\<close>.
\<close>

subsection \<open>Sign\<close>

lemmas sign_activation_collecting_sound_cover =
  sound_transfer.seeded_activation_collecting_sound_cover[OF sign_is_sound_transfer]

lemma sign_zero_point: "(0::int) \<in> gamma (SZero :: sign)"
  by simp

subsection \<open>Interval\<close>

lemmas ivl_activation_collecting_sound_cover =
  sound_transfer.seeded_activation_collecting_sound_cover[OF ivl_is_sound_transfer]

lemma ivl_zero_point: "(0::int) \<in> gamma (Ivl (Fin 0) (Fin 0) :: ivl)"
  by simp

subsection \<open>Returning witnesses\<close>

text \<open>The from-node returning witness theorem is specialised to each shipped domain.  It
  uses the same seeded post-solution obligations as the activation trace theorem, but the
  callee side of a return is a frame-entry suffix witness.\<close>

lemmas sign_twfr_sound_seeded =
  sound_transfer.twfr_sound_seeded[OF sign_is_sound_transfer]

lemmas ivl_twfr_sound_seeded =
  sound_transfer.twfr_sound_seeded[OF ivl_is_sound_transfer]

end
