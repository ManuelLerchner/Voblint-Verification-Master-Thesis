section \<open>M4.8 -- placement/storage independence regression suite\<close>

theory Example_Placement_Regression
  imports
    "Voblint_Analysis.Sign_DG"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

text \<open>
  Six compact cases validating that a variable's declared storage class
  (\<^const>\<open>declared_global\<close>) and its D/G placement (\<open>keep_local\<close>/\<open>publish_side\<close>)
  are independent axes: neither is a function of spelling, and placement
  soundness never inspects storage beyond the covering side-condition. One
  small program carries cases 1-3; cases 4-6 instantiate three different
  placement policies over that same program and its same soundness obligation.
\<close>

subsection \<open>1-3. A mixed program: non-\<open>G\<close> global, \<open>G\<close>-spelled local\<close>

definition m48_program :: imp_prog where
  "m48_program = program {
     global total;
     void main() { Glocal := 1; total := total + Glocal }
   }"

abbreviation m48_gs :: "vname \<Rightarrow> bool" where
  "m48_gs \<equiv> declared_global m48_program"

text \<open>Case 1: a declared global with no naming hint at all.\<close>
lemma m48_total_global [simp]: "m48_gs (STR ''total'')"
  by (simp add: m48_program_def)

text \<open>Case 2: a \<open>G\<close>-spelled local, correctly classified as not global.\<close>
lemma m48_glocal_not_global [simp]: "\<not> m48_gs (STR ''Glocal'')"
  by (simp add: m48_program_def)

text \<open>Case 3: the mixed program computes a real, non-trivial result: \<open>total\<close>
  starts at the \<open>SZero\<close> global seed, \<open>Glocal\<close> is locally \<open>1\<close> (\<open>SPos\<close>), and
  \<open>SZero \<squnion> SPos = SNonNeg\<close>.\<close>
lemma m48_total_result: "sign_exec_prog m48_gs (STR ''main'') m48_program (STR ''total'') = SNonNeg"
  by eval

subsection \<open>4. Classic exclusive placement\<close>

text \<open>The storage-derived split: every global published-only, every local
  kept-only. Sound because \<^const>\<open>classic_split_keep_local\<close>/
  \<^const>\<open>classic_split_publish_side\<close> cover every location.\<close>

lemma m48_sound_classic:
  "sound_dg_spec (unit_dg_spec_for m48_gs (sign_tf_for m48_gs)) gamma_unit m48_gs"
  by (rule sound_dg_spec_unit_for[OF sign_is_sound_transfer_for])

lemma m48_classic_placement_sound:
  "sound_dg_spec
     (unit_dg_spec_placed m48_gs (classic_split_keep_local m48_gs)
        (classic_split_publish_side m48_gs) (sign_tf_for m48_gs))
     gamma_unit m48_gs"
  by (rule sound_dg_spec_unit_placed[OF sign_is_sound_transfer_for classic_split_cover])

subsection \<open>5. Conjunctive \<open>keep_local\<close> \<open>\<and>\<close> \<open>publish_side\<close> placement\<close>

text \<open>\<open>total\<close> is both kept locally (a private, precisely strong-updated
  per-activation view) and published (a joined summary for other
  activations) -- the two-copies shape exclusivity cannot express, and the
  exact case \<open>Sign_DG.sign_dg_privatized\<close> validates concretely for an
  assignment step.\<close>

definition m48_keep_all :: "vname \<Rightarrow> bool" where
  "m48_keep_all x = True"

lemma m48_keep_all_cover: "\<forall>x. m48_gs x \<or> m48_keep_all x"
  unfolding m48_keep_all_def by simp

lemma m48_conjunctive_placement_sound:
  "sound_dg_spec
     (unit_dg_spec_placed m48_gs m48_keep_all m48_gs (sign_tf_for m48_gs))
     gamma_unit m48_gs"
  by (rule sound_dg_spec_unit_placed[OF sign_is_sound_transfer_for m48_keep_all_cover])

subsection \<open>6. Storage-independent placement behavior\<close>

text \<open>A placement policy that inverts the classic split relative to storage
  -- globals kept, locals published -- is exactly as sound as the classic
  split or the conjunctive one, for the same reason: \<open>sound_dg_spec_unit_placed\<close>
  never consults \<open>m48_gs\<close> when checking a \<open>keep_local\<close>/\<open>publish_side\<close> pair,
  only that the pair covers every location. Placement soundness is
  storage-independent by construction, not by coincidence of this example.\<close>

definition m48_keep_swapped :: "vname \<Rightarrow> bool" where
  "m48_keep_swapped x = m48_gs x"

definition m48_publish_swapped :: "vname \<Rightarrow> bool" where
  "m48_publish_swapped x = (\<not> m48_gs x)"

lemma m48_swapped_cover: "\<forall>x. m48_publish_swapped x \<or> m48_keep_swapped x"
  unfolding m48_publish_swapped_def m48_keep_swapped_def by simp

lemma m48_swapped_placement_sound:
  "sound_dg_spec
     (unit_dg_spec_placed m48_gs m48_keep_swapped m48_publish_swapped (sign_tf_for m48_gs))
     gamma_unit m48_gs"
  by (rule sound_dg_spec_unit_placed[OF sign_is_sound_transfer_for m48_swapped_cover])

end
