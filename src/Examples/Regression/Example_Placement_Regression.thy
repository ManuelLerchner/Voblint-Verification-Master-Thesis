section \<open>Placement and storage are independent axes\<close>

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

definition storage_program :: imp_prog where
  "storage_program = program {
     global total;
     void main() { Glocal := 1; total := total + Glocal }
   }"

abbreviation storage_gs :: "vname \<Rightarrow> bool" where
  "storage_gs \<equiv> declared_global storage_program"

text \<open>Case 1: a declared global with no naming hint at all.\<close>
lemma storage_total_global [simp]: "storage_gs (STR ''total'')"
  by (simp add: storage_program_def)

text \<open>Case 2: a \<open>G\<close>-spelled local, correctly classified as not global.\<close>
lemma storage_glocal_not_global [simp]: "\<not> storage_gs (STR ''Glocal'')"
  by (simp add: storage_program_def)

text \<open>Case 3: the mixed program computes a real, non-trivial result: \<open>total\<close>
  starts at the \<open>SZero\<close> global seed, \<open>Glocal\<close> is locally \<open>1\<close> (\<open>SPos\<close>), and
  \<open>SZero \<squnion> SPos = SNonNeg\<close>.\<close>
lemma storage_total_result:
  "case_lifted bot (\<lambda>\<sigma>. \<sigma>) (sign_exec_prog storage_gs (STR ''main'') storage_program) (STR ''total'') = SNonNeg"
  by eval

subsection \<open>4. Classic exclusive placement\<close>

text \<open>The storage-derived split: every global published-only, every local
  kept-only. Sound because \<^const>\<open>classic_split_keep_local\<close>/
  \<^const>\<open>classic_split_publish_side\<close> cover every location.\<close>

lemma storage_reserved_ret_var [simp]: "reserved_ret_var storage_gs"
  unfolding reserved_ret_var_def by (simp add: storage_program_def ret_var_def)

lemma storage_sound_classic:
  "sound_dg_spec (unit_dg_spec_for storage_gs (sign_tf_for storage_gs)) (gamma_unit storage_gs) storage_gs"
  by (rule sound_dg_spec_unit_for[OF sign_is_sound_transfer_for storage_reserved_ret_var])

lemma storage_classic_placement_sound:
  "sound_dg_spec
     (unit_dg_spec_placed storage_gs (classic_split_keep_local storage_gs)
        (classic_split_publish_side storage_gs) (sign_tf_for storage_gs))
     gamma_join storage_gs"
  by (rule sound_dg_spec_unit_placed[OF sign_is_sound_transfer_for classic_split_cover])

subsection \<open>5. Conjunctive \<open>keep_local\<close> \<open>\<and>\<close> \<open>publish_side\<close> placement\<close>

text \<open>\<open>total\<close> is both kept locally (a private, precisely strong-updated
  per-activation view) and published (a joined summary for other
  activations) -- the two-copies shape exclusivity cannot express, and the
  exact case \<open>Sign_DG.sign_dg_privatized\<close> validates concretely for an
  assignment step.\<close>

definition storage_keep_all :: "vname \<Rightarrow> bool" where
  "storage_keep_all x = True"

lemma storage_keep_all_cover: "\<forall>x. storage_gs x \<or> storage_keep_all x"
  unfolding storage_keep_all_def by simp

lemma storage_conjunctive_placement_sound:
  "sound_dg_spec
     (unit_dg_spec_placed storage_gs storage_keep_all storage_gs (sign_tf_for storage_gs))
     gamma_join storage_gs"
  by (rule sound_dg_spec_unit_placed[OF sign_is_sound_transfer_for storage_keep_all_cover])

subsection \<open>6. Storage-independent placement behavior\<close>

text \<open>A placement policy that inverts the classic split relative to storage
  -- globals kept, locals published -- is exactly as sound as the classic
  split or the conjunctive one, for the same reason: \<open>sound_dg_spec_unit_placed\<close>
  never consults \<open>storage_gs\<close> when checking a \<open>keep_local\<close>/\<open>publish_side\<close> pair,
  only that the pair covers every location. Placement soundness is
  storage-independent by construction, not by coincidence of this example.\<close>

definition storage_keep_swapped :: "vname \<Rightarrow> bool" where
  "storage_keep_swapped x = storage_gs x"

definition storage_publish_swapped :: "vname \<Rightarrow> bool" where
  "storage_publish_swapped x = (\<not> storage_gs x)"

lemma storage_swapped_cover: "\<forall>x. storage_publish_swapped x \<or> storage_keep_swapped x"
  unfolding storage_publish_swapped_def storage_keep_swapped_def by simp

lemma storage_swapped_placement_sound:
  "sound_dg_spec
     (unit_dg_spec_placed storage_gs storage_keep_swapped storage_publish_swapped (sign_tf_for storage_gs))
     gamma_join storage_gs"
  by (rule sound_dg_spec_unit_placed[OF sign_is_sound_transfer_for storage_swapped_cover])

end

