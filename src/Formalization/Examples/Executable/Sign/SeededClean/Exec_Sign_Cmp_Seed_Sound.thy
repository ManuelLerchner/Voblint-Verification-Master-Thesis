theory Exec_Sign_Cmp_Seed_Sound
  imports Exec_Sign_Cmp_Seed_Enter
begin

section \<open>Native DG seeded-clean witness, surfaced for consumers\<close>

text \<open>
  This theory is now a thin native-DG summary of the seeded-enter probe.  It
  exposes the DG witness and the concrete soundness theorem under the old
  theory name so the remaining consumers can be retargeted incrementally.
\<close>

lemma seed_clean_witness_runs: "twfr enterc combc seed_cfg 0 (seed_locg 0 seed_ctx_zero) 1
     (seed_locg 0 seed_ctx_zero) [gk 0, gk 1]"
  by (rule seed_wit)

lemma seed_clean_witness_sound: "\<exists>tr. twfr enterc combc seed_cfg 0 (seed_locg 0 seed_ctx_zero) 1
          (seed_locg 0 seed_ctx_zero) tr \<and> tr \<noteq> []
     \<and> last tr ''G'' \<in> gamma_sign (seed_locg 1 seed_ctx_zero ''G'')"
  by (rule seed_wit_sound)

lemma seed_clean_contexts_separated:
  "sign_dg.dg_G_c seed_dg seed_ctx_zero \<noteq> sign_dg.dg_G_c seed_dg seed_ctx_pos"
  by (rule contexts_separated)

end
