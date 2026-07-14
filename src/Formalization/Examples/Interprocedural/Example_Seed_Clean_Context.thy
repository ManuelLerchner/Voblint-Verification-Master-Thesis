theory Example_Seed_Clean_Context
  imports Exec_Sign_Cmp_Seed_Sound
begin

section \<open>Native DG seeded-clean context probe\<close>

text \<open>
  The seeded-clean context probe now rides the native DG witness directly.  The
  example keeps the concrete two-call program and the per-context separation
  result.
\<close>

theorem seed_clean_example_runs:
  "twfr enterc combc seed_cfg 0 (seed_locg 0 seed_ctx_zero) 1
     (seed_locg 0 seed_ctx_zero) [gk 0, gk 1]"
  by (rule seed_clean_witness_runs)

theorem seed_clean_example_sound:
  "\<exists>tr. twfr enterc combc seed_cfg 0 (seed_locg 0 seed_ctx_zero) 1
          (seed_locg 0 seed_ctx_zero) tr \<and> tr \<noteq> []
     \<and> last tr ''G'' \<in> gamma_sign (seed_locg 1 seed_ctx_zero ''G'')"
  by (rule seed_clean_witness_sound)

theorem seed_clean_example_context_split:
  "sign_dg.dg_G_c seed_dg seed_ctx_zero = seed_slot seed_ctx_zero
   \<and> sign_dg.dg_G_c seed_dg seed_ctx_pos = seed_slot seed_ctx_pos"
  by (simp add: dg_G_val)

text \<open>
  This is the surviving architectural point: contexts are separated by the DG
  witness itself, and the concrete execution checks the DG concretization
  directly.
\<close>

end
