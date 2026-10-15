theory Example_Keyed_Global_Footprint
  imports
    "Voblint_Framework.DG_Keyed_Split_Spec"
begin

section \<open>Keyed globals: an edge depends on what it reads and publishes what it writes\<close>

text \<open>
  Two globals \<open>g\<close> and \<open>h\<close> of core VIMP, the \<^const>\<open>GlobalId\<close> identities, and a
  procedure-scoped local \<open>x\<close>. Under the keyed lifter an edge's program depends on its
  source point and on the unknowns of the globals its expressions mention, and it
  publishes exactly at the unknowns of the globals it may assign. The footprints are the
  generic \<^const>\<open>gedge_global_reads\<close> and \<^const>\<open>gedge_global_writes\<close> at the parameters
  the analyzer uses: \<^const>\<open>exp_vars\<close>, the return slot \<^const>\<open>ReturnVar\<close> and
  \<^const>\<open>is_global\<close>. Updating \<open>h\<close> therefore cannot destabilize a point that reads only
  \<open>g\<close>: no equation reading \<open>g\<close> names \<open>h\<close>'s unknown.
\<close>

abbreviation g_id :: var_id where "g_id \<equiv> GlobalId (STR ''g'')"
abbreviation h_id :: var_id where "h_id \<equiv> GlobalId (STR ''h'')"

text \<open>\<open>x := g + 1\<close> and \<open>h := 1\<close>, at the 32-bit signed kind.\<close>

abbreviation read_g :: "(var_id, exp) gedge_action" where
  "read_g \<equiv> EA_Assign (ScopedId (STR ''main'') (STR ''x''))
     (TArith I32 AAdd (TVar I32 g_id) (TN I32 1))"

abbreviation write_h :: "(var_id, exp) gedge_action" where
  "write_h \<equiv> EA_Assign h_id (TN I32 1)"

lemma read_g_footprint:
  "gedge_global_reads exp_vars is_global read_g = [g_id]"
  "gedge_global_writes ReturnVar is_global read_g = []"
  by (simp_all add: gedge_global_reads_def gedge_global_writes_def gedge_reads_def
      cfg_transfer_sem.gedge_writes.simps global_names_in_def)

lemma write_h_footprint:
  "gedge_global_reads exp_vars is_global write_h = []"
  "gedge_global_writes ReturnVar is_global write_h = [h_id]"
  by (simp_all add: gedge_global_reads_def gedge_global_writes_def gedge_reads_def
      cfg_transfer_sem.gedge_writes.simps global_names_in_def)

text \<open>The keyed program for \<open>x := g + 1\<close> depends on \<open>g\<close>'s unknown and nothing else global.\<close>

lemma read_g_depends_on_g_only:
  "dep_program \<tau> (transfer_program (keyed_transfer cmb rl rg free
      (gedge_global_reads exp_vars is_global read_g)
      (gedge_global_writes ReturnVar is_global read_g) f) src key)
     = {src, Inr (key g_id)}"
  by (simp add: dep_transfer_program keyed_transfer_def read_g_footprint
      sp_compile_with_def sp_bind_def sp_return_def)

text \<open>The keyed program for \<open>h := 1\<close> publishes at \<open>h\<close>'s unknown and nowhere else.\<close>

lemma write_h_publishes_h_only:
  "side_path \<tau> (sp_compile (transfer_program (keyed_transfer cmb rl rg free
      (gedge_global_reads exp_vars is_global write_h)
      (gedge_global_writes ReturnVar is_global write_h) f) src key))
     = [key h_id]"
  by (cases src)
     (simp_all add: write_h_footprint transfer_program_def transfer_program_at_def
        keyed_transfer_def sp_compile_def sp_compile_with_def sp_map_def sp_bind_def
        sp_return_def dg_read_at_def sp_read_local_def sp_read_global_def dg_sideg_def
        sp_publish_def)

end
