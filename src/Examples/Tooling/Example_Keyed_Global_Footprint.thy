theory Example_Keyed_Global_Footprint
  imports
    "Voblint_Framework.DG_Keyed_Split_Spec"
begin

section \<open>Keyed globals: an edge depends on what it reads and publishes what it writes\<close>

text \<open>
  Two declared globals \<open>g\<close> and \<open>h\<close>. Under the keyed lifter an edge's program
  depends on its source point and on the unknowns of the globals its expressions
  mention, and it publishes exactly at the unknowns of the globals it may assign.
  Updating \<open>h\<close> therefore cannot destabilize a point that reads only \<open>g\<close>: no
  equation reading \<open>g\<close> names \<open>h\<close>'s unknown.
\<close>

definition gh :: "vname \<Rightarrow> bool" where "gh x \<longleftrightarrow> x \<in> {STR ''g'', STR ''h''}"

abbreviation read_g :: edge_action where
  "read_g \<equiv> EA_Assign (STR ''x'') (Plus (V (STR ''g'')) (N 1))"

abbreviation write_h :: edge_action where
  "write_h \<equiv> EA_Assign (STR ''h'') (N 1)"

lemma read_g_footprint:
  "edge_global_reads gh read_g = [STR ''g'']" "edge_global_writes gh read_g = []"
  by (simp_all add: gh_def edge_global_reads_def edge_global_writes_def edge_reads_def
      global_names_in_def)

lemma write_h_footprint:
  "edge_global_reads gh write_h = []" "edge_global_writes gh write_h = [STR ''h'']"
  by (simp_all add: gh_def edge_global_reads_def edge_global_writes_def edge_reads_def
      global_names_in_def)

text \<open>The keyed program for \<open>x := g + 1\<close> depends on \<open>g\<close>'s unknown and nothing else global.\<close>

lemma read_g_depends_on_g_only:
  "dep_program \<tau> (transfer_program (keyed_transfer cmb rl rg free
      (edge_global_reads gh read_g) (edge_global_writes gh read_g) f) src key)
     = {src, Inr (key (STR ''g''))}"
  by (simp add: dep_keyed_transfer read_g_footprint)

text \<open>The keyed program for \<open>h := 1\<close> publishes at \<open>h\<close>'s unknown and nowhere else.\<close>

lemma write_h_publishes_h_only:
  "side_path \<tau> (sp_compile (transfer_program (keyed_transfer cmb rl rg free
      (edge_global_reads gh write_h) (edge_global_writes gh write_h) f) src key))
     = [key (STR ''h'')]"
  by (simp add: side_path_keyed_transfer write_h_footprint)

end
