theory Example_Config_Mode_Digest_Precision
  imports
    "Voblint_Analysis.Exec_Sign_RD_Keyed_Solve"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_IMP2.IMP2_Notation"
begin

section \<open>Showcase: the digest-indexed analysis, against the baseline it replaces\<close>

text \<open>
  A configuration \<^emph>\<open>mode\<close> lives in the global \<open>G\<close>.  \<open>main\<close> sets it, calls \<open>configure\<close>, and reads
  the result --- \<^emph>\<open>twice\<close>, under \<open>G = 0\<close> then \<open>G = 1\<close>.  \<open>configure\<close> branches on the mode.  The
  two \<open>G\<close> writes are two \<^emph>\<open>definition sites\<close>: \<^const>\<open>DS1\<close> (\<open>G := 0\<close>) and \<^const>\<open>DS3\<close> (\<open>G := 1\<close>).

  The example is a two-panel comparison, each panel machine-checked by \<open>eval\<close>:
  \<^item> \<^bold>\<open>Panel A\<close> --- the previous \<^emph>\<open>context-insensitive\<close> pipeline.  It renders a full annotated CFG,
    but the global \<open>G\<close> is a single shared slot (\<^const>\<open>SNonNeg\<close>): both calls merge, both branches
    stay live, every result is \<^const>\<open>SNonNeg\<close>.  The failure the migration fixes.
  \<^item> \<^bold>\<open>Panel B\<close> --- the digest-indexed reaching-definition read.  It keys the two writes to
    separate def-site slots (\<^const>\<open>SZero\<close> / \<^const>\<open>SPos\<close>) and reads each precisely.  The fix.

  A single \<^emph>\<open>fully-integrated\<close> picture --- one CFG whose every node is annotated by its digest read
  --- is not yet buildable; the closing remark says exactly why, and that the gap is tooling, not
  soundness.
\<close>

subsection \<open>The program\<close>

text \<open>\<open>G\<close> is the mode (a global; \<open>G\<close>-prefixed names are global).  \<open>configure\<close> branches on the mode
  and writes the result global \<open>GResult\<close>; \<open>main\<close> calls it under \<open>G = 0\<close> then \<open>G = 1\<close>.\<close>

definition config_program :: imp_prog where
  "config_program = \<lbrakk>
     int G , GResult ;

     void configure() {
       if (0 < G) { GResult := 1 } else { GResult := 0 }
     }

     void main() {
       G := 0;  configure();  safe_result := GResult;
       G := 1;  configure();  fast_result := GResult
     }
   \<rbrakk>"

lemma config_program_one_proc: "prog_procs config_program = [''configure'']"
  by (simp add: config_program_def)

subsection \<open>Panel A: the context-insensitive baseline (the failure)\<close>

text \<open>
  The certified sign pipeline (\<^const>\<open>sign_exec_prog\<close>) analyses \<open>configure\<close> once for both calls
  and keeps \<open>G\<close> in one flow-insensitive slot.  Both calls therefore return \<^const>\<open>SNonNeg\<close>, and
  the annotated CFG shows the two \<^const>\<open>EA_Enter\<close> edges into the shared body with both branches
  live and the global slot \<open>G = \<close>@{const SNonNeg}.
\<close>

lemma baseline_safe_result: "sign_exec_prog config_program ''safe_result'' = SNonNeg"
  by eval

lemma baseline_fast_result: "sign_exec_prog config_program ''fast_result'' = SNonNeg"
  by eval

lemma baseline_indistinguishable:
  "sign_exec_prog config_program ''safe_result'' = sign_exec_prog config_program ''fast_result''"
  by (simp add: baseline_safe_result baseline_fast_result)

text \<open>The annotated CFG (both calls share one \<open>configure\<close> body; \<open>G = \<close>@{const SNonNeg}; both
  branches live).\<close>
ML_val \<open>
  writeln (@{code sign_annotated_dot_prog_lit} @{code config_program})
\<close>

subsection \<open>Panel B: the digest-indexed reaching-definition read (the fix)\<close>

text \<open>
  The reaching-definition analysis routes each global write to its own \<^type>\<open>def_site\<close> slot ---
  the executable equation system \<^const>\<open>rd_eqs\<close>, run through the vendored side solver as
  \<^const>\<open>rd_solution\<close>.  The two writes never join at publication:
\<close>

value "snd rd_solution (Inr DS1)"
value "snd rd_solution (Inr DS3)"

lemma slot_first_write:  "lookup_st (snd rd_solution (Inr DS1)) ''G'' = SZero" by (rule slot_DS1)
lemma slot_second_write: "lookup_st (snd rd_solution (Inr DS3)) ''G'' = SPos"  by (rule slot_DS3)

text \<open>
  The digest read at a point filters the def-site slots by the point's reaching set: reaching
  \<^const>\<open>DS1\<close> recovers \<^const>\<open>SZero\<close>, reaching \<^const>\<open>DS3\<close> recovers \<^const>\<open>SPos\<close>.  The first call's
  read sees only its own write, the second sees only its own --- the modes are kept apart where
  Panel A merged them.
\<close>

theorem first_call_reads_mode_zero:
  "glob_env_cmp (\<lambda>_ g. rd_compatible {DS1} g) () rd_env ''G'' = SZero"
  by (rule read_reach_DS1)

theorem second_call_reads_mode_pos:
  "glob_env_cmp (\<lambda>_ g. rd_compatible {DS3} g) () rd_env ''G'' = SPos"
  by (rule read_reach_DS3)

theorem digest_separates_the_calls:
  "glob_env_cmp (\<lambda>_ g. rd_compatible {DS1} g) () rd_env ''G''
     \<noteq> glob_env_cmp (\<lambda>_ g. rd_compatible {DS3} g) () rd_env ''G''"
  by (simp add: first_call_reads_mode_zero second_call_reads_mode_pos)

text \<open>The same monovariant loss as Panel A, isolated to the read: joining all def-sites under one
  context gives back \<^const>\<open>SNonNeg\<close> --- exactly the precision the def-site keying recovers.\<close>

theorem context_keyed_would_merge:
  "glob_env_cmp (\<lambda>_ g. rd_compatible {DS1, DS3} g) () rd_env ''G'' = SNonNeg"
  by (rule read_join_all)

subsection \<open>Soundness\<close>

text \<open>
  The def-site-keyed read over-approximates the concrete reaching definitions at every program
  point: the generic collecting theorem \<open>reaching_def_collect_sound_bot_incl\<close> (theory
  \<open>Digest_Global_Read\<close>), instantiated for this concrete sign reader as \<open>rd_collect_sound_witness\<close>
  (theory \<open>Exec_Sign_RD_Keyed_Run\<close>).  The executable reads of Panel B are exactly the values that
  certified reader assigns the call and return points, so the analysis run here is the one whose
  soundness is proved.
\<close>

theorem showcase_reads_are_the_certified_reads:
  "glob_env_cmp (\<lambda>_ g. rd_compatible {DS1} g) () rd_env ''G'' = rd_obs rd_reach rd_sig (4, ()) ''G''
   \<and> glob_env_cmp (\<lambda>_ g. rd_compatible {DS3} g) () rd_env ''G'' = rd_obs rd_reach rd_sig (6, ()) ''G''"
  by (rule exec_read_agrees_with_sound_witness)

subsection \<open>What a single fully-integrated RD-annotated CFG would need\<close>

text \<open>
  Panel A and Panel B are, today, two different pipelines: Panel A renders a whole-program CFG
  but shares globals; Panel B computes digest precision but its reaching function \<open>rd_reach\<close> is
  supplied by hand for the witness's two points, \<^emph>\<open>not\<close> computed over the compiled CFG.  To fuse
  them --- one CFG whose every node label is that node's digest read --- the missing piece is an
  \<^emph>\<open>executable reaching-definition summary pass\<close>: a map \<open>(pp, ctx) \<mapsto> \<close> reaching set over the
  compiled CFG, feeding \<^const>\<open>rd_obs\<close> per node.  That is a tooling / UX layer on top of what is
  proved here; the read soundness (\<open>showcase_reads_are_the_certified_reads\<close>) does not depend on
  it.
\<close>

end
