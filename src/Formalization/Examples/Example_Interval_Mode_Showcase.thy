theory Example_Interval_Mode_Showcase
  imports "Voblint_Analysis.Exec_Ivl_Mode_Compiled_Run"
begin

section \<open>Interval value-carried digest showcase\<close>

text \<open>
  The interval counterpart of \<open>Example_Mode_Value_Digest_Showcase\<close>:
  a guided reading of the interval mode-digest run, wrapping
  \<^theory>\<open>Voblint_Analysis.Exec_Ivl_Mode_Compiled_Run\<close> for the umbrella document.  Everything is
  proved there; this theory only re-exposes the headline facts.

  The program \<^const>\<open>iv_prog\<close> runs a while loop and then calls a procedure under two contexts
  distinguished by an ordinary local, projected to a digest by \<^const>\<open>ivl_decode\<close>.  The same
  generic \<^locale>\<open>value_digest_reader\<close> kernel the sign flagship uses is instantiated here at the
  interval domain --- the second dissimilar instance, which is what makes the kernel's
  genericity a demonstrated fact.
\<close>

subsection \<open>The while loop is tracked as an interval range\<close>

text \<open>After \<open>i := 0; while (i < 5) { i := i + 1 }\<close> the analysis knows \<open>i = [5,5]\<close> at the exit.\<close>
lemmas showcase_loop = iv_loop_tracked

subsection \<open>The digest separates the global; the context-blind read merges it\<close>

text \<open>Digest-keyed: \<open>ILo\<close> keeps \<open>G = [0,5]\<close>, \<open>IHi\<close> keeps \<open>G = [9,9]\<close>; context-blind merges to \<open>[0,9]\<close>.\<close>
lemmas showcase_separation = iv_digest_separates_the_modes

subsection \<open>Sound under every update rule\<close>

text \<open>The run is a certified abstract post-solution under join, per-origin, and warrowing; the
  update-rule menu (\<^const>\<open>run_menu\<close>) reads the \<open>ILo\<close> partition under each.\<close>
lemmas showcase_update_rules = iv_digest_across_update_rules
lemmas showcase_widening_sound = wide_abstracts

subsection \<open>GraphViz\<close>

text \<open>\<^const>\<open>iv_digest_dot\<close> renders the context-clustered digest graph (one cluster per mode with
  its separated \<open>G\<close>); \<^const>\<open>wide_dot\<close> renders the annotated widening loop.  Both use the
  generic \<^class>\<open>show_val\<close> renderers.\<close>

ML_val \<open>writeln (@{code iv_digest_dot})\<close>

end
