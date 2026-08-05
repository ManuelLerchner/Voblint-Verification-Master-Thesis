theory Example_Ghost_LastWriter
  imports "Voblint_Core.Ghost_Last_Write_Domain"
begin

section \<open>Executable demonstration: last-writer tracking over a straight-line program\<close>

text \<open>
  The context-insensitive vertical slice from \<open>GHOST_DOMAIN_SEEDING_MIGRATION.md\<close> section 10,
  case 1: the CFG for \<^verbatim>\<open>g := 1; i := 0; g := 2\<close> is the one \<^const>\<open>compile_prog\<close> actually
  produces from the source program below, not a hand-built \<^typ>\<open>cfg\<close> value.  \<^const>\<open>calls\<close> is
  empty, so no \<open>routed_context\<close> integration is exercised here; that is the routed-context
  milestone's own payoff (case 2 of section 10), out of scope for this slice.

  Throughout, "the last writer of \<open>x\<close> is \<open>v\<close>" names \<open>v\<close> as the node \<^emph>\<open>reached by\<close> the write
  --- the target of the writing edge, matching \<^const>\<open>last_write_step\<close>,
  \<^const>\<open>ghost_step\<close>'s own \<open>v\<close> parameter, and \<open>ghost_step_sound_trace\<close>'s conclusion, not the
  edge's source.
\<close>

subsection \<open>The example source program and its compiled CFG\<close>

definition example_prog :: imp_prog where
  "example_prog = program {
     global g;
     void main() { g := 1; i := 0; g := 2 }
   }"

definition example_cfg :: cfg where
  "example_cfg =
     compile_prog (prog_table example_prog) (prog_procs example_prog)
       prog_main_name (prog_main example_prog)"

text \<open>Edge-action functionality holds for every compiled program, unconditionally --- this is
  \<open>compile_prog_intra_functional\<close>'s own scope; nothing here claims it for a hand-built
  \<^typ>\<open>cfg\<close>.\<close>
lemma example_cfg_functional: "cfg_intra_functional example_cfg"
  unfolding example_cfg_def by (rule compile_prog_intra_cfg_functional)

text \<open>The four statement nodes the compiler allocates for \<^verbatim>\<open>g := 1; i := 0; g := 2\<close>, in
  source order --- computed, not asserted; \<open>by eval\<close> runs the same compiler code
  \<^const>\<open>compile_prog\<close> executes anywhere else.\<close>

definition n0 :: cfg_node where "n0 = Statement 0"
definition n1 :: cfg_node where "n1 = Statement 1"
definition n2 :: cfg_node where "n2 = Statement 2"
definition n3 :: cfg_node where "n3 = Statement 3"

text \<open>The full compiled edge set, computed once so every downstream membership and
  non-membership fact is read off it directly instead of re-deriving edge shapes from
  \<^const>\<open>cfg_intra_functional\<close> alone (which only forces action agreement for a fixed
  source/target pair, not that a source has a single outgoing edge).  Besides the three
  assignments, \<^const>\<open>compile_proc\<close> adds the fixed entry wiring into \<open>n0\<close> and, since the body
  falls through, the fixed epilogue out of \<open>n3\<close>.\<close>
lemma example_cfg_intra_eval:
  "intra example_cfg =
     {(FunctionEntry ''main'', EA_Nop, n0),
      (n0, EA_Assign ''g'' (N 1), n1),
      (n1, EA_Assign ''i'' (N 0), n2),
      (n2, EA_Assign ''g'' (N 2), n3),
      (n3, EA_Ret None ''main'', FunctionResult ''main'')}"
  unfolding example_cfg_def n0_def n1_def n2_def n3_def by eval

lemma example_cfg_entry: "cfg_entry example_cfg = FunctionEntry ''main''"
  unfolding example_cfg_def by (simp add: inv16_entry_is_main prog_main_name_def)

text \<open>No action other than the entry wiring leaves \<^const>\<open>FunctionEntry\<close> \<open>''main''\<close>, and it
  does not write \<open>g\<close>.\<close>
lemma example_cfg_entry_out_no_write:
  assumes "(FunctionEntry ''main'', a, v) \<in> intra example_cfg"
  shows "\<not> edge_writes a ''g''"
  using assms unfolding example_cfg_intra_eval n0_def n1_def n2_def n3_def by auto

text \<open>No action other than the \<open>i\<close>-write leaves \<open>n1\<close>, read directly off the closed-form edge
  set --- what the "unrelated assignment preserves the writer" step below needs.\<close>
lemma example_cfg_n1_out_unique:
  assumes "(n1, a, v) \<in> intra example_cfg"
  shows "a = EA_Assign ''i'' (N 0) \<and> v = n2"
  using assms unfolding example_cfg_intra_eval n0_def n1_def n2_def n3_def by auto

subsection \<open>A concrete trace and its last-writer trajectory\<close>

definition s0 :: store where "s0 = (\<lambda>_. 0)"
definition s1 :: store where "s1 = s0(''g'' := 1)"
definition s2 :: store where "s2 = s1(''i'' := 0)"
definition s3 :: store where "s3 = s2(''g'' := 2)"

definition p_entry :: "(cfg_node \<times> store) list" where "p_entry = [(FunctionEntry ''main'', s0)]"
definition p0 :: "(cfg_node \<times> store) list" where "p0 = p_entry @ [(n0, s0)]"
definition p1 :: "(cfg_node \<times> store) list" where "p1 = p0 @ [(n1, s1)]"
definition p2 :: "(cfg_node \<times> store) list" where "p2 = p1 @ [(n2, s2)]"
definition p3 :: "(cfg_node \<times> store) list" where "p3 = p2 @ [(n3, s3)]"

text \<open>Before any write, the trace-level last writer of \<open>g\<close> is \<^const>\<open>None\<close> --- true already at
  the procedure entry, and preserved across the non-writing entry-wiring step into \<open>n0\<close>.\<close>
lemma last_writer_before_any_write: "last_writer example_cfg ''g'' p0 = None"
proof -
  have pene: "p_entry \<noteq> []" by (simp add: p_entry_def)
  have lastpe: "fst (last p_entry) = FunctionEntry ''main''" by (simp add: p_entry_def)
  have base: "last_writer example_cfg ''g'' p_entry = None" by (simp add: p_entry_def)
  have nw: "\<not> last_write_step example_cfg (FunctionEntry ''main'') n0 ''g''"
    unfolding last_write_step_def using example_cfg_entry_out_no_write by blast
  show ?thesis
    unfolding p0_def
    using last_writer_snoc_no_write[OF pene] lastpe nw base by simp
qed

text \<open>After the first write, the writer is precisely the node reached by that write.\<close>
lemma last_writer_after_first_write: "last_writer example_cfg ''g'' p1 = Some n1"
proof -
  have p0ne: "p0 \<noteq> []" by (simp add: p0_def p_entry_def)
  have lastp0: "fst (last p0) = n0" by (simp add: p0_def)
  have ws: "last_write_step example_cfg n0 n1 ''g''"
    unfolding last_write_step_def example_cfg_intra_eval by auto
  show ?thesis
    unfolding p1_def using last_writer_snoc_write[OF p0ne] lastp0 ws by simp
qed

text \<open>An unrelated assignment (to \<open>i\<close>) preserves the last writer of \<open>g\<close>.\<close>
lemma last_writer_unrelated_preserved: "last_writer example_cfg ''g'' p2 = Some n1"
proof -
  have p1ne: "p1 \<noteq> []" by (simp add: p1_def p0_def p_entry_def)
  have lastp1: "fst (last p1) = n1" by (simp add: p1_def)
  have nw: "\<not> last_write_step example_cfg n1 n2 ''g''"
  proof
    assume "last_write_step example_cfg n1 n2 ''g''"
    then obtain a where a: "(n1, a, n2) \<in> intra example_cfg" "edge_writes a ''g''"
      unfolding last_write_step_def by blast
    have "a = EA_Assign ''i'' (N 0)" using example_cfg_n1_out_unique[of a n2] a(1) by simp
    with a(2) show False by simp
  qed
  show ?thesis
    unfolding p2_def
    using last_writer_snoc_no_write[OF p1ne] lastp1 nw last_writer_after_first_write by simp
qed

text \<open>After the second write, the writer points to the second write's target node.\<close>
lemma last_writer_after_second_write: "last_writer example_cfg ''g'' p3 = Some n3"
proof -
  have p2ne: "p2 \<noteq> []" by (simp add: p2_def p1_def p0_def p_entry_def)
  have lastp2: "fst (last p2) = n2" by (simp add: p2_def)
  have ws: "last_write_step example_cfg n2 n3 ''g''"
    unfolding last_write_step_def example_cfg_intra_eval by auto
  show ?thesis
    unfolding p3_def using last_writer_snoc_write[OF p2ne] lastp2 ws by simp
qed

subsection \<open>The trace is a genuine \<^const>\<open>valid_ltr\<close> execution\<close>

text \<open>The characterization lemmas above compute \<^const>\<open>last_writer\<close> over \<open>p0\<close>/\<open>p1\<close>/\<open>p2\<close>/\<open>p3\<close>
  as bare lists.  This section closes the gap the milestone review flagged: those lists are
  exactly the \<^const>\<open>path\<close> of a trace the current collecting semantics actually admits, built
  by four concrete \<^const>\<open>valid_ltr\<close> steps from \<^const>\<open>cfg_entry\<close>, not merely plausible ones.\<close>

abbreviation example_gs :: "vname \<Rightarrow> bool" where
  "example_gs \<equiv> storage_global example_prog prog_main_name"

lemma t_entry_valid: "Root p_entry \<in> valid_ltr example_gs example_cfg {s0}"
  using valid_ltr.init[of s0 "{s0}" example_cfg example_gs]
  by (simp add: p_entry_def example_cfg_entry)

lemma t0_valid: "Root p0 \<in> valid_ltr example_gs example_cfg {s0}"
proof -
  have e: "(sink_node (Root p_entry), EA_Nop, n0) \<in> intra example_cfg"
    using example_cfg_intra_eval by (simp add: p_entry_def sink_node_def)
  have s': "s0 \<in> edge_step EA_Nop (sink_store (Root p_entry))"
    by (simp add: p_entry_def sink_store_def)
  have "CFG_Local_Trace.extend (Root p_entry) (n0, s0) \<in> valid_ltr example_gs example_cfg {s0}"
    by (rule valid_ltr.intra[OF t_entry_valid e s'])
  then show ?thesis by (simp add: p_entry_def p0_def)
qed

lemma t1_valid: "Root p1 \<in> valid_ltr example_gs example_cfg {s0}"
proof -
  have e: "(sink_node (Root p0), EA_Assign ''g'' (N 1), n1) \<in> intra example_cfg"
    using example_cfg_intra_eval by (simp add: p0_def sink_node_def)
  have s': "s1 \<in> edge_step (EA_Assign ''g'' (N 1)) (sink_store (Root p0))"
    by (simp add: p0_def sink_store_def s1_def)
  have "CFG_Local_Trace.extend (Root p0) (n1, s1) \<in> valid_ltr example_gs example_cfg {s0}"
    by (rule valid_ltr.intra[OF t0_valid e s'])
  then show ?thesis by (simp add: p0_def p1_def)
qed

lemma t2_valid: "Root p2 \<in> valid_ltr example_gs example_cfg {s0}"
proof -
  have e: "(sink_node (Root p1), EA_Assign ''i'' (N 0), n2) \<in> intra example_cfg"
    using example_cfg_intra_eval by (simp add: p1_def sink_node_def)
  have s': "s2 \<in> edge_step (EA_Assign ''i'' (N 0)) (sink_store (Root p1))"
    by (simp add: p1_def sink_store_def s2_def)
  have "CFG_Local_Trace.extend (Root p1) (n2, s2) \<in> valid_ltr example_gs example_cfg {s0}"
    by (rule valid_ltr.intra[OF t1_valid e s'])
  then show ?thesis by (simp add: p1_def p2_def)
qed

lemma t3_valid: "Root p3 \<in> valid_ltr example_gs example_cfg {s0}"
proof -
  have e: "(sink_node (Root p2), EA_Assign ''g'' (N 2), n3) \<in> intra example_cfg"
    using example_cfg_intra_eval by (simp add: p2_def sink_node_def)
  have s': "s3 \<in> edge_step (EA_Assign ''g'' (N 2)) (sink_store (Root p2))"
    by (simp add: p2_def sink_store_def s3_def)
  have "CFG_Local_Trace.extend (Root p2) (n3, s3) \<in> valid_ltr example_gs example_cfg {s0}"
    by (rule valid_ltr.intra[OF t2_valid e s'])
  then show ?thesis by (simp add: p2_def p3_def)
qed

text \<open>The trace-level specification, restated against the admitted trace itself rather than
  its bare \<^const>\<open>path\<close>.\<close>
lemma trace_last_writer_after_second_write:
  "trace_last_writer example_cfg ''g'' (Root p3) = Some n3"
  unfolding trace_last_writer_def by (simp add: last_writer_after_second_write)

lemmas example_trace_valid = t_entry_valid t0_valid t1_valid t2_valid t3_valid

subsection \<open>The incremental ghost computation agrees\<close>

text \<open>Seeding the ghost state at a reached point with no writes yet uses \<^term>\<open>FVal None\<close>, the
  genuine domain value for "no write, precisely" --- not \<^const>\<open>bot\<close> (see
  \<open>Ghost_Last_Write_Domain\<close>).\<close>

definition w0 :: ghost_lw where "w0 = (\<lambda>_. FVal None)"
definition w1 :: ghost_lw where "w1 = ghost_step (EA_Assign ''g'' (N 1)) n1 w0"
definition w2 :: ghost_lw where "w2 = ghost_step (EA_Assign ''i'' (N 0)) n2 w1"
definition w3 :: ghost_lw where "w3 = ghost_step (EA_Assign ''g'' (N 2)) n3 w2"

lemma w1_ghost: "w1 ''g'' = FVal (Some n1)"
  by (simp add: w1_def w0_def ghost_step_def)

lemma w2_ghost_preserved: "w2 ''g'' = FVal (Some n1)"
  by (simp add: w2_def w1_ghost ghost_step_def)

lemma w3_ghost: "w3 ''g'' = FVal (Some n3)"
  by (simp add: w3_def w2_ghost_preserved ghost_step_def)

text \<open>The incremental ghost trajectory computes exactly what the trace-level specification
  says at every step: \<open>w1\<close>/\<open>w2\<close>/\<open>w3\<close>'s \<open>''g''\<close> slot names precisely the same node as
  \<open>last_writer\<close> does at \<open>p1\<close>/\<open>p2\<close>/\<open>p3\<close>.\<close>
lemma ghost_matches_trace_spec:
  "w1 ''g'' = FVal (last_writer example_cfg ''g'' p1)"
  "w2 ''g'' = FVal (last_writer example_cfg ''g'' p2)"
  "w3 ''g'' = FVal (last_writer example_cfg ''g'' p3)"
  by (simp_all add: w1_ghost w2_ghost_preserved w3_ghost last_writer_after_first_write
      last_writer_unrelated_preserved last_writer_after_second_write)

text \<open>This slice imports \<open>Ghost_Last_Write_Domain\<close> only, not \<open>Ghost_Last_Write_Product\<close>: an
  "identity base transfer is trivially sound" claim is false for a real value domain in general
  (an unmodified abstract value need not still admit a changed concrete store; it holds only
  when the domain already claims nothing, e.g.\ a constant-\<open>\<top>\<close> two-point domain, or vacuously
  at \<open>\<bottom>\<close>).  Exercising \<open>product_step\<close> honestly needs a real per-edge sound base
  transfer --- \<open>sign\<close>'s own assignment transfer, say --- which is the concrete \<open>dg_spec\<close>
  milestone's job, not this one's.\<close>

subsection \<open>The carrier join for divergent writers loses precision\<close>

text \<open>Two branches whose last writer of \<open>g\<close> differ (here, \<open>n1\<close> and \<open>n3\<close>, the two write sites
  above) join to \<^const>\<open>FTop\<close> --- "conflicting or unknown writer" --- never to either single
  writer.  This is a fact about the flat-domain carrier's own \<open>\<squnion>\<close>, not a computed branch merge
  from a compiled CFG; a real branch merge belongs to the concrete \<open>dg_spec\<close>/solver milestone.\<close>
lemma ghost_join_loses_precision:
  "FVal (Some n1) \<squnion> FVal (Some n3) = (FTop :: cfg_node option flat_top)"
proof -
  have "n1 \<noteq> n3" by (simp add: n1_def n3_def)
  then show ?thesis by (simp add: sup_flat_top_def less_eq_flat_top_def)
qed

text \<open>A path that never wrote \<open>g\<close> joined with a path that did also loses precision, not
  "silently retains the write" --- the distinction \<open>Ghost_Last_Write_Domain\<close> keeps between
  \<^term>\<open>FVal None\<close> and \<^const>\<open>bot\<close> is what makes this the sound answer.\<close>
lemma ghost_join_no_write_vs_write:
  "FVal None \<squnion> FVal (Some n1) = (FTop :: cfg_node option flat_top)"
  by (simp add: sup_flat_top_def less_eq_flat_top_def)

text \<open>By contrast, joining an \<^emph>\<open>unreached\<close> branch (\<^const>\<open>bot\<close>, pure "no information") with
  either a no-write or a precise-write fact is absorbed --- the unreached side contributes
  nothing, distinguishing framework non-reachability from a genuine "no write" domain value.\<close>
lemma ghost_join_unreachable_no_write:
  "(bot :: cfg_node option flat_top) \<squnion> FVal None = FVal None"
  by (simp add: sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)

lemma ghost_join_unreachable_write:
  "(bot :: cfg_node option flat_top) \<squnion> FVal (Some n1) = FVal (Some n1)"
  by (simp add: sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)

end

