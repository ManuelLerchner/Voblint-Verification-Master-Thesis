theory Example_Mode_Value_Digest_Showcase
  imports "Voblint_Analysis.Exec_Sign_Mode_Compiled_Run"
begin

section \<open>Value-carried digest showcase\<close>

text \<open>
  One compiled program, \<^emph>\<open>one\<close> solver run, analysed with a value-carried digest: the call
  context is a projection of the caller's abstract state, and the global is partitioned by that
  same projection.  This is the faithful transcription of Goblint's \<open>context : D.t \<rightarrow> C.t\<close> and
  its digest-keyed \<open>sideg\<close>.  Every claim below is \<open>by eval\<close> on the solver's own output, or
  \<open>by (rule \<dots>)\<close> onto a proven lemma --- nothing is hand-computed.

  The underlying run and its annotated-CFG renderer are proved in
  \<^theory>\<open>Voblint_Analysis.Exec_Sign_Mode_Compiled_Run\<close>; the read kernel and the bridge lemma in
  \<^theory>\<open>Voblint_Analysis.Value_Digest_Read\<close>.  This theory is the guided reading.  The interval
  counterpart --- same kernel, interval domain, with a while loop --- is the self-contained run
  \<open>Voblint_Analysis.Exec_Ivl_Mode_Compiled_Run\<close>.
\<close>

subsection \<open>The program\<close>

text \<open>
  \<open>mode\<close> is an \<^emph>\<open>ordinary local variable\<close> the analysis reads back as the digest --- no
  instrumentation: \<open>main\<close> reads it into the local computation (\<open>x := G + mode\<close>).  \<open>G\<close> is
  the one global.  \<open>main\<close> sets \<open>mode\<close> and \<open>G\<close>, calls \<open>f\<close> under each mode, and reads them back;
  \<open>f\<close> reads \<open>G\<close>.  The two calls happen at two different modes, so \<open>f\<close> is analysed \<^emph>\<open>twice\<close>,
  each activation seeing only its own global partition.

  @{term mode_prog}:
  \begin{verbatim}
    global G;
    void f()    { z := G }
    void main() { mode := 0; G := 0; f(); x := G + mode;
                  mode := 1; G := 1; f(); y := G + mode }
  \end{verbatim}
\<close>

value "prog_procs mode_prog"
value "prog_main mode_prog"

subsection \<open>Compiled control-flow graph\<close>

text \<open>
  The real pipeline compiles the program to @{term mode_cfg}.  \<open>f\<close> is compiled first, so its
  body is the low program points; \<open>main\<close> is the rest.  An \<^const>\<open>EA_Enter\<close> edge is a call, and
  each \<^emph>\<open>combine\<close> triple \<open>(call, exit, return)\<close> is the matching return.
\<close>

value "sorted_list_of_set (nodes mode_cfg)"
value "cfg_edges_list mode_cfg"
value "cfg_combines_list mode_cfg"

subsection \<open>Contexts from the local state\<close>

text \<open>
  The call context is not hand-chosen: @{const mode_ec} reads the caller's local \<open>''mode''\<close> and
  decodes it to a \<^typ>\<open>mode\<close> --- a \<^emph>\<open>function of the caller abstract state\<close>.  Only the finite
  enumeration of \<^typ>\<open>mode\<close> bounds how many activations appear.  Running the solver materialises
  both:
\<close>

lemma showcase_both_contexts_generated: "ctxs_at 0 = {MZero, MOne}"
  by (rule ctxs_at_0)

text \<open>
  Soundness point --- \<^emph>\<open>the mode rides the context, not the callee's locals\<close>.  On a call,
  \<^const>\<open>enter_state\<close> resets the callee's locals to \<open>0\<close>, so \<open>f\<close>'s own \<open>''mode''\<close> local is wiped
  on entry (visible below: \<open>f\<close>'s nodes carry \<open>mode = Bottom\<close>).  A callee cannot recover its
  digest by re-projecting its reset local slot; the mode travels through the context side
  channel.  This is Goblint's frame-locality of the digest.
\<close>

subsection \<open>Mode-keyed global writes\<close>

text \<open>
  The digest-keyed writer @{const side_cfg_T_eff_digest_st} keys each global write by the digest
  @{const mode_dg} of its \<^emph>\<open>write-point state\<close> --- Goblint's \<open>sideg (G, Digest.compute d)\<close>.  \<open>G :=
  0\<close> (taken at mode \<open>0\<close>) publishes to the finite key \<^term>\<open>Inr MZero\<close>, and \<open>G := 1\<close> (at mode
  \<open>1\<close>) to \<^term>\<open>Inr MOne\<close> --- two \<^emph>\<open>finite\<close> partition slots, never the whole \<^typ>\<open>sign st\<close>.
  The two writes stay apart:
\<close>

value "lookup_st (snd mode_digest_solution (Inr MZero)) ''G''"
value "lookup_st (snd mode_digest_solution (Inr MOne)) ''G''"

text \<open>The payoff, sealed by the solver: the modes keep \<open>G\<close> apart (\<^const>\<open>SZero\<close> vs \<^const>\<open>SPos\<close>)
  where a context-blind join collapses to \<^const>\<open>SNonNeg\<close>.\<close>
theorem showcase_writer_separates:
  "lookup_st (snd mode_digest_solution (Inr MZero)) ''G'' = SZero
   \<and> lookup_st (snd mode_digest_solution (Inr MOne)) ''G'' = SPos
   \<and> lookup_st (snd mode_digest_solution (Inr MZero)) ''G''
       < lookup_st (snd mode_digest_solution (Inr MZero) \<squnion> snd mode_digest_solution (Inr MOne)) ''G''"
  by (rule digest_separates_the_modes)

subsection \<open>Projection reads --- on the same run\<close>

text \<open>
  The solved environment as a plain-function abstract state, feeding the projection reader
  @{const mode_obs}.  This is the \<^emph>\<open>same\<close> \<^const>\<open>mode_digest_solution\<close> whose writes just
  separated --- one run, reads and writes.
\<close>
definition mode_digest_env :: "(nat \<times> mode) + mode \<Rightarrow> sign abs_state" where
  "mode_digest_env = (\<lambda>k. fun_of_st (snd mode_digest_solution k))"

text \<open>
  \<open>main\<close> runs under one activation, \<^term>\<open>MZero\<close>.  At its two read points --- \<open>x := G + mode\<close> on the edge
  out of \<open>pp7\<close> (there \<open>mode = 0\<close>) and \<open>y := G + mode\<close> on the edge out of \<open>pp14\<close> (there \<open>mode = 1\<close>) ---
  @{const mode_obs} decodes the \<^emph>\<open>flow-sensitive\<close> local and reads exactly that partition:
  \<^const>\<open>SZero\<close> for the first read, \<^const>\<open>SPos\<close> for the second, on the real compiled run.
\<close>

lemma showcase_read_at_x: "mode_obs mode_digest_env (7, MZero) ''G'' = SZero"
  unfolding mode_obs_reduce mode_digest_env_def mode_digest_unfold by eval

lemma showcase_read_at_y: "mode_obs mode_digest_env (14, MZero) ''G'' = SPos"
  unfolding mode_obs_reduce mode_digest_env_def mode_digest_unfold by eval

text \<open>The monovariant loss, isolated to the read: joining all modes merges \<open>G\<close> back to
  \<^const>\<open>SNonNeg\<close> --- the precision the mode keying recovers.\<close>
lemma showcase_read_blind: "glob_env_cmp (\<lambda>_ _. True) MZero mode_digest_env ''G'' = SNonNeg"
  unfolding mode_digest_env_def mode_digest_unfold by eval

theorem showcase_reads_point_sensitive:
  "mode_obs mode_digest_env (7, MZero) ''G'' = SZero
   \<and> mode_obs mode_digest_env (14, MZero) ''G'' = SPos
   \<and> mode_obs mode_digest_env (7, MZero) ''G'' < glob_env_cmp (\<lambda>_ _. True) MZero mode_digest_env ''G''"
proof -
  have "SZero < SNonNeg" by eval
  thus ?thesis using showcase_read_at_x showcase_read_at_y showcase_read_blind by simp
qed

subsection \<open>Certified executable result\<close>

text \<open>
  The proven bridge @{thm[source] mode_obs_eq_side_env_cmp} identifies the projection read with
  the certified context read @{const side_env_cmp} \<^emph>\<open>exactly where the projected \<open>''mode''\<close> aligns
  with the activation context\<close>.  At \<open>pp7\<close> \<open>''mode''\<close> is still \<^term>\<open>MZero\<close>, so alignment holds on the run:
\<close>

lemma showcase_align_at_x: "mode_decode (mode_digest_env (Inl (7, MZero)) ''mode'') = MZero"
  unfolding mode_digest_env_def mode_digest_unfold mode_decode_def by eval

theorem showcase_read_is_certified_at_x:
  "mode_obs mode_digest_env (7, MZero) = side_env_cmp (=) mode_digest_env (7, MZero)"
  using showcase_align_at_x by (rule mode_obs_eq_side_env_cmp)

text \<open>
  Where \<open>''mode''\<close> has moved on inside the same activation --- \<open>pp14\<close>, \<open>mode = 1\<close> still under
  \<open>main @ MZero\<close> --- alignment \<^emph>\<open>fails\<close>, and the projection read is strictly more precise than the
  fixed context: it reads \<^const>\<open>SPos\<close> (the correct value written into \<open>y\<close>) where the context
  \<^term>\<open>MZero\<close> would select the wrong slot.  That extra precision is exactly the digest's value.
\<close>

lemma showcase_misalign_at_y: "mode_decode (mode_digest_env (Inl (14, MZero)) ''mode'') = MOne"
  unfolding mode_digest_env_def mode_digest_unfold mode_decode_def by eval

text \<open>
  So the certificate has two halves.  The bridge (above) certifies the reader \<^emph>\<open>shape\<close> against
  the context-read soundness theorem on the aligned points.  The digest \<^emph>\<open>writer\<close> is separately
  transported to its abstract image (\<open>part_post_solution_digest_st_to_abs_eff\<close>) and its solver
  invariants discharged on this run (\<open>mode_INR_BOT\<close>, \<open>mode_LOCAL_POST\<close>).  What is \<^emph>\<open>not\<close> closed
  is a read \<^emph>\<open>boundary\<close>, and it is settled the honest way --- by a machine-checked
  counterexample: the kernel's \<open>MODE_AGREE\<close> (the \<open>''mode''\<close> read at a callee exit under the routed
  context equals the read at the return) is \<^bold>\<open>false\<close> here.  A callee's \<open>''mode''\<close> local is reset on entry,
  so at a callee interior it decodes \<^term>\<open>MZero\<close> while the mode-1 return decodes \<^term>\<open>MOne\<close>.
  The value-derived read is therefore precise in the frame that \<^emph>\<open>sets\<close> the mode and rides the
  context elsewhere --- Goblint's frame-locality.  The read kernel is instantiated, never
  modified.  See \<open>docs/VALUE_CARRIED_DIGEST_STATUS.md\<close> and \<open>docs/DIGEST_TWO_FAMILIES.md\<close>.
\<close>

subsection \<open>Annotated CFG\<close>

text \<open>
  The solved digest run rendered with \<^emph>\<open>three\<close> activation clusters --- \<open>main\<close> once, \<open>f @ MZero\<close>,
  \<open>f @ MOne\<close>.  Each node is labelled with its solved locals; each \<open>f\<close> cluster with its visible
  global partition, and \<open>main\<close> with both slots \<open>G@MZero\<close> / \<open>G@MOne\<close>.  The two calls are routed by
  the digest \<^emph>\<open>computed from the solution\<close> (@{const call_ctx}): the mode-\<open>0\<close> call enters \<open>f @
  MZero\<close>, the mode-\<open>1\<close> call enters \<open>f @ MOne\<close>, both returning into \<open>main\<close>.  The source is
  branch-free, so control flow is a single path with the two \<open>f\<close> excursions.
\<close>

ML_val \<open>writeln (@{code mode_digest_dot_lit})\<close>

subsection \<open>What this demonstrates\<close>

text \<open>
  \<^item> \<^bold>\<open>One executable analysis\<close> computes the abstract state --- the vendored side-effecting
    solver on the compiled CFG, no hand-written result and no second equation system.
  \<^item> \<^bold>\<open>The digest is a projection\<close> of that state (@{const mode_dg} of the local \<open>''mode''\<close>),
    generated automatically as the call context.
  \<^item> \<^bold>\<open>Globals are partitioned by the digest\<close> (\<^term>\<open>Inr MZero\<close>, \<^term>\<open>Inr MOne\<close>), keyed at each
    write by the write-point state --- Goblint's \<open>sideg\<close> with a digest.
  \<^item> \<^bold>\<open>\<open>f\<close> is analysed in two contexts\<close> (@{thm[source] ctxs_at_0}); the callee's read rides the
    context, its reset locals notwithstanding.
  \<^item> \<^bold>\<open>The projection read is more precise than the activation context\<close> and equals the certified
    context read exactly where \<open>''mode''\<close> aligns (@{thm[source] showcase_read_is_certified_at_x}).
    The digest writer is transported and its invariants discharged; the residual read boundary
    at callee interiors (\<open>MODE_AGREE\<close>) is machine-checked \<^emph>\<open>false\<close> --- frame-locality, not a
    gap.  The read kernel (\<open>digest_global_read\<close>) is instantiated, never modified.
\<close>

subsection \<open>Further reading\<close>

text \<open>
  \<^item> \<^theory>\<open>Voblint_Analysis.Value_Digest_Read\<close> --- the read kernel (the \<open>digest_global_read\<close>
    instance), the reduction \<open>mode_obs_reduce\<close>, and the certified bridge
    \<open>mode_obs_eq_side_env_cmp\<close>.
  \<^item> \<^theory>\<open>Voblint_Analysis.Exec_Sign_Mode_Compiled_Run\<close> --- the compiled run behind this
    showcase: the digest writer's transport, the discharged solver invariants, and the
    \<open>MODE_AGREE\<close> counterexample.
  \<^item> \<open>docs/DIGEST_TWO_FAMILIES.md\<close> --- this value-derived digest beside the
    externally-computed reaching-definition digest, and the frame-locality boundary that
    separates them.
\<close>

end
