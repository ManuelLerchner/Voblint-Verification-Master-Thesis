section \<open>Example: Intermediate-Point Safety on a Non-Terminating Program\<close>

text \<open>\label{sec:example-nonterminating-safe}\<close>

theory Example_NonTerminating_Safe
  imports Pipeline
begin

text \<open>
  A program that never terminates: \verb|x := 10; while True do skip|.

  Exit soundness (\<open>pipeline_sound_runs_to\<close>) carries the premise
  \<open>runs_to c s t\<close>.  For this program no such \<open>t\<close> exists, so the
  conclusion is vacuously discharged --- we learn nothing about the
  analyzer's output at intermediate program points.

  The path-based variant \<open>pipeline_sound_path\<close>, added by the small-step
  migration (docs/SMALL\_STEP\_MIGRATION.md), drops the big-step premise.
  Its conclusion holds at every program point \<open>v\<close> reachable via a CFG
  path from the entry --- in particular at the program point right after
  \<open>''x'' ::= N 10\<close>, even though the program never returns from the
  trailing infinite loop.
\<close>


definition nonterm_prog :: com where
  "nonterm_prog \<equiv> (''x'' ::= N 10) ;; WHILE (Bc True) DO SKIP"


subsection \<open>The program does not terminate\<close>

text \<open>
  \<open>WHILE (Bc True) DO SKIP\<close> never reaches \<open>SKIP\<close> in small-step.
  (Proof via star inversion; full script in Phase 6.)
\<close>

lemma while_true_skip_no_finish:
  "\<not> ((WHILE (Bc True) DO SKIP, s) \<rightarrow>* (SKIP, t))"
  by (fact IMP2_SmallStep.while_true_skip_no_finish)


lemma nonterm_prog_no_runs_to:
  "\<not> (\<exists>t. runs_to nonterm_prog s t)"
proof clarify
  fix t assume "runs_to nonterm_prog s t"
  then have "(nonterm_prog, s) \<rightarrow>* (SKIP, t)"
    by (rule runs_to_small_step)
  then have star: "((''x'' ::= N 10) ;; WHILE (Bc True) DO SKIP, s) \<rightarrow>* (SKIP, t)"
    by (simp add: nonterm_prog_def)
  from seq_star_finish[OF star] obtain s2 where
        "(''x'' ::= N 10, s) \<rightarrow>* (SKIP, s2)"
    and w: "(WHILE (Bc True) DO SKIP, s2) \<rightarrow>* (SKIP, t)"
    by blast
  from w while_true_skip_no_finish show False by simp
qed


subsection \<open>Intermediate-point safety via the path-based theorem\<close>

text \<open>
  Despite the absence of a terminating run, soundness at every CFG-reachable
  program point is expressible and provable: it follows directly from
  \<open>pipeline_sound_path\<close> by instantiation at \<^const>\<open>nonterm_prog\<close>.
  The proof carries no big-step assumption.
\<close>

theorem nonterm_safe_at_every_pp:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes cfi:        "comp_fun_idem (ac_join cfg)"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree (to_cfg nonterm_prog) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (cfg_entry (to_cfg nonterm_prog))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach
       (make_rhs_tree (to_cfg nonterm_prog) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (TD_plain_Interp_solve
          (make_rhs_tree (to_cfg nonterm_prog) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
          (cfg_entry (to_cfg nonterm_prog)))
       (cfg_entry (to_cfg nonterm_prog))"
  assumes path:     "cfg_path (to_cfg nonterm_prog)
                              (cfg_entry (to_cfg nonterm_prog)) es v"
  assumes t_in:     "t \<in> edges_collect es {s}"
  shows "t \<in> sound_domain.gamma_state (ac_gamma cfg) (run_analysis cfg nonterm_prog v)"
  by (rule pipeline_sound_path[OF sound join_eq bot_eq tf_sound s_in_gamma
            cfi td_solve_dom td_cfg_in_reach path t_in])


section \<open>Example: Diverging Program With Mutating State\<close>

text \<open>\label{sec:example-incr-loop-safe}\<close>

text \<open>
  The previous example assigns \<open>x\<close> exactly once, then enters an idle
  infinite loop.  Per-pp safety at the post-assignment program point is
  trivially "\<open>x\<close> equals 10" --- the diverging tail never touches \<open>x\<close>,
  so even a soundness theorem that ignored divergence entirely could
  pin down \<open>x\<close>'s value there.

  This second example exercises \<open>pipeline_sound_path\<close> in a regime where
  exit-only \<open>pipeline_sound_runs_to\<close> genuinely has nothing to say:
  the program mutates state inside a diverging loop, so the concrete
  reachable set at the loop's body-entry program point is
  \<open>{ s(''x'' := k) | k \<ge> 0 }\<close> --- countably infinite.  A sound abstract
  state at that program point must overapproximate all of those values
  simultaneously.  The exit-only soundness corollary is vacuous (no
  \<open>runs_to c s t\<close>), yet the path-based theorem still constrains
  the analyzer's output at every intermediate program point.

  Concretely: the program is \<open>x := 0 ;; WHILE True DO x := x + 1\<close>.
  Under an interval-domain instance, a correct analyzer would converge
  (via [[widening]]) on \<open>x \<in> [0, +\<infinity>)\<close> at the loop head and
  \<open>x \<in> [1, +\<infinity>)\<close> at the post-increment program point.  We do not
  specialise to intervals here --- the safety theorem stays
  domain-parametric so it can be reused for sign / parity / octagon
  instantiations.
\<close>


definition incr_loop_prog :: com where
  "incr_loop_prog \<equiv> (''x'' ::= N 0) ;;
                    WHILE (Bc True) DO (''x'' ::= Plus (V ''x'') (N 1))"


subsection \<open>The program does not terminate\<close>

text \<open>
  Same divergence pattern as \<open>while_true_skip_diverges\<close>, but the body
  is \<open>''x'' ::= Plus (V ''x'') (N 1)\<close> rather than \<open>SKIP\<close>.  The body
  terminates each iteration (it is a single assignment), so the
  \<open>WhileTrue\<close> case still produces a recursive big-step derivation on
  the same  WHILE command --- just at a different state
  (\<open>s' = s(''x'' := s ''x'' + 1)\<close>).  Because the induction generalises
  over \<open>s\<close>, the induction hypothesis applies directly to that recursive
  call and closes the case.

  Structure: induct with the command pattern pinned and \<open>s\<close>, \<open>t\<close>
  schematic.  Two cases survive after \<open>com.distinct\<close> rules out the
  others:
  \<^item> \<open>WhileFalse\<close>: contradicts \<open>bval (Bc True) s = True\<close>;
  \<^item> \<open>WhileTrue\<close>: the assignment body always reduces, then the
    induction hypothesis on the recursive WHILE derivation
    yields \<open>False\<close>.
\<close>

lemma while_true_incr_no_finish:
  "\<not> ((WHILE (Bc True) DO (''x'' ::= Plus (V ''x'') (N 1)), s) \<rightarrow>* (SKIP, t))"
  by (fact IMP2_SmallStep.while_true_incr_no_finish)

lemma incr_loop_no_runs_to:
  "\<not> (\<exists>t. runs_to incr_loop_prog s t)"
proof clarify
  fix t assume "runs_to incr_loop_prog s t"
  then have "(incr_loop_prog, s) \<rightarrow>* (SKIP, t)"
    by (rule runs_to_small_step)
  then have star: "((''x'' ::= N 0) ;; WHILE (Bc True) DO (''x'' ::= Plus (V ''x'') (N 1)), s) \<rightarrow>* (SKIP, t)"
    by (simp add: incr_loop_prog_def)
  from seq_star_finish[OF star] obtain s2 where
        "(''x'' ::= N 0, s) \<rightarrow>* (SKIP, s2)"
    and w: "(WHILE (Bc True) DO (''x'' ::= Plus (V ''x'') (N 1)), s2) \<rightarrow>* (SKIP, t)"
    by blast
  from w while_true_incr_no_finish show False by simp
qed


subsection \<open>Intermediate-point safety via the path-based theorem\<close>

text \<open>
  Identical instantiation pattern to \<open>nonterm_safe_at_every_pp\<close>: the
  conclusion is exactly \<open>pipeline_sound_path\<close> applied to
  \<^const>\<open>incr_loop_prog\<close>.  No new domain-side reasoning is needed ---
  the entire payoff comes from \<open>pipeline_sound_path\<close>'s missing
  termination premise.

  Reading the conclusion: pick any abstract domain \<open>cfg\<close> with a sound
  TF and a TD solver that terminates on this program's RHS tree.  Pick
  any concrete state \<open>s \<in> \<gamma>(init)\<close>, any CFG path \<open>es\<close> from entry to
  some program point \<open>v\<close>, and any concrete state \<open>t\<close> reachable from
  \<open>s\<close> along \<open>es\<close>.  Then \<open>t\<close> is in the concretisation of the analyser's
  abstract state at \<open>v\<close>.

  For \<^const>\<open>incr_loop_prog\<close> this is genuinely interesting at \<open>v\<close> =
  the program point inside the loop body (after the increment): the
  set of concrete \<open>t\<close> reachable there is \<open>{ s(''x'' := k) | k \<ge> 1 }\<close>,
  unbounded.  The theorem says any correct abstract state at that
  program point must overapproximate all of them.
\<close>

theorem incr_loop_safe_at_every_pp:
  fixes cfg :: "'a::bounded_semilattice_sup_bot analysis_config"
  assumes sound:      "sound_domain (ac_gamma cfg)"
  assumes join_eq:    "ac_join cfg = (\<lambda>s1 s2. \<lambda>x. s1 x \<squnion> s2 x)"
  assumes bot_eq:     "ac_bot cfg = (\<lambda>_. bot)"
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s \<in> sound_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes cfi:        "comp_fun_idem (ac_join cfg)"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree (to_cfg incr_loop_prog) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (cfg_entry (to_cfg incr_loop_prog))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach
       (make_rhs_tree (to_cfg incr_loop_prog) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
       (TD_plain_Interp_solve
          (make_rhs_tree (to_cfg incr_loop_prog) (ac_tf cfg) (ac_join cfg) (ac_bot cfg) (ac_init cfg))
          (cfg_entry (to_cfg incr_loop_prog)))
       (cfg_entry (to_cfg incr_loop_prog))"
  assumes path:     "cfg_path (to_cfg incr_loop_prog)
                              (cfg_entry (to_cfg incr_loop_prog)) es v"
  assumes t_in:     "t \<in> edges_collect es {s}"
  shows "t \<in> sound_domain.gamma_state (ac_gamma cfg) (run_analysis cfg incr_loop_prog v)"
  by (rule pipeline_sound_path[OF sound join_eq bot_eq tf_sound s_in_gamma
            cfi td_solve_dom td_cfg_in_reach path t_in])


text \<open>
  Note: this theorem says nothing concrete about \<^emph>\<open>which\<close> abstract
  value the analyser computes --- that depends on the chosen domain
  and its [[widening]] strategy.  A follow-up example specialised to
  the interval domain (once interval-side [[widening]] termination is
  available) would replace the parametric \<open>cfg\<close> with a concrete
  \<open>interval_analysis_config\<close> and conclude e.g.\\
  \<open>run_analysis interval_cfg incr_loop_prog (post_incr_pp) ''x'' = [1, +\<infinity>)\<close>.
  That is a precision claim, not a soundness one, and lives downstream
  of the interval-domain track.
\<close>

end
