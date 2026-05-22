section \<open>Example: Intermediate-Point Safety on a Non-Terminating Program\<close>

text \<open>\label{sec:example-nonterminating-safe}\<close>

theory Example_NonTerminating_Safe
  imports Pipeline
begin

text \<open>
  A program that never terminates: \verb|x := 10; while True do skip|.

  Big-step soundness (\<open>pipeline_sound\<close>) carries the premise
  \<open>(c, s) \<Rightarrow> t\<close> (``execution reaches a final state'').  For this program
  no such \<open>t\<close> exists, so the conclusion is vacuously discharged --- we
  learn nothing about the analyzer's output at intermediate program points.

  The path-based variant \<open>pipeline_sound_path\<close>, added by the small-step
  migration (docs/SMALL\_STEP\_MIGRATION.md), drops the big-step premise.
  Its conclusion holds at every program point \<open>v\<close> reachable via a CFG
  path from the entry --- in particular at the program point right after
  \<open>''x'' ::= N 10\<close>, even though the program never returns from the
  trailing infinite loop.
\<close>


definition nonterm_prog :: com where
  "nonterm_prog \<equiv> (''x'' ::= N 10) ;; WHILE (Bc True) DO SKIP"


subsection \<open>Intermediate-point safety via the path-based theorem\<close>

text \<open>
  Despite the absence of a big-step result, soundness at every CFG-reachable
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
    "TD_plain.solve_domnonterm_prog
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

end
