theory Analysis_Certified
  imports Analysis_Run_Solver_Sound
begin

section \<open>One soundness statement over every configuration the CLI answers\<close>

text \<open>
  The endpoints so far are one per configuration: a domain, a solver discipline
  and a context policy, each with its own theorem. This theory states the result
  once, for an arbitrary configuration, and derives all of them from
  \<^const>\<open>run_voblint\<close> alone.

  Three functions carry the case split that the statement therefore does not.
  \<open>certified_preconditions\<close> names the two per-program facts the chosen
  configuration needs --- its solver run completed, and it solved enough keys ---
  and \<open>analysis_result_covers\<close> says that the table that configuration
  built describes a store at a node, at some context when the policy keeps
  contexts. Both are ordinary recursive definitions over the domain, the solver
  and the policy, for the reason \<^const>\<open>analyse_state_covers\<close> already is: an
  abstract state's type is the domain's own carrier, so nothing polymorphic can
  hold all five. \<open>checks_sound_at\<close> is the check column's claim, which
  needs no such split.

  Configuration legality is not a premise. An unsupported pairing answers
  \<^const>\<open>Unsupported_Configuration\<close>, so \<open>Analysed out\<close> already says the
  resolver accepted it, and the resolver's accepted set and the certified set
  coincide: every pairing it resolves to a plan carries this theorem. Neither is
  well-formedness a premise, for the same reason --- a malformed program answers
  \<^const>\<open>Malformed_Program\<close>.
\<close>

subsection \<open>What the chosen configuration owes, and what its table claims\<close>

text \<open>
  One equation per domain and policy, each reading the solver off its own
  argument. The wildcard branch is the discipline that policy defaults to, so it
  answers for \<^const>\<open>None\<close> and for that discipline named explicitly --- the two
  spellings the resolver sends to one plan. A branch reading \<open>False\<close> is a pairing
  the resolver rejects.
\<close>

fun certified_preconditions ::
    "analysis_domain \<Rightarrow> solver_choice option \<Rightarrow> context_mode
       \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "certified_preconditions Sign_Analysis solver Ctx_None p =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow>
          sign_po_terminates (declared_global p) p
          \<and> vars_cover (prog_cfg p) (sign_po_vars (declared_global p) p)
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow> analyse_certified Sign_Analysis p)"
| "certified_preconditions Sign_Analysis solver Ctx_EntryState p =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          sign_entry_state_terminates_for (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (sign_es.ctx_succ (declared_global p) p) []
            (sign_entry_state_vars (declared_global p) p))"
| "certified_preconditions Sign_Analysis solver (Ctx_CallString k) p =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          sign_cs_terminates k (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (sign_cs_ctx_succ k (declared_global p) p) []
            (sign_cs_vars k (declared_global p) p))"
| "certified_preconditions Interval_Analysis solver Ctx_None p =
     (case solver of
        Some Solver_Join \<Rightarrow>
          interval_join_terminates (declared_global p) p
          \<and> vars_cover (prog_cfg p) (interval_join_vars (declared_global p) p)
      | Some Solver_PerOrigin \<Rightarrow>
          interval_po_terminates (declared_global p) p
          \<and> vars_cover (prog_cfg p) (interval_po_vars (declared_global p) p)
      | Some Solver_WarrowPerOrigin \<Rightarrow>
          interval_wpo_terminates (declared_global p) p
          \<and> vars_cover (prog_cfg p) (interval_wpo_vars (declared_global p) p)
      | _ \<Rightarrow> analyse_certified Interval_Analysis p)"
| "certified_preconditions Interval_Analysis solver Ctx_EntryState p =
     (case solver of
        Some Solver_Join \<Rightarrow>
          interval_es_join.terminates (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p)
            (interval_es_join.ctx_succ (declared_global p) p) []
            (interval_es_join.sol_vars (declared_global p) p)
      | Some Solver_PerOrigin \<Rightarrow>
          interval_es_po.terminates (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p)
            (interval_es_po.ctx_succ (declared_global p) p) []
            (interval_es_po.sol_vars (declared_global p) p)
      | Some Solver_WarrowPerOrigin \<Rightarrow>
          interval_es_wpo.terminates (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p)
            (interval_es_wpo.ctx_succ (declared_global p) p) []
            (interval_es_wpo.sol_vars (declared_global p) p)
      | _ \<Rightarrow>
          entry_state_terminates_prog (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (interval_es.ctx_succ (declared_global p) p) []
            (entry_state_vars_prog (declared_global p) p))"
| "certified_preconditions Interval_Analysis solver (Ctx_CallString k) p =
     (case solver of
        Some Solver_Join \<Rightarrow>
          interval_cs_join_terminates k (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (interval_cs_join_ctx_succ k (declared_global p) p) []
            (interval_cs_join_vars k (declared_global p) p)
      | Some Solver_PerOrigin \<Rightarrow>
          interval_cs_po_terminates k (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (interval_cs_po_ctx_succ k (declared_global p) p) []
            (interval_cs_po_vars k (declared_global p) p)
      | Some Solver_WarrowPerOrigin \<Rightarrow>
          interval_cs_wpo_terminates k (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (interval_cs_wpo_ctx_succ k (declared_global p) p) []
            (interval_cs_wpo_vars k (declared_global p) p)
      | _ \<Rightarrow>
          interval_cs_terminates k (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (interval_cs_ctx_succ k (declared_global p) p) []
            (interval_cs_vars k (declared_global p) p))"
| "certified_preconditions Int_Analysis solver Ctx_None p =
     (case solver of
        Some Solver_Join \<Rightarrow>
          int_join_terminates (declared_global p) p
          \<and> vars_cover (prog_cfg p) (int_join_vars (declared_global p) p)
      | Some Solver_PerOrigin \<Rightarrow>
          int_po_terminates (declared_global p) p
          \<and> vars_cover (prog_cfg p) (int_po_vars (declared_global p) p)
      | Some Solver_WarrowPerOrigin \<Rightarrow>
          int_wpo_terminates (declared_global p) p
          \<and> vars_cover (prog_cfg p) (int_wpo_vars (declared_global p) p)
      | _ \<Rightarrow> analyse_certified Int_Analysis p)"
| "certified_preconditions Int_Analysis solver Ctx_EntryState p =
     (case solver of
        Some Solver_Join \<Rightarrow>
          int_es_join_terminates (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (int_es_join_ctx_succ (declared_global p) p) []
            (int_es_join_vars (declared_global p) p)
      | Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          int_es_terminates (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (int_es_ctx_succ (declared_global p) p) []
            (int_es_vars (declared_global p) p))"
| "certified_preconditions Int_Analysis solver (Ctx_CallString k) p =
     (case solver of
        Some Solver_Join \<Rightarrow>
          int_cs_join_terminates k (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (int_cs_join_ctx_succ k (declared_global p) p) []
            (int_cs_join_vars k (declared_global p) p)
      | Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          int_cs_terminates k (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (int_cs_ctx_succ k (declared_global p) p) []
            (int_cs_vars k (declared_global p) p))"
| "certified_preconditions Parity_Analysis solver Ctx_None p =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow>
          parity_po_terminates (declared_global p) p
          \<and> vars_cover (prog_cfg p) (parity_po_vars (declared_global p) p)
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow> analyse_certified Parity_Analysis p)"
| "certified_preconditions Parity_Analysis solver Ctx_EntryState p =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          parity_entry_state_terminates_for (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (parity_es.ctx_succ (declared_global p) p) []
            (parity_entry_state_vars (declared_global p) p))"
| "certified_preconditions Parity_Analysis solver (Ctx_CallString k) p =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          parity_cs_terminates k (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (parity_cs_ctx_succ k (declared_global p) p) []
            (parity_cs_vars k (declared_global p) p))"
| "certified_preconditions Congruence_Analysis solver Ctx_None p =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow>
          congruence_po_terminates (declared_global p) p
          \<and> vars_cover (prog_cfg p) (congruence_po_vars (declared_global p) p)
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow> analyse_certified Congruence_Analysis p)"
| "certified_preconditions Congruence_Analysis solver Ctx_EntryState p =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          congruence_entry_state_terminates_for (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (congruence_es.ctx_succ (declared_global p) p) []
            (congruence_entry_state_vars (declared_global p) p))"
| "certified_preconditions Congruence_Analysis solver (Ctx_CallString k) p =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          congruence_cs_terminates k (declared_global p) p
          \<and> ctx_vars_cover (prog_cfg p) (congruence_cs_ctx_succ k (declared_global p) p) []
            (congruence_cs_vars k (declared_global p) p))"

fun analysis_result_covers ::
    "analysis_domain \<Rightarrow> solver_choice option \<Rightarrow> context_mode
       \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" where
  "analysis_result_covers Sign_Analysis solver Ctx_None p v s =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow>
          (s \<in> \<lbrakk>case lookup_context (analyse_sign_result_per_origin p) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow> analyse_state_covers Sign_Analysis p v s)"
| "analysis_result_covers Sign_Analysis solver Ctx_EntryState p v s =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_sign_entry_state_result p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>))"
| "analysis_result_covers Sign_Analysis solver (Ctx_CallString k) p v s =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_sign_call_string_result k p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>))"
| "analysis_result_covers Interval_Analysis solver Ctx_None p v s =
     (case solver of
        Some Solver_Join \<Rightarrow>
          (s \<in> \<lbrakk>case lookup_context (analyse_interval_result_join p) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)
      | Some Solver_PerOrigin \<Rightarrow>
          (s \<in> \<lbrakk>case lookup_context (analyse_interval_result_per_origin p) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)
      | Some Solver_WarrowPerOrigin \<Rightarrow>
          (s \<in> \<lbrakk>case lookup_context (analyse_interval_result_wpo p) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)
      | _ \<Rightarrow> analyse_state_covers Interval_Analysis p v s)"
| "analysis_result_covers Interval_Analysis solver Ctx_EntryState p v s =
     (case solver of
        Some Solver_Join \<Rightarrow>
          (\<exists>c st. lookup_context (interval_es_join.result (declared_global p) p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>)
      | Some Solver_PerOrigin \<Rightarrow>
          (\<exists>c st. lookup_context (interval_es_po.result (declared_global p) p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>)
      | Some Solver_WarrowPerOrigin \<Rightarrow>
          (\<exists>c st. lookup_context (interval_es_wpo.result (declared_global p) p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>)
      | _ \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_interval_entry_state_result p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>))"
| "analysis_result_covers Interval_Analysis solver (Ctx_CallString k) p v s =
     (case solver of
        Some Solver_Join \<Rightarrow>
          (\<exists>c st. lookup_context (interval_cs_join_result k (declared_global p) p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>)
      | Some Solver_PerOrigin \<Rightarrow>
          (\<exists>c st. lookup_context (interval_cs_po_result k (declared_global p) p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>)
      | Some Solver_WarrowPerOrigin \<Rightarrow>
          (\<exists>c st. lookup_context (interval_cs_wpo_result k (declared_global p) p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>)
      | _ \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_interval_call_string_result k p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>))"
| "analysis_result_covers Int_Analysis solver Ctx_None p v s =
     (case solver of
        Some Solver_Join \<Rightarrow>
          (s \<in> \<lbrakk>case lookup_context (analyse_int_join_result p) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)
      | Some Solver_PerOrigin \<Rightarrow>
          (s \<in> \<lbrakk>case lookup_context (analyse_int_per_origin_result p) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)
      | Some Solver_WarrowPerOrigin \<Rightarrow>
          (s \<in> \<lbrakk>case lookup_context (analyse_int_wpo_result p) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)
      | _ \<Rightarrow> analyse_state_covers Int_Analysis p v s)"
| "analysis_result_covers Int_Analysis solver Ctx_EntryState p v s =
     (case solver of
        Some Solver_Join \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_int_entry_state_result p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>)
      | Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_int_entry_state_result_warrow p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>))"
| "analysis_result_covers Int_Analysis solver (Ctx_CallString k) p v s =
     (case solver of
        Some Solver_Join \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_int_call_string_result k p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>)
      | Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_int_call_string_result_warrow k p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>))"
| "analysis_result_covers Parity_Analysis solver Ctx_None p v s =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow>
          (s \<in> \<lbrakk>case lookup_context (analyse_parity_result_per_origin p) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow> analyse_state_covers Parity_Analysis p v s)"
| "analysis_result_covers Parity_Analysis solver Ctx_EntryState p v s =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_parity_entry_state_result p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>))"
| "analysis_result_covers Parity_Analysis solver (Ctx_CallString k) p v s =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_parity_call_string_result k p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>))"
| "analysis_result_covers Congruence_Analysis solver Ctx_None p v s =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow>
          (s \<in> \<lbrakk>case lookup_context (analyse_congruence_result_per_origin p) v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>)
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow> analyse_state_covers Congruence_Analysis p v s)"
| "analysis_result_covers Congruence_Analysis solver Ctx_EntryState p v s =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_congruence_entry_state_result p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>))"
| "analysis_result_covers Congruence_Analysis solver (Ctx_CallString k) p v s =
     (case solver of
        Some Solver_PerOrigin \<Rightarrow> False
      | Some Solver_Warrow \<Rightarrow> False
      | Some Solver_WarrowPerOrigin \<Rightarrow> False
      | _ \<Rightarrow>
          (\<exists>c st. lookup_context (analyse_congruence_call_string_result k p) v c = Lifted st
            \<and> s \<in> \<lbrakk>st\<rbrakk>))"

definition certified_config ::
    "analysis_domain \<Rightarrow> solver_choice option \<Rightarrow> context_mode\<Rightarrow> bool" where
  "certified_config D solver ctx =
     (resolve_analysis_config (mk_analysis_config D solver ctx) \<noteq> None)"

definition checks_sound_at :: "analysis_output \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" where
  "checks_sound_at out v s =
     (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
        row_verdict row \<noteq> Dead
      \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
      \<and> (row_verdict row = Decided Check_Refuted
           \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"

text \<open>
  One shape conversion, used by every context-sensitive instantiation below: a
  store in one activation bucket is a store the collecting semantics admits at
  that node, and the context it was filed under is a witness for the table claim.
\<close>

lemma headline_of_ctx_endpoint:
  fixes r :: "('c, 'a::sound_domain abs_state) analysis_result"
  assumes "\<exists>v stk ctx st.
             csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
           \<and> s \<in> activation_collect (declared_global p) R rc (prog_cfg p)
                     (cinit_stores (declared_global p)) v ctx
           \<and> lookup_context r v ctx = Lifted st \<and> s \<in> \<lbrakk>st\<rbrakk>
           \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
                row_verdict row \<noteq> Dead
              \<and> (row_verdict row = Decided Check_Proved
                   \<longrightarrow> truthy (aval (row_exp row) s))
              \<and> (row_verdict row = Decided Check_Refuted
                   \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
               \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                         (cinit_stores (declared_global p)) v
               \<and> (\<exists>c st. lookup_context r v c = Lifted st \<and> s \<in> \<lbrakk>st\<rbrakk>)
               \<and> checks_sound_at out v s"
  using assms activation_collect_le_ltr_collect [THEN subsetD]
  unfolding checks_sound_at_def by blast

lemma certified_config_of_Analysed:
  assumes "run_voblint D solver ctx view p = Analysed out"
  shows "certified_config D solver ctx"
  using assms unfolding certified_config_def run_voblint_def
  by (auto split: if_splits option.splits)

subsection \<open>The endpoint\<close>

text \<open>
  Run the source program, stop wherever you like, and ask any accepted
  configuration for a report: there is a graph node and frame stack for where you
  stopped, the store in your hands is one the collecting semantics really admits
  there, the table that configuration built describes it, and every check printed
  beside it holds of it, with no row there marked unreachable.

  The proof is 32 instantiations of the per-configuration endpoints and nothing
  else. A pairing whose two spellings resolve to one plan reuses one endpoint,
  since the answers are then the same term.
\<close>

theorem run_voblint_certified_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and cert: "certified_preconditions D solver ctx p"
      and ans: "run_voblint D solver ctx view p = Analysed out"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
               \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                         (cinit_stores (declared_global p)) v
               \<and> analysis_result_covers D solver ctx p v s
               \<and> checks_sound_at out v s"
proof -
  from ans have wfx: "wf_program_compile_input_exec p"
    by (simp add: run_voblint_def split: if_splits)
  note wf = wf_program_compile_input_exec_sound [OF wfx]
  note act = activation_collect_le_ltr_collect [THEN subsetD]
  show ?thesis
  proof (cases D)
    case Sign_Analysis
    show ?thesis
    proof (cases ctx)
      case Ctx_None
      show ?thesis
      proof (cases solver)
        case None
        from cert have c: "analyse_certified Sign_Analysis p"
          by (simp add: Sign_Analysis Ctx_None None)
        have a: "run_voblint Sign_Analysis None Ctx_None view p
                   = Analysed out"
          using ans by (simp add: Sign_Analysis Ctx_None None)
        from run_voblint_source_sound [OF wf c s0 run a]
        show ?thesis by (auto simp: Sign_Analysis Ctx_None None checks_sound_at_def)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have c: "analyse_certified Sign_Analysis p"
            by (simp add: Sign_Analysis Ctx_None Some Solver_Join)
          have a: "run_voblint Sign_Analysis None Ctx_None view p
                     = Analysed out"
            using ans wfx
            by (simp add: Sign_Analysis Ctx_None Some Solver_Join run_voblint_def
                mk_analysis_config_def split: if_splits)
          from run_voblint_source_sound [OF wf c s0 run a]
          show ?thesis by (auto simp: Sign_Analysis Ctx_None Some Solver_Join checks_sound_at_def)
        next
          case Solver_PerOrigin
          from cert have t: "sign_po_terminates (declared_global p) p"
            and cv: "vars_cover (prog_cfg p) (sign_po_vars (declared_global p) p)"
            by (simp_all add: Sign_Analysis Ctx_None Some Solver_PerOrigin)
          have a: "run_voblint Sign_Analysis (Some Solver_PerOrigin) Ctx_None view p
                     = Analysed out"
            using ans by (simp add: Sign_Analysis Ctx_None Some Solver_PerOrigin)
          have cap: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                             (cinit_stores (declared_global p)) u
                       \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_per_origin p) u () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
            using sign_po_asm.result_node_sound [OF t cv]
            by (simp add: sign_po_asm.state_at_unfold analyse_sign_result_per_origin_def
                analyse_sign_result_per_origin_for_def)
          from run_voblint_sign_per_origin_source_sound [OF wf s0 run t cv a]
          show ?thesis using cap
            by (auto simp: Sign_Analysis Ctx_None Some Solver_PerOrigin checks_sound_at_def)
        next
          case Solver_Warrow
          with cert Some Sign_Analysis Ctx_None
          show ?thesis by simp
        next
          case Solver_WarrowPerOrigin
          with cert Some Sign_Analysis Ctx_None
          show ?thesis by simp
        qed
      qed
    next
      case Ctx_EntryState
      show ?thesis
      proof (cases solver)
        case None
        from cert have t: "sign_entry_state_terminates_for (declared_global p) p"
          and cv: "ctx_vars_cover (prog_cfg p) (sign_es.ctx_succ (declared_global p) p) []
                    (sign_entry_state_vars (declared_global p) p)"
          by (simp_all add: Sign_Analysis Ctx_EntryState None)
        have a: "run_voblint Sign_Analysis None Ctx_EntryState view p
                   = Analysed out"
          using ans by (simp add: Sign_Analysis Ctx_EntryState None)
        from headline_of_ctx_endpoint
               [OF run_voblint_sign_entry_state_source_sound [OF wf s0 run t cv a]]
        show ?thesis by (simp add: Sign_Analysis Ctx_EntryState None)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "sign_entry_state_terminates_for (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (sign_es.ctx_succ (declared_global p) p) []
                    (sign_entry_state_vars (declared_global p) p)"
            by (simp_all add: Sign_Analysis Ctx_EntryState Some Solver_Join)
          have a: "run_voblint Sign_Analysis None Ctx_EntryState view p
                     = Analysed out"
            using ans wfx
            by (simp add: Sign_Analysis Ctx_EntryState Some Solver_Join run_voblint_def
                mk_analysis_config_def split: if_splits)
          from headline_of_ctx_endpoint
                 [OF run_voblint_sign_entry_state_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Sign_Analysis Ctx_EntryState Some Solver_Join)
        next
          case Solver_PerOrigin
          with cert Some Sign_Analysis Ctx_EntryState
          show ?thesis by simp
        next
          case Solver_Warrow
          with cert Some Sign_Analysis Ctx_EntryState
          show ?thesis by simp
        next
          case Solver_WarrowPerOrigin
          with cert Some Sign_Analysis Ctx_EntryState
          show ?thesis by simp
        qed
      qed
    next
      case (Ctx_CallString k)
      show ?thesis
      proof (cases solver)
        case None
        from cert have t: "sign_cs_terminates k (declared_global p) p"
          and cv: "ctx_vars_cover (prog_cfg p) (sign_cs_ctx_succ k (declared_global p) p) []
                    (sign_cs_vars k (declared_global p) p)"
          by (simp_all add: Sign_Analysis Ctx_CallString None)
        have a: "run_voblint Sign_Analysis None (Ctx_CallString k) view p
                   = Analysed out"
          using ans by (simp add: Sign_Analysis Ctx_CallString None)
        from headline_of_ctx_endpoint
               [OF run_voblint_sign_call_string_source_sound [OF wf s0 run t cv a]]
        show ?thesis by (simp add: Sign_Analysis Ctx_CallString None)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "sign_cs_terminates k (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (sign_cs_ctx_succ k (declared_global p) p) []
                    (sign_cs_vars k (declared_global p) p)"
            by (simp_all add: Sign_Analysis Ctx_CallString Some Solver_Join)
          have a: "run_voblint Sign_Analysis None (Ctx_CallString k) view p
                     = Analysed out"
            using ans wfx
            by (simp add: Sign_Analysis Ctx_CallString Some Solver_Join run_voblint_def
                mk_analysis_config_def split: if_splits)
          from headline_of_ctx_endpoint
                 [OF run_voblint_sign_call_string_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Sign_Analysis Ctx_CallString Some Solver_Join)
        next
          case Solver_PerOrigin
          with cert Some Sign_Analysis Ctx_CallString
          show ?thesis by simp
        next
          case Solver_Warrow
          with cert Some Sign_Analysis Ctx_CallString
          show ?thesis by simp
        next
          case Solver_WarrowPerOrigin
          with cert Some Sign_Analysis Ctx_CallString
          show ?thesis by simp
        qed
      qed
    qed
  next
    case Interval_Analysis
    show ?thesis
    proof (cases ctx)
      case Ctx_None
      show ?thesis
      proof (cases solver)
        case None
        from cert have c: "analyse_certified Interval_Analysis p"
          by (simp add: Interval_Analysis Ctx_None None)
        have a: "run_voblint Interval_Analysis None Ctx_None view p
                   = Analysed out"
          using ans by (simp add: Interval_Analysis Ctx_None None)
        from run_voblint_source_sound [OF wf c s0 run a]
        show ?thesis by (auto simp: Interval_Analysis Ctx_None None checks_sound_at_def)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "interval_join_terminates (declared_global p) p"
            and cv: "vars_cover (prog_cfg p) (interval_join_vars (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_None Some Solver_Join)
          have a: "run_voblint Interval_Analysis (Some Solver_Join) Ctx_None view p
                     = Analysed out"
            using ans by (simp add: Interval_Analysis Ctx_None Some Solver_Join)
          have cap: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                             (cinit_stores (declared_global p)) u
                       \<subseteq> \<lbrakk>case lookup_context (analyse_interval_result_join p) u () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
            using interval_join_asm.result_node_sound [OF t cv]
            by (simp add: interval_join_asm.state_at_unfold analyse_interval_result_join_def
                analyse_interval_result_join_for_def)
          from run_voblint_interval_join_source_sound [OF wf s0 run t cv a]
          show ?thesis using cap
            by (auto simp: Interval_Analysis Ctx_None Some Solver_Join checks_sound_at_def)
        next
          case Solver_PerOrigin
          from cert have t: "interval_po_terminates (declared_global p) p"
            and cv: "vars_cover (prog_cfg p) (interval_po_vars (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_None Some Solver_PerOrigin)
          have a: "run_voblint Interval_Analysis (Some Solver_PerOrigin) Ctx_None view p
                     = Analysed out"
            using ans by (simp add: Interval_Analysis Ctx_None Some Solver_PerOrigin)
          have cap: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                             (cinit_stores (declared_global p)) u
                       \<subseteq> \<lbrakk>case lookup_context (analyse_interval_result_per_origin p) u () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
            using interval_po_asm.result_node_sound [OF t cv]
            by (simp add: interval_po_asm.state_at_unfold analyse_interval_result_per_origin_def
                analyse_interval_result_per_origin_for_def)
          from run_voblint_interval_per_origin_source_sound [OF wf s0 run t cv a]
          show ?thesis using cap
            by (auto simp: Interval_Analysis Ctx_None Some Solver_PerOrigin checks_sound_at_def)
        next
          case Solver_Warrow
          from cert have c: "analyse_certified Interval_Analysis p"
            by (simp add: Interval_Analysis Ctx_None Some Solver_Warrow)
          have a: "run_voblint Interval_Analysis None Ctx_None view p
                     = Analysed out"
            using ans wfx
            by (simp add: Interval_Analysis Ctx_None Some Solver_Warrow run_voblint_def
                mk_analysis_config_def split: if_splits)
          from run_voblint_source_sound [OF wf c s0 run a]
          show ?thesis
            by (auto simp: Interval_Analysis Ctx_None Some Solver_Warrow checks_sound_at_def)
        next
          case Solver_WarrowPerOrigin
          from cert have t: "interval_wpo_terminates (declared_global p) p"
            and cv: "vars_cover (prog_cfg p) (interval_wpo_vars (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_None Some Solver_WarrowPerOrigin)
          have a: "run_voblint Interval_Analysis (Some Solver_WarrowPerOrigin) Ctx_None view p
                     = Analysed out"
            using ans by (simp add: Interval_Analysis Ctx_None Some Solver_WarrowPerOrigin)
          have cap: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                             (cinit_stores (declared_global p)) u
                       \<subseteq> \<lbrakk>case lookup_context (analyse_interval_result_wpo p) u () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
            using interval_wpo_asm.result_node_sound [OF t cv]
            by (simp add: interval_wpo_asm.state_at_unfold analyse_interval_result_wpo_def
                analyse_interval_result_wpo_for_def)
          from run_voblint_interval_wpo_source_sound [OF wf s0 run t cv a]
          show ?thesis using cap
            by (auto simp: Interval_Analysis Ctx_None Some Solver_WarrowPerOrigin
                checks_sound_at_def)
        qed
      qed
    next
      case Ctx_EntryState
      show ?thesis
      proof (cases solver)
        case None
        from cert have t: "entry_state_terminates_prog (declared_global p) p"
          and cv: "ctx_vars_cover (prog_cfg p) (interval_es.ctx_succ (declared_global p) p) []
                    (entry_state_vars_prog (declared_global p) p)"
          by (simp_all add: Interval_Analysis Ctx_EntryState None)
        have a: "run_voblint Interval_Analysis None Ctx_EntryState view p
                   = Analysed out"
          using ans by (simp add: Interval_Analysis Ctx_EntryState None)
        from headline_of_ctx_endpoint
               [OF run_voblint_interval_entry_state_source_sound [OF wf s0 run t cv a]]
        show ?thesis by (simp add: Interval_Analysis Ctx_EntryState None)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "interval_es_join.terminates (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p)
                    (interval_es_join.ctx_succ (declared_global p) p) []
                    (interval_es_join.sol_vars (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_EntryState Some Solver_Join)
          have a: "run_voblint Interval_Analysis (Some Solver_Join) Ctx_EntryState view p
                     = Analysed out"
            using ans by (simp add: Interval_Analysis Ctx_EntryState Some Solver_Join)
          from headline_of_ctx_endpoint
                 [OF run_voblint_interval_entry_state_join_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Interval_Analysis Ctx_EntryState Some Solver_Join)
        next
          case Solver_PerOrigin
          from cert have t: "interval_es_po.terminates (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p)
                    (interval_es_po.ctx_succ (declared_global p) p) []
                    (interval_es_po.sol_vars (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_EntryState Some Solver_PerOrigin)
          have a: "run_voblint Interval_Analysis (Some Solver_PerOrigin) Ctx_EntryState view p
                     = Analysed out"
            using ans by (simp add: Interval_Analysis Ctx_EntryState Some Solver_PerOrigin)
          from headline_of_ctx_endpoint
                 [OF run_voblint_interval_entry_state_per_origin_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Interval_Analysis Ctx_EntryState Some Solver_PerOrigin)
        next
          case Solver_Warrow
          from cert have t: "entry_state_terminates_prog (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (interval_es.ctx_succ (declared_global p) p) []
                    (entry_state_vars_prog (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_EntryState Some Solver_Warrow)
          have a: "run_voblint Interval_Analysis None Ctx_EntryState view p
                     = Analysed out"
            using ans wfx
            by (simp add: Interval_Analysis Ctx_EntryState Some Solver_Warrow run_voblint_def
                mk_analysis_config_def split: if_splits)
          from headline_of_ctx_endpoint
                 [OF run_voblint_interval_entry_state_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Interval_Analysis Ctx_EntryState Some Solver_Warrow)
        next
          case Solver_WarrowPerOrigin
          from cert have t: "interval_es_wpo.terminates (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p)
                    (interval_es_wpo.ctx_succ (declared_global p) p) []
                    (interval_es_wpo.sol_vars (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_EntryState Some Solver_WarrowPerOrigin)
          have a: "run_voblint Interval_Analysis (Some Solver_WarrowPerOrigin) Ctx_EntryState view p
                     = Analysed out"
            using ans by (simp add: Interval_Analysis Ctx_EntryState Some Solver_WarrowPerOrigin)
          from headline_of_ctx_endpoint
                 [OF run_voblint_interval_entry_state_wpo_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Interval_Analysis Ctx_EntryState Some Solver_WarrowPerOrigin)
        qed
      qed
    next
      case (Ctx_CallString k)
      show ?thesis
      proof (cases solver)
        case None
        from cert have t: "interval_cs_terminates k (declared_global p) p"
          and cv: "ctx_vars_cover (prog_cfg p) (interval_cs_ctx_succ k (declared_global p) p) []
                    (interval_cs_vars k (declared_global p) p)"
          by (simp_all add: Interval_Analysis Ctx_CallString None)
        have a: "run_voblint Interval_Analysis None (Ctx_CallString k) view p
                   = Analysed out"
          using ans by (simp add: Interval_Analysis Ctx_CallString None)
        from headline_of_ctx_endpoint
               [OF run_voblint_interval_call_string_source_sound [OF wf s0 run t cv a]]
        show ?thesis by (simp add: Interval_Analysis Ctx_CallString None)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "interval_cs_join_terminates k (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (interval_cs_join_ctx_succ k (declared_global p) p)
                []
                    (interval_cs_join_vars k (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_CallString Some Solver_Join)
          have a: "run_voblint Interval_Analysis (Some Solver_Join) (Ctx_CallString k) view p
                     = Analysed out"
            using ans by (simp add: Interval_Analysis Ctx_CallString Some Solver_Join)
          from headline_of_ctx_endpoint
                 [OF run_voblint_interval_call_string_join_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Interval_Analysis Ctx_CallString Some Solver_Join)
        next
          case Solver_PerOrigin
          from cert have t: "interval_cs_po_terminates k (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (interval_cs_po_ctx_succ k (declared_global p) p)
                []
                    (interval_cs_po_vars k (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_CallString Some Solver_PerOrigin)
          have a: "run_voblint Interval_Analysis (Some Solver_PerOrigin) (Ctx_CallString k) view p
                     = Analysed out"
            using ans by (simp add: Interval_Analysis Ctx_CallString Some Solver_PerOrigin)
          from headline_of_ctx_endpoint
                 [OF run_voblint_interval_call_string_po_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Interval_Analysis Ctx_CallString Some Solver_PerOrigin)
        next
          case Solver_Warrow
          from cert have t: "interval_cs_terminates k (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (interval_cs_ctx_succ k (declared_global p) p) []
                    (interval_cs_vars k (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_CallString Some Solver_Warrow)
          have a: "run_voblint Interval_Analysis None (Ctx_CallString k) view p
                     = Analysed out"
            using ans wfx
            by (simp add: Interval_Analysis Ctx_CallString Some Solver_Warrow run_voblint_def
                mk_analysis_config_def split: if_splits)
          from headline_of_ctx_endpoint
                 [OF run_voblint_interval_call_string_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Interval_Analysis Ctx_CallString Some Solver_Warrow)
        next
          case Solver_WarrowPerOrigin
          from cert have t: "interval_cs_wpo_terminates k (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (interval_cs_wpo_ctx_succ k (declared_global p) p)
                []
                    (interval_cs_wpo_vars k (declared_global p) p)"
            by (simp_all add: Interval_Analysis Ctx_CallString Some Solver_WarrowPerOrigin)
          have a: "run_voblint Interval_Analysis (Some Solver_WarrowPerOrigin) (Ctx_CallString k)
              view p
                     = Analysed out"
            using ans by (simp add: Interval_Analysis Ctx_CallString Some Solver_WarrowPerOrigin)
          from headline_of_ctx_endpoint
                 [OF run_voblint_interval_call_string_wpo_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Interval_Analysis Ctx_CallString Some Solver_WarrowPerOrigin)
        qed
      qed
    qed
  next
    case Int_Analysis
    show ?thesis
    proof (cases ctx)
      case Ctx_None
      show ?thesis
      proof (cases solver)
        case None
        from cert have c: "analyse_certified Int_Analysis p"
          by (simp add: Int_Analysis Ctx_None None)
        have a: "run_voblint Int_Analysis None Ctx_None view p
                   = Analysed out"
          using ans by (simp add: Int_Analysis Ctx_None None)
        from run_voblint_source_sound [OF wf c s0 run a]
        show ?thesis by (auto simp: Int_Analysis Ctx_None None checks_sound_at_def)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "int_join_terminates (declared_global p) p"
            and cv: "vars_cover (prog_cfg p) (int_join_vars (declared_global p) p)"
            by (simp_all add: Int_Analysis Ctx_None Some Solver_Join)
          have a: "run_voblint Int_Analysis (Some Solver_Join) Ctx_None view p
                     = Analysed out"
            using ans by (simp add: Int_Analysis Ctx_None Some Solver_Join)
          have cap: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                             (cinit_stores (declared_global p)) u
                       \<subseteq> \<lbrakk>case lookup_context (analyse_int_join_result p) u () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
            using int_join_asm.result_node_sound [OF t cv]
            by (simp add: int_join_asm.state_at_unfold analyse_int_join_result_def
                analyse_int_join_result_for_def int_join_result_def)
          from run_voblint_int_join_source_sound [OF wf s0 run t cv a]
          show ?thesis using cap
            by (auto simp: Int_Analysis Ctx_None Some Solver_Join checks_sound_at_def)
        next
          case Solver_PerOrigin
          from cert have t: "int_po_terminates (declared_global p) p"
            and cv: "vars_cover (prog_cfg p) (int_po_vars (declared_global p) p)"
            by (simp_all add: Int_Analysis Ctx_None Some Solver_PerOrigin)
          have a: "run_voblint Int_Analysis (Some Solver_PerOrigin) Ctx_None view p
                     = Analysed out"
            using ans by (simp add: Int_Analysis Ctx_None Some Solver_PerOrigin)
          have cap: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                             (cinit_stores (declared_global p)) u
                       \<subseteq> \<lbrakk>case lookup_context (analyse_int_per_origin_result p) u () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
            using int_po_asm.result_node_sound [OF t cv]
            by (simp add: int_po_asm.state_at_unfold analyse_int_per_origin_result_def
                analyse_int_per_origin_result_for_def int_po_result_def)
          from run_voblint_int_per_origin_source_sound [OF wf s0 run t cv a]
          show ?thesis using cap
            by (auto simp: Int_Analysis Ctx_None Some Solver_PerOrigin checks_sound_at_def)
        next
          case Solver_Warrow
          from cert have c: "analyse_certified Int_Analysis p"
            by (simp add: Int_Analysis Ctx_None Some Solver_Warrow)
          have a: "run_voblint Int_Analysis None Ctx_None view p
                     = Analysed out"
            using ans wfx
            by (simp add: Int_Analysis Ctx_None Some Solver_Warrow run_voblint_def
                mk_analysis_config_def split: if_splits)
          from run_voblint_source_sound [OF wf c s0 run a]
          show ?thesis by (auto simp: Int_Analysis Ctx_None Some Solver_Warrow checks_sound_at_def)
        next
          case Solver_WarrowPerOrigin
          from cert have t: "int_wpo_terminates (declared_global p) p"
            and cv: "vars_cover (prog_cfg p) (int_wpo_vars (declared_global p) p)"
            by (simp_all add: Int_Analysis Ctx_None Some Solver_WarrowPerOrigin)
          have a: "run_voblint Int_Analysis (Some Solver_WarrowPerOrigin) Ctx_None view p
                     = Analysed out"
            using ans by (simp add: Int_Analysis Ctx_None Some Solver_WarrowPerOrigin)
          have cap: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                             (cinit_stores (declared_global p)) u
                       \<subseteq> \<lbrakk>case lookup_context (analyse_int_wpo_result p) u () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
            using int_wpo_asm.result_node_sound [OF t cv]
            by (simp add: int_wpo_asm.state_at_unfold analyse_int_wpo_result_def
                analyse_int_wpo_result_for_def int_wpo_result_def)
          from run_voblint_int_wpo_source_sound [OF wf s0 run t cv a]
          show ?thesis using cap
            by (auto simp: Int_Analysis Ctx_None Some Solver_WarrowPerOrigin checks_sound_at_def)
        qed
      qed
    next
      case Ctx_EntryState
      show ?thesis
      proof (cases solver)
        case None
        from cert have t: "int_es_terminates (declared_global p) p"
          and cv: "ctx_vars_cover (prog_cfg p) (int_es_ctx_succ (declared_global p) p) []
                    (int_es_vars (declared_global p) p)"
          by (simp_all add: Int_Analysis Ctx_EntryState None)
        have a: "run_voblint Int_Analysis None Ctx_EntryState view p
                   = Analysed out"
          using ans by (simp add: Int_Analysis Ctx_EntryState None)
        from headline_of_ctx_endpoint
               [OF run_voblint_int_entry_state_source_sound [OF wf s0 run t cv a]]
        show ?thesis by (simp add: Int_Analysis Ctx_EntryState None)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "int_es_join_terminates (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (int_es_join_ctx_succ (declared_global p) p) []
                    (int_es_join_vars (declared_global p) p)"
            by (simp_all add: Int_Analysis Ctx_EntryState Some Solver_Join)
          have a: "run_voblint Int_Analysis (Some Solver_Join) Ctx_EntryState view p
                     = Analysed out"
            using ans by (simp add: Int_Analysis Ctx_EntryState Some Solver_Join)
          from headline_of_ctx_endpoint
                 [OF run_voblint_int_entry_state_join_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Int_Analysis Ctx_EntryState Some Solver_Join)
        next
          case Solver_PerOrigin
          with cert Some Int_Analysis Ctx_EntryState
          show ?thesis by simp
        next
          case Solver_Warrow
          from cert have t: "int_es_terminates (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (int_es_ctx_succ (declared_global p) p) []
                    (int_es_vars (declared_global p) p)"
            by (simp_all add: Int_Analysis Ctx_EntryState Some Solver_Warrow)
          have a: "run_voblint Int_Analysis None Ctx_EntryState view p
                     = Analysed out"
            using ans wfx
            by (simp add: Int_Analysis Ctx_EntryState Some Solver_Warrow run_voblint_def
                mk_analysis_config_def split: if_splits)
          from headline_of_ctx_endpoint
                 [OF run_voblint_int_entry_state_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Int_Analysis Ctx_EntryState Some Solver_Warrow)
        next
          case Solver_WarrowPerOrigin
          with cert Some Int_Analysis Ctx_EntryState
          show ?thesis by simp
        qed
      qed
    next
      case (Ctx_CallString k)
      show ?thesis
      proof (cases solver)
        case None
        from cert have t: "int_cs_terminates k (declared_global p) p"
          and cv: "ctx_vars_cover (prog_cfg p) (int_cs_ctx_succ k (declared_global p) p) []
                    (int_cs_vars k (declared_global p) p)"
          by (simp_all add: Int_Analysis Ctx_CallString None)
        have a: "run_voblint Int_Analysis None (Ctx_CallString k) view p
                   = Analysed out"
          using ans by (simp add: Int_Analysis Ctx_CallString None)
        from headline_of_ctx_endpoint
               [OF run_voblint_int_call_string_source_sound [OF wf s0 run t cv a]]
        show ?thesis by (simp add: Int_Analysis Ctx_CallString None)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "int_cs_join_terminates k (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (int_cs_join_ctx_succ k (declared_global p) p) []
                    (int_cs_join_vars k (declared_global p) p)"
            by (simp_all add: Int_Analysis Ctx_CallString Some Solver_Join)
          have a: "run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString k) view p
                     = Analysed out"
            using ans by (simp add: Int_Analysis Ctx_CallString Some Solver_Join)
          from headline_of_ctx_endpoint
                 [OF run_voblint_int_call_string_join_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Int_Analysis Ctx_CallString Some Solver_Join)
        next
          case Solver_PerOrigin
          with cert Some Int_Analysis Ctx_CallString
          show ?thesis by simp
        next
          case Solver_Warrow
          from cert have t: "int_cs_terminates k (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (int_cs_ctx_succ k (declared_global p) p) []
                    (int_cs_vars k (declared_global p) p)"
            by (simp_all add: Int_Analysis Ctx_CallString Some Solver_Warrow)
          have a: "run_voblint Int_Analysis None (Ctx_CallString k) view p
                     = Analysed out"
            using ans wfx
            by (simp add: Int_Analysis Ctx_CallString Some Solver_Warrow run_voblint_def
                mk_analysis_config_def split: if_splits)
          from headline_of_ctx_endpoint
                 [OF run_voblint_int_call_string_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Int_Analysis Ctx_CallString Some Solver_Warrow)
        next
          case Solver_WarrowPerOrigin
          with cert Some Int_Analysis Ctx_CallString
          show ?thesis by simp
        qed
      qed
    qed
  next
    case Parity_Analysis
    show ?thesis
    proof (cases ctx)
      case Ctx_None
      show ?thesis
      proof (cases solver)
        case None
        from cert have c: "analyse_certified Parity_Analysis p"
          by (simp add: Parity_Analysis Ctx_None None)
        have a: "run_voblint Parity_Analysis None Ctx_None view p
                   = Analysed out"
          using ans by (simp add: Parity_Analysis Ctx_None None)
        from run_voblint_source_sound [OF wf c s0 run a]
        show ?thesis by (auto simp: Parity_Analysis Ctx_None None checks_sound_at_def)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have c: "analyse_certified Parity_Analysis p"
            by (simp add: Parity_Analysis Ctx_None Some Solver_Join)
          have a: "run_voblint Parity_Analysis None Ctx_None view p
                     = Analysed out"
            using ans wfx
            by (simp add: Parity_Analysis Ctx_None Some Solver_Join run_voblint_def
                mk_analysis_config_def split: if_splits)
          from run_voblint_source_sound [OF wf c s0 run a]
          show ?thesis by (auto simp: Parity_Analysis Ctx_None Some Solver_Join checks_sound_at_def)
        next
          case Solver_PerOrigin
          from cert have t: "parity_po_terminates (declared_global p) p"
            and cv: "vars_cover (prog_cfg p) (parity_po_vars (declared_global p) p)"
            by (simp_all add: Parity_Analysis Ctx_None Some Solver_PerOrigin)
          have a: "run_voblint Parity_Analysis (Some Solver_PerOrigin) Ctx_None view p
                     = Analysed out"
            using ans by (simp add: Parity_Analysis Ctx_None Some Solver_PerOrigin)
          have cap: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                             (cinit_stores (declared_global p)) u
                       \<subseteq> \<lbrakk>case lookup_context (analyse_parity_result_per_origin p) u () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
            using parity_po_asm.result_node_sound [OF t cv]
            by (simp add: parity_po_asm.state_at_unfold analyse_parity_result_per_origin_def
                analyse_parity_result_per_origin_for_def)
          from run_voblint_parity_per_origin_source_sound [OF wf s0 run t cv a]
          show ?thesis using cap
            by (auto simp: Parity_Analysis Ctx_None Some Solver_PerOrigin checks_sound_at_def)
        next
          case Solver_Warrow
          with cert Some Parity_Analysis Ctx_None
          show ?thesis by simp
        next
          case Solver_WarrowPerOrigin
          with cert Some Parity_Analysis Ctx_None
          show ?thesis by simp
        qed
      qed
    next
      case Ctx_EntryState
      show ?thesis
      proof (cases solver)
        case None
        from cert have t: "parity_entry_state_terminates_for (declared_global p) p"
          and cv: "ctx_vars_cover (prog_cfg p) (parity_es.ctx_succ (declared_global p) p) []
                    (parity_entry_state_vars (declared_global p) p)"
          by (simp_all add: Parity_Analysis Ctx_EntryState None)
        have a: "run_voblint Parity_Analysis None Ctx_EntryState view p
                   = Analysed out"
          using ans by (simp add: Parity_Analysis Ctx_EntryState None)
        from headline_of_ctx_endpoint
               [OF run_voblint_parity_entry_state_source_sound [OF wf s0 run t cv a]]
        show ?thesis by (simp add: Parity_Analysis Ctx_EntryState None)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "parity_entry_state_terminates_for (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (parity_es.ctx_succ (declared_global p) p) []
                    (parity_entry_state_vars (declared_global p) p)"
            by (simp_all add: Parity_Analysis Ctx_EntryState Some Solver_Join)
          have a: "run_voblint Parity_Analysis None Ctx_EntryState view p
                     = Analysed out"
            using ans wfx
            by (simp add: Parity_Analysis Ctx_EntryState Some Solver_Join run_voblint_def
                mk_analysis_config_def split: if_splits)
          from headline_of_ctx_endpoint
                 [OF run_voblint_parity_entry_state_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Parity_Analysis Ctx_EntryState Some Solver_Join)
        next
          case Solver_PerOrigin
          with cert Some Parity_Analysis Ctx_EntryState
          show ?thesis by simp
        next
          case Solver_Warrow
          with cert Some Parity_Analysis Ctx_EntryState
          show ?thesis by simp
        next
          case Solver_WarrowPerOrigin
          with cert Some Parity_Analysis Ctx_EntryState
          show ?thesis by simp
        qed
      qed
    next
      case (Ctx_CallString k)
      show ?thesis
      proof (cases solver)
        case None
        from cert have t: "parity_cs_terminates k (declared_global p) p"
          and cv: "ctx_vars_cover (prog_cfg p) (parity_cs_ctx_succ k (declared_global p) p) []
                    (parity_cs_vars k (declared_global p) p)"
          by (simp_all add: Parity_Analysis Ctx_CallString None)
        have a: "run_voblint Parity_Analysis None (Ctx_CallString k) view p
                   = Analysed out"
          using ans by (simp add: Parity_Analysis Ctx_CallString None)
        from headline_of_ctx_endpoint
               [OF run_voblint_parity_call_string_source_sound [OF wf s0 run t cv a]]
        show ?thesis by (simp add: Parity_Analysis Ctx_CallString None)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "parity_cs_terminates k (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (parity_cs_ctx_succ k (declared_global p) p) []
                    (parity_cs_vars k (declared_global p) p)"
            by (simp_all add: Parity_Analysis Ctx_CallString Some Solver_Join)
          have a: "run_voblint Parity_Analysis None (Ctx_CallString k) view p
                     = Analysed out"
            using ans wfx
            by (simp add: Parity_Analysis Ctx_CallString Some Solver_Join run_voblint_def
                mk_analysis_config_def split: if_splits)
          from headline_of_ctx_endpoint
                 [OF run_voblint_parity_call_string_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Parity_Analysis Ctx_CallString Some Solver_Join)
        next
          case Solver_PerOrigin
          with cert Some Parity_Analysis Ctx_CallString
          show ?thesis by simp
        next
          case Solver_Warrow
          with cert Some Parity_Analysis Ctx_CallString
          show ?thesis by simp
        next
          case Solver_WarrowPerOrigin
          with cert Some Parity_Analysis Ctx_CallString
          show ?thesis by simp
        qed
      qed
    qed
  next
    case Congruence_Analysis
    show ?thesis
    proof (cases ctx)
      case Ctx_None
      show ?thesis
      proof (cases solver)
        case None
        from cert have c: "analyse_certified Congruence_Analysis p"
          by (simp add: Congruence_Analysis Ctx_None None)
        have a: "run_voblint Congruence_Analysis None Ctx_None view p
                   = Analysed out"
          using ans by (simp add: Congruence_Analysis Ctx_None None)
        from run_voblint_source_sound [OF wf c s0 run a]
        show ?thesis by (auto simp: Congruence_Analysis Ctx_None None checks_sound_at_def)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have c: "analyse_certified Congruence_Analysis p"
            by (simp add: Congruence_Analysis Ctx_None Some Solver_Join)
          have a: "run_voblint Congruence_Analysis None Ctx_None view p
                     = Analysed out"
            using ans wfx
            by (simp add: Congruence_Analysis Ctx_None Some Solver_Join run_voblint_def
                mk_analysis_config_def split: if_splits)
          from run_voblint_source_sound [OF wf c s0 run a]
          show ?thesis
            by (auto simp: Congruence_Analysis Ctx_None Some Solver_Join checks_sound_at_def)
        next
          case Solver_PerOrigin
          from cert have t: "congruence_po_terminates (declared_global p) p"
            and cv: "vars_cover (prog_cfg p) (congruence_po_vars (declared_global p) p)"
            by (simp_all add: Congruence_Analysis Ctx_None Some Solver_PerOrigin)
          have a: "run_voblint Congruence_Analysis (Some Solver_PerOrigin) Ctx_None view p
                     = Analysed out"
            using ans by (simp add: Congruence_Analysis Ctx_None Some Solver_PerOrigin)
          have cap: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                             (cinit_stores (declared_global p)) u
                       \<subseteq> \<lbrakk>case lookup_context (analyse_congruence_result_per_origin p) u () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
            using congruence_po_asm.result_node_sound [OF t cv]
            by (simp add: congruence_po_asm.state_at_unfold analyse_congruence_result_per_origin_def
                analyse_congruence_result_per_origin_for_def)
          from run_voblint_congruence_per_origin_source_sound [OF wf s0 run t cv a]
          show ?thesis using cap
            by (auto simp: Congruence_Analysis Ctx_None Some Solver_PerOrigin checks_sound_at_def)
        next
          case Solver_Warrow
          with cert Some Congruence_Analysis Ctx_None
          show ?thesis by simp
        next
          case Solver_WarrowPerOrigin
          with cert Some Congruence_Analysis Ctx_None
          show ?thesis by simp
        qed
      qed
    next
      case Ctx_EntryState
      show ?thesis
      proof (cases solver)
        case None
        from cert have t: "congruence_entry_state_terminates_for (declared_global p) p"
          and cv: "ctx_vars_cover (prog_cfg p) (congruence_es.ctx_succ (declared_global p) p) []
                    (congruence_entry_state_vars (declared_global p) p)"
          by (simp_all add: Congruence_Analysis Ctx_EntryState None)
        have a: "run_voblint Congruence_Analysis None Ctx_EntryState view p
                   = Analysed out"
          using ans by (simp add: Congruence_Analysis Ctx_EntryState None)
        from headline_of_ctx_endpoint
               [OF run_voblint_congruence_entry_state_source_sound [OF wf s0 run t cv a]]
        show ?thesis by (simp add: Congruence_Analysis Ctx_EntryState None)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "congruence_entry_state_terminates_for (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (congruence_es.ctx_succ (declared_global p) p) []
                    (congruence_entry_state_vars (declared_global p) p)"
            by (simp_all add: Congruence_Analysis Ctx_EntryState Some Solver_Join)
          have a: "run_voblint Congruence_Analysis None Ctx_EntryState view p
                     = Analysed out"
            using ans wfx
            by (simp add: Congruence_Analysis Ctx_EntryState Some Solver_Join run_voblint_def
                mk_analysis_config_def split: if_splits)
          from headline_of_ctx_endpoint
                 [OF run_voblint_congruence_entry_state_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Congruence_Analysis Ctx_EntryState Some Solver_Join)
        next
          case Solver_PerOrigin
          with cert Some Congruence_Analysis Ctx_EntryState
          show ?thesis by simp
        next
          case Solver_Warrow
          with cert Some Congruence_Analysis Ctx_EntryState
          show ?thesis by simp
        next
          case Solver_WarrowPerOrigin
          with cert Some Congruence_Analysis Ctx_EntryState
          show ?thesis by simp
        qed
      qed
    next
      case (Ctx_CallString k)
      show ?thesis
      proof (cases solver)
        case None
        from cert have t: "congruence_cs_terminates k (declared_global p) p"
          and cv: "ctx_vars_cover (prog_cfg p) (congruence_cs_ctx_succ k (declared_global p) p) []
                    (congruence_cs_vars k (declared_global p) p)"
          by (simp_all add: Congruence_Analysis Ctx_CallString None)
        have a: "run_voblint Congruence_Analysis None (Ctx_CallString k) view p
                   = Analysed out"
          using ans by (simp add: Congruence_Analysis Ctx_CallString None)
        from headline_of_ctx_endpoint
               [OF run_voblint_congruence_call_string_source_sound [OF wf s0 run t cv a]]
        show ?thesis by (simp add: Congruence_Analysis Ctx_CallString None)
      next
        case (Some sc)
        show ?thesis
        proof (cases sc)
          case Solver_Join
          from cert have t: "congruence_cs_terminates k (declared_global p) p"
            and cv: "ctx_vars_cover (prog_cfg p) (congruence_cs_ctx_succ k (declared_global p) p) []
                    (congruence_cs_vars k (declared_global p) p)"
            by (simp_all add: Congruence_Analysis Ctx_CallString Some Solver_Join)
          have a: "run_voblint Congruence_Analysis None (Ctx_CallString k) view p
                     = Analysed out"
            using ans wfx
            by (simp add: Congruence_Analysis Ctx_CallString Some Solver_Join run_voblint_def
                mk_analysis_config_def split: if_splits)
          from headline_of_ctx_endpoint
                 [OF run_voblint_congruence_call_string_source_sound [OF wf s0 run t cv a]]
          show ?thesis by (simp add: Congruence_Analysis Ctx_CallString Some Solver_Join)
        next
          case Solver_PerOrigin
          with cert Some Congruence_Analysis Ctx_CallString
          show ?thesis by simp
        next
          case Solver_Warrow
          with cert Some Congruence_Analysis Ctx_CallString
          show ?thesis by simp
        next
          case Solver_WarrowPerOrigin
          with cert Some Congruence_Analysis Ctx_CallString
          show ?thesis by simp
        qed
      qed
    qed
  qed
qed

end
