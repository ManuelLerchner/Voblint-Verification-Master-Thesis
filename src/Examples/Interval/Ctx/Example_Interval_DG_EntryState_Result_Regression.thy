theory Example_Interval_DG_EntryState_Result_Regression
  imports
    Example_Interval_DG_Ctx_Globals_Regression
    Example_Interval_DG_Ctx_Factorial_Regression
begin

section \<open>Regression: the entry-state solved-result table\<close>

text \<open>
  Acceptance witnesses for \<^const>\<open>analyse_interval_entry_state_result\<close>, the
  context-sensitive reading of the entry-state D/G solution as an
  \<^type>\<open>analysis_result\<close>. The two programs under test are the ones the
  sibling entry-state regressions already solve: \<^const>\<open>gcall_prog\<close>, whose
  three calls to \<open>bump\<close> keep three activations of one callee apart while a
  declared global crosses each call boundary, and \<^const>\<open>fact_prog\<close>, whose
  recursive base-case branch is structurally dead inside every \<open>n>=2\<close>
  activation.

  What is under test here is the result table, not those solutions: the
  contexts stay explicit rather than being joined away, a covered context and
  an uncovered one are answered differently, and a covered-but-dead context
  reads as \<^const>\<open>Unreachable\<close> instead of as a bottom state the caller has to
  recognize itself.
\<close>

definition gcall_result :: "(ivl list, ivl abs_state) analysis_result" where
  "gcall_result = analyse_interval_entry_state_result gcall_prog"

abbreviation bump_entry :: cfg_node where
  "bump_entry \<equiv> FunctionEntry (STR ''bump'')"

subsection \<open>Multiple contexts stay explicit at one callee entry\<close>

text \<open>
  All three activations of \<open>bump\<close> are covered at its \<^const>\<open>FunctionEntry\<close>
  node, each under its own routed context, and the table keeps them apart.
  Nothing here consults a join.
\<close>

lemma gcall_result_bump_contexts:
  "contexts_at gcall_result bump_entry
     = {gcall_ctx_first, gcall_ctx_second, gcall_ctx_third}"
  by eval

lemma gcall_result_bump_context_count:
  "card (contexts_at gcall_result bump_entry) = 3"
  by eval

subsection \<open>A global crossing a call boundary, per activation\<close>

text \<open>
  Each context's own state, read straight off the table: the formal \<open>n\<close> binds
  to that activation's argument, and the global \<open>g\<close> arrives at the value the
  caller had written by that call site. The third activation's argument is the
  global itself, so its context and its entered \<open>n\<close> both carry the caller's
  live value rather than a placeholder.
\<close>

lemma gcall_result_bump_first:
  "map_point_state (\<lambda>st. (st (STR ''g''), st (STR ''n'')))
     (lookup_context gcall_result bump_entry gcall_ctx_first)
   = Reachable (Ivl (Fin 10) (Fin 10), Ivl (Fin 5) (Fin 5))"
  by eval

lemma gcall_result_bump_second:
  "map_point_state (\<lambda>st. (st (STR ''g''), st (STR ''n'')))
     (lookup_context gcall_result bump_entry gcall_ctx_second)
   = Reachable (Ivl (Fin 15) (Fin 15), Ivl (Fin 4) (Fin 4))"
  by eval

lemma gcall_result_bump_third:
  "map_point_state (\<lambda>st. (st (STR ''g''), st (STR ''n'')))
     (lookup_context gcall_result bump_entry gcall_ctx_third)
   = Reachable (Ivl (Fin 19) (Fin 19), Ivl (Fin 19) (Fin 19))"
  by eval

text \<open>The three per-context states are pairwise different, so the contexts
  above are not three names for one shared unknown.\<close>

lemma gcall_result_bump_states_distinct:
  "map_point_state (\<lambda>st. st (STR ''n''))
     (lookup_context gcall_result bump_entry gcall_ctx_first)
   \<noteq> map_point_state (\<lambda>st. st (STR ''n''))
       (lookup_context gcall_result bump_entry gcall_ctx_second)"
  "map_point_state (\<lambda>st. st (STR ''n''))
     (lookup_context gcall_result bump_entry gcall_ctx_second)
   \<noteq> map_point_state (\<lambda>st. st (STR ''n''))
       (lookup_context gcall_result bump_entry gcall_ctx_third)"
  by eval+

subsection \<open>Returned values and the global's final value in the caller\<close>

text \<open>
  The caller runs under the single context \<open>[]\<close>. After each return the table
  shows the callee's global write surviving into the caller and the
  return-value assignment landing \<open>bump\<close>'s own returned value in the caller's
  variable.
\<close>

lemma gcall_result_after_first_return:
  "map_point_state (\<lambda>st. (st (STR ''g''), st (STR ''a'')))
     (lookup_context gcall_result (Statement 5) [])
   = Reachable (Ivl (Fin 15) (Fin 15), Ivl (Fin 15) (Fin 15))"
  by eval

lemma gcall_result_after_second_return:
  "map_point_state (\<lambda>st. (st (STR ''g''), st (STR ''b'')))
     (lookup_context gcall_result (Statement 8) [])
   = Reachable (Ivl (Fin 19) (Fin 19), Ivl (Fin 19) (Fin 19))"
  by eval

lemma gcall_result_after_third_return:
  "map_point_state (\<lambda>st. (st (STR ''g''), st (STR ''c'')))
     (lookup_context gcall_result (Statement 10) [])
   = Reachable (Ivl (Fin 38) (Fin 38), Ivl (Fin 38) (Fin 38))"
  by eval

subsection \<open>A covered context that is nonetheless unreachable\<close>

text \<open>
  \<^const>\<open>fact_prog\<close>'s \<open>n<2\<close> base-case branch is dead inside the \<open>n=3\<close>
  activation. The solver still covers that key, so this is not the absent-key
  case below: the table reports \<^const>\<open>Unreachable\<close> because the stored state
  concretizes to nothing.

  The same node is live in the innermost \<open>n=1\<close> activation, where the base
  case is the branch actually taken, so \<^const>\<open>node_live_ex\<close> reports the node
  live. That is precisely the resolution the per-context table adds over the
  per-node view: liveness of a node says nothing about liveness of a
  particular activation at it.
\<close>

definition fact_result :: "(ivl list, ivl abs_state) analysis_result" where
  "fact_result = analyse_interval_entry_state_result fact_prog"

lemma fact_result_dead_branch_covered:
  "(Statement 2, ctx_a) \<in> result_keys fact_result"
  by eval

lemma fact_result_dead_branch_not_reachable:
  "\<not> is_reachable_point (lookup_context fact_result (Statement 2) ctx_a)"
  by eval

lemma fact_result_dead_branch_unreachable:
  "lookup_context fact_result (Statement 2) ctx_a = Unreachable"
  using fact_result_dead_branch_not_reachable
  by (simp add: is_reachable_point_iff)

lemma fact_result_base_case_live_ctx:
  "map_point_state (\<lambda>st. st (STR ''n''))
     (lookup_context fact_result (Statement 2) ctx_a1)
   = Reachable (Ivl (Fin 1) (Fin 1))"
  by eval

lemma fact_result_dead_branch_node_live:
  "node_live_ex fact_result (Statement 2)"
  by eval

subsection \<open>A context the solver never covered\<close>

text \<open>
  A real node queried at a context no activation ever entered under. The
  membership guard in \<^const>\<open>lookup_context\<close> answers \<^const>\<open>Unreachable\<close>;
  no fallback to the seeded default context \<open>[]\<close> takes place, so the answer
  does not silently become some other activation's state.
\<close>

definition gcall_ctx_bogus :: "ivl list" where
  "gcall_ctx_bogus = [Ivl (Fin 77) (Fin 77)]"

lemma gcall_result_bogus_absent:
  "(bump_entry, gcall_ctx_bogus) \<notin> result_keys gcall_result"
  by eval

lemma gcall_result_bogus_unreachable:
  "lookup_context gcall_result bump_entry gcall_ctx_bogus = Unreachable"
  by (rule lookup_context_absent[OF gcall_result_bogus_absent])

text \<open>The default context \<open>[]\<close> is likewise uncovered at the callee entry, so
  it is not a hidden answer either.\<close>

lemma gcall_result_bump_default_ctx_absent:
  "(bump_entry, []) \<notin> result_keys gcall_result"
  by eval

subsection \<open>The joined per-node view\<close>

text \<open>
  \<^const>\<open>lookup_joined_state\<close> folds the domain's own join over exactly the
  three contexts above, so the callee entry's joined \<open>n\<close> spans the three
  entered arguments and its joined \<open>g\<close> spans the three global values the
  caller had written. This is checked against the join of the per-context
  states pinned above, which is the only reading the fold can have.
\<close>

lemma gcall_result_bump_joined:
  "map_point_state (\<lambda>st. (st (STR ''g''), st (STR ''n'')))
     (lookup_joined_state gcall_result bump_entry)
   = Reachable (Ivl (Fin 10) (Fin 19), Ivl (Fin 4) (Fin 19))"
  by eval

lemma gcall_result_bump_live:
  "node_live_ex gcall_result bump_entry"
  by eval

subsection \<open>Routing a call from the table alone\<close>

text \<open>
  \<^const>\<open>entry_state_callee_ctx\<close> recomputes a call's callee context from the
  caller's own \<^const>\<open>Reachable\<close> state, without reopening the solver's solution
  map. \<open>gcall_callee_ctx_at\<close> is the shape a consumer of the table uses: the
  \<^const>\<open>Unreachable\<close> case is decided first and answers \<^const>\<open>None\<close>, so no
  routing is attempted at a point no execution reaches, and the routing
  function itself never sees a reachability question.
\<close>

definition gcall_callee_ctx_at :: "pp \<Rightarrow> call_action \<Rightarrow> ivl list option" where
  "gcall_callee_ctx_at u ca =
     (case lookup_context gcall_result u [] of
        Unreachable \<Rightarrow> None
      | Reachable st \<Rightarrow> entry_state_callee_ctx gcall_gs ca st)"

abbreviation gcall_call_first :: call_action where
  "gcall_call_first \<equiv> CallEdge (compile_dst (prog_tyenv gcall_prog) (Some (STR ''a''))) [STR ''n'']
     (compile_actuals (prog_tyenv gcall_prog) [STR ''n''] [exp.N 5])"

abbreviation gcall_call_second :: call_action where
  "gcall_call_second \<equiv> CallEdge (compile_dst (prog_tyenv gcall_prog) (Some (STR ''b''))) [STR ''n'']
     (compile_actuals (prog_tyenv gcall_prog) [STR ''n''] [exp.N 4])"

abbreviation gcall_call_third :: call_action where
  "gcall_call_third \<equiv> CallEdge (compile_dst (prog_tyenv gcall_prog) (Some (STR ''c''))) [STR ''n'']
     (compile_actuals (prog_tyenv gcall_prog) [STR ''n''] [V (STR ''g'')])"

text \<open>Each call site's own context, pinned as a value.\<close>

lemma gcall_callee_ctx_at_values:
  "gcall_callee_ctx_at (Statement 4) gcall_call_first = Some [Ivl (Fin 5) (Fin 5)]"
  "gcall_callee_ctx_at (Statement 5) gcall_call_second = Some [Ivl (Fin 4) (Fin 4)]"
  "gcall_callee_ctx_at (Statement 9) gcall_call_third = Some [Ivl (Fin 19) (Fin 19)]"
  by eval+

text \<open>The same three contexts the solver routed with
  (\<^const>\<open>gcall_ctx_first\<close> and its siblings, each defined through
  \<^const>\<open>entry_state_route\<close> on the raw solved state), so an edge drawn from a
  recomputed context reaches the key the callee was actually materialized
  under.\<close>

lemma gcall_callee_ctx_at_agrees_with_route:
  "gcall_callee_ctx_at (Statement 4) gcall_call_first = Some gcall_ctx_first"
  "gcall_callee_ctx_at (Statement 5) gcall_call_second = Some gcall_ctx_second"
  "gcall_callee_ctx_at (Statement 9) gcall_call_third = Some gcall_ctx_third"
  by eval+

lemma gcall_callee_ctx_at_covered:
  "(bump_entry, the (gcall_callee_ctx_at (Statement 4) gcall_call_first)) \<in> result_keys gcall_result"
  "(bump_entry, the (gcall_callee_ctx_at (Statement 5) gcall_call_second)) \<in> result_keys gcall_result"
  "(bump_entry, the (gcall_callee_ctx_at (Statement 9) gcall_call_third)) \<in> result_keys gcall_result"
  by eval+

text \<open>No call site routes to another call site's context. This is the negative
  half: a renderer pairing call sites with callee contexts by position, or by
  picking any covered context at the callee, would draw
  \<open>call#1 -> bump/[19,19]\<close> and nothing above would notice.\<close>

lemma gcall_callee_ctx_at_no_cross:
  "gcall_callee_ctx_at (Statement 4) gcall_call_first \<noteq> Some gcall_ctx_second"
  "gcall_callee_ctx_at (Statement 4) gcall_call_first \<noteq> Some gcall_ctx_third"
  "gcall_callee_ctx_at (Statement 5) gcall_call_second \<noteq> Some gcall_ctx_third"
  by eval+

subsection \<open>Two call sites sharing one callee context\<close>

text \<open>
  Entry-state contexts key on what is passed, so two call sites passing the
  same argument share one callee context --- and legitimately so: one
  activation covers both, and there is nothing to keep apart. The consequence
  for anything reconstructing interprocedural edges is that a callee context
  does not identify a call site. Each call's continuation has to come from that
  call's own tuple; recovering it backwards from the callee key is ambiguous
  exactly here.
\<close>

definition twin_prog :: imp_prog where
  "twin_prog = program {
     void idf(n) {
       return n + 1
     }
     void main() {
       a := idf(5);
       b := idf(5);
       __voblint_check(a == 6);
       __voblint_check(b == 6)
     }
   }"

definition twin_result :: "(ivl list, ivl abs_state) analysis_result" where
  "twin_result = analyse_interval_entry_state_result twin_prog"

definition twin_call_contexts :: "(pp \<times> pp \<times> ivl list option) list" where
  "twin_call_contexts =
     map (\<lambda>(call, ca, entry, cont).
            (call, cont,
             case lookup_context twin_result call [] of
               Unreachable \<Rightarrow> None
             | Reachable st \<Rightarrow>
                 entry_state_callee_ctx (declared_global twin_prog) ca st))
       (cfg_calls_list (prog_cfg prog_main_name twin_prog))"

lemma twin_call_contexts_shared:
  "twin_call_contexts =
     [(Statement 2, Statement 3, Some [Ivl (Fin 5) (Fin 5)]),
      (Statement 3, Statement 4, Some [Ivl (Fin 5) (Fin 5)])]"
  by eval

text \<open>Stated separately so the shared half and the distinct half of the same
  table cannot drift apart: one callee context, two continuations.\<close>

lemma twin_call_contexts_one_context:
  "remdups (map (\<lambda>(_, _, c). c) twin_call_contexts) = [Some [Ivl (Fin 5) (Fin 5)]]"
  by eval

lemma twin_call_continuations_distinct:
  "map (\<lambda>(_, cont, _). cont) twin_call_contexts = [Statement 3, Statement 4]"
  by eval

text \<open>The callee is materialized once, under that one shared context, and the
  caller's own context stays the root one.\<close>

lemma twin_result_idf_contexts:
  "contexts_at twin_result (FunctionEntry (STR ''idf'')) = {[Ivl (Fin 5) (Fin 5)]}"
  by eval

lemma twin_analyse_interval_entry_state:
  "analyse_interval_entry_state twin_prog =
     [(Statement 4, elaborate_syn (prog_tyenv twin_prog) (exp.Eq (V (STR ''a'')) (exp.N 6)), Decided Check_Proved),
      (Statement 5, elaborate_syn (prog_tyenv twin_prog) (exp.Eq (V (STR ''b'')) (exp.N 6)), Decided Check_Proved)]"
  by eval

end
