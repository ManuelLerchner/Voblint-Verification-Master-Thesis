section \<open>Compiler baseline: reachability of the current compiled CFG\<close>

theory Example_Compile_Baseline
  imports
    "Voblint_CFG.CFG_Prune"
    "Voblint_CFG.Compile_Invariants"
    "Voblint_CFG.Located_Exec"
    "Voblint_Core.CFG_Enumeration"
    "Voblint_VIMP.VIMP_Notation"
begin

text \<open>
  Executable diagnostics for the compiled CFG, recorded before any compiler change.  The
  structural successor relation \<^const>\<open>cfg_succ_rel\<close> is set-valued; \<open>succ_list\<close> is its
  list view, with one clause per source of that relation: INTRA, ENTRY, COMB_CALLER, and
  COMB_RESULT.
\<close>

subsection \<open>Executable structural successors\<close>

definition succ_list :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node list" where
  "succ_list g u =
     map (\<lambda>(s, a, v). v) (filter (\<lambda>(s, a, v). s = u) (cfg_intra_list g))
   @ concat
       (map (\<lambda>(c, ca, ce, k).
               (if c = u then [ce, k] else [])
             @ (case ce of
                  FunctionEntry q \<Rightarrow> (if u = FunctionResult q then [k] else [])
                | _ \<Rightarrow> []))
         (cfg_calls_list g))"

subsection \<open>Node inventory and forward reachability\<close>

text \<open>Every node mentioned by the graph, deduplicated: intra endpoints, call sites, callee
  entries, call continuations, and the graph entry.\<close>

definition all_nodes_list :: "cfg \<Rightarrow> cfg_node list" where
  "all_nodes_list g =
     remdups
       (concat (map (\<lambda>(u, a, v). [u, v]) (cfg_intra_list g))
      @ concat (map (\<lambda>(c, ca, ce, k). [c, ce, k]) (cfg_calls_list g))
      @ [cfg_entry g])"

text \<open>Roots for pruning: every procedure entry node in the graph, so that a procedure never
  called from \<open>main\<close> still counts as reachable rather than as compiler debris.\<close>

definition entry_roots :: "cfg \<Rightarrow> cfg_node list" where
  "entry_roots g =
     filter (\<lambda>v. case v of FunctionEntry q \<Rightarrow> True | _ \<Rightarrow> False) (all_nodes_list g)"

definition reach_step :: "cfg \<Rightarrow> cfg_node list \<Rightarrow> cfg_node list" where
  "reach_step g vs = remdups (vs @ concat (map (succ_list g) vs))"

text \<open>One round of \<open>reach_step\<close> adds at least one node until closure, so iterating as often
  as there are nodes saturates.\<close>

definition reach_from :: "cfg \<Rightarrow> cfg_node list \<Rightarrow> cfg_node list" where
  "reach_from g roots = (reach_step g ^^ length (all_nodes_list g)) roots"

definition reach_list :: "cfg \<Rightarrow> cfg_node list" where
  "reach_list g = reach_from g (entry_roots g)"

definition dead_list :: "cfg \<Rightarrow> cfg_node list" where
  "dead_list g = filter (\<lambda>v. v \<notin> set (reach_list g)) (all_nodes_list g)"

definition nop_edge_list :: "cfg \<Rightarrow> (cfg_node \<times> edge_action \<times> cfg_node) list" where
  "nop_edge_list g = filter (\<lambda>(u, a, v). a = EA_Nop) (cfg_intra_list g)"

subsection \<open>One-line report per program\<close>

text \<open>\<open>(nodes, dead nodes, intra edges, nop edges, call edges)\<close> --- the row recorded for each
  regression program, so a compiler change shows up as a diff of these numbers.\<close>

definition cfg_report :: "cfg \<Rightarrow> nat \<times> nat \<times> nat \<times> nat \<times> nat" where
  "cfg_report g =
     (length (all_nodes_list g), length (dead_list g), length (cfg_intra_list g),
      length (nop_edge_list g), length (cfg_calls_list g))"

subsection \<open>Uniform program builder\<close>

definition prog_cfg :: "imp_prog \<Rightarrow> cfg" where
  "prog_cfg P = compile_prog (prog_table P) (prog_procs P) ''main'' (prog_main P)"

subsection \<open>Programs 1--8: intraprocedural shapes\<close>

text \<open>Each shape is the body of \<open>f\<close>, with \<open>main\<close> reduced to a single call, so the \<open>main\<close>
  contribution to every row is constant and the differences isolate the shape.\<close>

definition p01_skip :: imp_prog where
  "p01_skip = program { void f() { skip } void main() { f() } }"

definition p02_assign :: imp_prog where
  "p02_assign = program { void f() { x := 1 } void main() { f() } }"

definition p03_return :: imp_prog where
  "p03_return = program { void f() { return 1 } void main() { f() } }"

definition p04_return_then_dead :: imp_prog where
  "p04_return_then_dead = program { void f() { return 1; x := 2 } void main() { f() } }"

definition p05_if_both_return :: imp_prog where
  "p05_if_both_return =
     program { void f() { if (x < 1) { return 1 } else { return 2 } } void main() { f() } }"

definition p06_if_one_returns :: imp_prog where
  "p06_if_one_returns =
     program { void f() { if (x < 1) { return 1 } else { y := 2 } } void main() { f() } }"

definition p07_while_body_returns :: imp_prog where
  "p07_while_body_returns =
     program { void f() { while (x < 1) { return 1 } } void main() { f() } }"

definition p08_nested_if :: imp_prog where
  "p08_nested_if =
     program { void f() { if (x < 1) { if (x < 0) { y := 1 } else { y := 2 } } else { y := 3 } }
               void main() { f() } }"

subsection \<open>Program 10: recursive factorial\<close>

definition factorial_program :: imp_prog where
  "factorial_program = program {

     void fac(n) {
       if (n < 2) {
         return 1
       } else {
         tmp := fac(n - 1);
         return n * tmp
       }
     }

     void main() {
       N := 8;
       r := fac(N)
     }
   }"

definition factorial_cfg :: cfg where
  "factorial_cfg =
     compile_prog
       (prog_table factorial_program)
       (prog_procs factorial_program)
       ''main''
       (prog_main factorial_program)"

subsection \<open>Programs 9, 11--14: interprocedural shapes\<close>

definition p09_one_call :: imp_prog where
  "p09_one_call = program { void g() { y := 1 } void main() { g() } }"

definition p11_nested_calls :: imp_prog where
  "p11_nested_calls =
     program { void h() { y := 1 } void g() { h() } void main() { g() } }"

definition p12_two_call_sites :: imp_prog where
  "p12_two_call_sites =
     program { void g() { y := 1 } void f() { g(); g() } void main() { f() } }"

definition p13_after_guaranteed_return :: imp_prog where
  "p13_after_guaranteed_return =
     program { void f() { if (x < 1) { return 1 } else { return 2 }; z := 9 }
               void main() { f() } }"

definition p14_main_only :: imp_prog where
  "p14_main_only = program { void main() { skip } }"

subsection \<open>Program 15: runtime-only residuals are not source programs\<close>

text \<open>\<^const>\<open>Restore\<close> and \<^const>\<open>Unwind\<close> cannot occur in a compiled program: the compiler
  input contract excludes them through \<^const>\<open>source_com\<close>.  The regression is the rejection
  itself, not a compiled graph.\<close>

lemma p15_restore_not_source: "\<not> source_com Restore"
  by simp

lemma p15_unwind_not_source: "\<not> source_com Unwind"
  by simp

lemma p15_restore_body_rejected:
  "~ wf_compile_input is_global \<Pi> ps mnm Restore"
  by (simp add: wf_compile_input_def wf_source_program_def)

lemma p15_unwind_body_rejected:
  "~ wf_compile_input is_global \<Pi> ps mnm Unwind"
  by (simp add: wf_compile_input_def wf_source_program_def)

subsection \<open>Recorded baseline\<close>

text \<open>Rows are \<open>(nodes, dead, intra, nops, calls)\<close>.  These are the numbers the
  continuation-passing compiler must be compared against; the \<open>dead\<close> column is the one the
  redesign is meant to drive to zero.\<close>

value "map cfg_report
  [prog_cfg p01_skip, prog_cfg p02_assign, prog_cfg p03_return,
   prog_cfg p04_return_then_dead, prog_cfg p05_if_both_return,
   prog_cfg p06_if_one_returns, prog_cfg p07_while_body_returns,
   prog_cfg p08_nested_if]"

value "map cfg_report
  [prog_cfg p09_one_call, factorial_cfg, prog_cfg p11_nested_calls,
   prog_cfg p12_two_call_sites, prog_cfg p13_after_guaranteed_return,
   prog_cfg p14_main_only]"

subsection \<open>Dead nodes, per program\<close>

value "map dead_list
  [prog_cfg p01_skip, prog_cfg p02_assign, prog_cfg p03_return,
   prog_cfg p04_return_then_dead, prog_cfg p05_if_both_return,
   prog_cfg p06_if_one_returns, prog_cfg p07_while_body_returns,
   prog_cfg p08_nested_if]"

value "map dead_list
  [prog_cfg p09_one_call, factorial_cfg, prog_cfg p11_nested_calls,
   prog_cfg p12_two_call_sites, prog_cfg p13_after_guaranteed_return,
   prog_cfg p14_main_only]"

subsection \<open>Observable action traces\<close>

text \<open>
  The old-versus-new comparison for a compiler change: run the compiled graph deterministically
  and record the labels crossed.  \<^const>\<open>cstep\<close> is an inductive relation, so this is its
  executable deterministic reading --- at most one intra edge is enabled at a node of a
  compiled program, guards being complementary --- and it is diagnostic code, not a proof
  device.

  A label is observable unless it is a bookkeeping \<^term>\<open>EA_Nop\<close>: two graphs agree
  observationally when they perform the same assignments, guards, calls and returns in the
  same order.
\<close>

datatype step_label =
    LIntra (step_action: edge_action)
  | LCall (step_call_proc: pname)
  | LRet (step_ret_proc: pname)

type_synonym exec_frame = "cfg_node \<times> vname option \<times> store"

definition enabled_intra ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> store \<Rightarrow> (edge_action \<times> cfg_node) option" where
  "enabled_intra g u s =
     (case filter (\<lambda>(a, v). edge_step a s \<noteq> None)
             (map (\<lambda>(x, a, v). (a, v))
               (filter (\<lambda>(x, a, v). x = u) (cfg_intra_list g))) of
        [] \<Rightarrow> None
      | av # _ \<Rightarrow> Some av)"

definition call_at ::
    "cfg \<Rightarrow> cfg_node \<Rightarrow> (call_action \<times> cfg_node \<times> cfg_node) option" where
  "call_at g u =
     (case map (\<lambda>(c, ca, ce, k). (ca, ce, k))
             (filter (\<lambda>(c, ca, ce, k). c = u) (cfg_calls_list g)) of
        [] \<Rightarrow> None
      | x # _ \<Rightarrow> Some x)"

text \<open>One step: a pending activation returns at its \<^term>\<open>FunctionResult\<close>, otherwise an
  enabled intra edge fires, otherwise a call edge pushes an activation.\<close>

definition step_exec ::
    "cfg \<Rightarrow> cfg_node \<times> store \<times> exec_frame list
        \<Rightarrow> (step_label \<times> (cfg_node \<times> store \<times> exec_frame list)) option" where
  "step_exec g cf =
     (case cf of (u, s, stk) \<Rightarrow>
        (case (u, stk) of
           (FunctionResult q, (cont, dst, caller) # rest) \<Rightarrow>
             Some (LRet q, (cont, combine_collect is_global dst caller s, rest))
         | _ \<Rightarrow>
             (case enabled_intra g u s of
                Some (a, v) \<Rightarrow>
                  (case edge_step a s of
                     Some s' \<Rightarrow> Some (LIntra a, (v, s', stk))
                   | None \<Rightarrow> None)
              | None \<Rightarrow>
                  (case call_at g u of
                     Some (ca, FunctionEntry q, k) \<Rightarrow>                      Some (LCall q,
                            (FunctionEntry q, call_enter is_global ca s,
                              (k, (case ca of CallEdge dst pars args \<Rightarrow> dst), s) # stk))
                   | _ \<Rightarrow> None))))"

fun run_labels ::
    "cfg \<Rightarrow> nat \<Rightarrow> cfg_node \<times> store \<times> exec_frame list \<Rightarrow> step_label list" where
  "run_labels g 0 cf = []"
| "run_labels g (Suc k) cf =
     (case step_exec g cf of
        None \<Rightarrow> []
      | Some (l, cf') \<Rightarrow> l # run_labels g k cf')"

definition observable :: "step_label list \<Rightarrow> step_label list" where
  "observable = filter (\<lambda>l. l \<noteq> LIntra EA_Nop)"

definition trace_from_entry :: "cfg \<Rightarrow> store \<Rightarrow> nat \<Rightarrow> step_label list" where
  "trace_from_entry g s bound = observable (run_labels g bound (cfg_entry g, s, []))"

subsection \<open>Recorded observable traces\<close>

definition zero_store :: store where
  "zero_store = (\<lambda>_. 0)"

value "trace_from_entry (prog_cfg p02_assign) zero_store 20"

value "trace_from_entry (prog_cfg p06_if_one_returns) zero_store 20"

value "trace_from_entry factorial_cfg zero_store 200"

subsection \<open>Factorial detail\<close>

value "all_nodes_list factorial_cfg"

value "dead_list factorial_cfg"

value "nop_edge_list factorial_cfg"

end
