theory Example_Sign_Base_Vs_Routed_Migration
  imports
    Voblint_Formalization.Sign_Exec_Ctx_Sound
    Voblint_CLI.State_Report_GraphViz
    Example_Analysis_Dispatch_Regression
begin

hide_const phase.N

text \<open>
  Scaffolding for the Base-to-routed-unit Sign migration: empirical parity
  evidence between Sign's production Base-family result
  (\<^const>\<open>analyse_sign_result\<close>/\<^const>\<open>analyse_sign_report\<close>,
  \<^theory>\<open>Voblint_Analysis.Sign_Checks\<close>) and the routed-unit-context result proved
  sound in \<^theory>\<open>Voblint_Formalization.Sign_Exec_Ctx_Sound\<close>
  (\<^const>\<open>analyse_sign_ctx_result\<close>). No equality theorem between the two
  producers is attempted here: both are independently sound, and the
  production solver family proves soundness only, never canonicity, so exact
  executable-result equality between them is not a reachable goal. This
  theory instead runs concrete \<open>by eval\<close> parity checks across the existing
  Sign regression corpus plus two new recursion/repeated-call-site programs,
  to gather migration evidence. Delete this theory once Base/unit is
  retired, after promoting anything interesting it found into permanent
  regressions.
\<close>

section \<open>A minimal, comparable check report for the routed-unit producer\<close>

text \<open>
  \<^const>\<open>analyse_sign_ctx_result_for\<close> only reaches the raw result table --
  \<open>Sign_Exec_Ctx_Sound.thy\<close>'s own comment flags this as a temporary,
  minimal adapter, with no check-report layer built on top. This mirrors
  \<^const>\<open>analyse_sign_report_for\<close> (\<open>Sign_Checks.thy\<close>) exactly, reading
  through \<^const>\<open>analyse_sign_ctx_result_for\<close> instead of
  \<^const>\<open>analyse_sign_result_for\<close>, so a verdict-level comparison is possible
  alongside the state-level one, without touching production \<open>Sign_Checks\<close>.
\<close>

definition analyse_sign_ctx_report_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_ctx_report_for gs mnm p =
     (let r = analyse_sign_ctx_result_for gs mnm p
      in classify_checks (prog_cfg mnm p)
           (\<lambda>v. case lookup_context r v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)
           sign_classify_check)"

definition analyse_sign_ctx_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_ctx_report p = analyse_sign_ctx_report_for (declared_global p) prog_main_name p"

section \<open>State-level classification machinery\<close>

datatype sign_parity_bucket =
  Bucket_Identical
| Bucket_Routed_More_Precise
| Bucket_Routed_Less_Precise
| Bucket_Incomparable
| Bucket_Both_Unreachable

text \<open>
  \<^typ>\<open>sign abs_state\<close>'s own \<open>\<le>\<close>/\<open>=\<close> quantify over all of \<^typ>\<open>vname\<close>
  (\<^theory>\<open>Voblint_Core.Analysis_Result\<close>'s own comment on why the per-node join
  is passed as an explicit function), so neither has an executable
  realization. Both Base's and routed-unit's transfer functions default
  every variable outside a program's own in-scope names to \<open>STop\<close>
  identically, so restricting the comparison to \<^const>\<open>program_vars\<close> is
  exact, not an approximation -- the same argument \<^const>\<open>program_vars\<close>'s own
  comment (\<^theory>\<open>Voblint_CLI.State_Report_GraphViz\<close>) makes for a
  non-relational domain's reachability probe: no variable outside that scope
  can ever differ between the two sides.
\<close>

definition state_le_on :: "vname list \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> bool" where
  "state_le_on vars f g = list_all (\<lambda>x. f x \<le> g x) vars"

definition state_eq_on :: "vname list \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> bool" where
  "state_eq_on vars f g = list_all (\<lambda>x. f x = g x) vars"

text \<open>Per-variable breakdown, for the \<open>Bucket_Incomparable\<close> case: only the
  variables where the two sides actually disagree.\<close>

definition per_var_diff ::
    "vname list \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> (vname \<times> sign \<times> sign) list" where
  "per_var_diff vars b r = filter (\<lambda>(x, bs, rs). bs \<noteq> rs) (map (\<lambda>x. (x, b x, r x)) vars)"

text \<open>
  \<open>Unreachable\<close> is \<^typ>\<open>'a point_state\<close>'s bottom (\<^theory>\<open>Voblint_Core.Analysis_Result\<close>),
  so a side that reports \<open>Unreachable\<close> where the other reports \<open>Reachable\<close> is
  the \<^emph>\<open>more\<close> precise side (it claims no execution reaches this point at all):
  \<open>base = Unreachable, routed = Reachable _\<close> is \<open>base < routed\<close>, i.e.
  \<open>Bucket_Routed_Less_Precise\<close>, matching the general \<open>Reachable\<close>/\<open>Reachable\<close>
  case below where a smaller abstract state is likewise the more precise one.
\<close>

definition classify_sign_point ::
  "vname list \<Rightarrow> sign abs_state point_state \<Rightarrow> sign abs_state point_state \<Rightarrow> sign_parity_bucket" where
  "classify_sign_point vars base routed =
     (case (base, routed) of
        (Unreachable, Unreachable) \<Rightarrow> Bucket_Both_Unreachable
      | (Unreachable, Reachable _) \<Rightarrow> Bucket_Routed_Less_Precise
      | (Reachable _, Unreachable) \<Rightarrow> Bucket_Routed_More_Precise
      | (Reachable b, Reachable r) \<Rightarrow>
          if state_eq_on vars b r then Bucket_Identical
          else if state_le_on vars r b then Bucket_Routed_More_Precise
          else if state_le_on vars b r then Bucket_Routed_Less_Precise
          else Bucket_Incomparable)"

definition sign_state_parity_report :: "imp_prog \<Rightarrow> (pp \<times> sign_parity_bucket) list" where
  "sign_state_parity_report p =
     (let vars = program_vars p;
          base = analyse_sign_result p;
          routed = analyse_sign_ctx_result p
      in map (\<lambda>v. (v, classify_sign_point vars (lookup_context base v ()) (lookup_context routed v ())))
             (cfg_node_list (prog_cfg prog_main_name p)))"

definition bucket_counts :: "sign_parity_bucket list \<Rightarrow> (sign_parity_bucket \<times> nat) list" where
  "bucket_counts bs =
     [(Bucket_Identical, length (filter ((=) Bucket_Identical) bs)),
      (Bucket_Routed_More_Precise, length (filter ((=) Bucket_Routed_More_Precise) bs)),
      (Bucket_Routed_Less_Precise, length (filter ((=) Bucket_Routed_Less_Precise) bs)),
      (Bucket_Incomparable, length (filter ((=) Bucket_Incomparable) bs)),
      (Bucket_Both_Unreachable, length (filter ((=) Bucket_Both_Unreachable) bs))]"

definition sign_state_parity_counts :: "imp_prog \<Rightarrow> (sign_parity_bucket \<times> nat) list" where
  "sign_state_parity_counts p = bucket_counts (map snd (sign_state_parity_report p))"

text \<open>Every point that landed in \<open>Bucket_Incomparable\<close>, with its per-variable
  breakdown, so a genuinely incomparable case is inspectable directly instead
  of only counted.\<close>

definition sign_state_incomparable_detail ::
    "imp_prog \<Rightarrow> (pp \<times> (vname \<times> sign \<times> sign) list) list" where
  "sign_state_incomparable_detail p =
     (let vars = program_vars p;
          base = analyse_sign_result p;
          routed = analyse_sign_ctx_result p
      in [(v, per_var_diff vars b r).
            v \<leftarrow> cfg_node_list (prog_cfg prog_main_name p),
            Reachable b \<leftarrow> [lookup_context base v ()],
            Reachable r \<leftarrow> [lookup_context routed v ()],
            classify_sign_point vars (Reachable b) (Reachable r) = Bucket_Incomparable])"

section \<open>Verdict-level classification\<close>

datatype verdict_parity_bucket = V_Same | V_Routed_More_Precise | V_Routed_Less_Precise | V_Flip

text \<open>
  \<open>V_Flip\<close> (\<open>Check_Proved\<close> on one side, \<open>Check_Refuted\<close> on the other) is not
  ordinary migration noise: on a fixture whose concrete result is fixed and
  decidable, at most one of \<open>Check_Proved\<close>/\<open>Check_Refuted\<close> can be sound, so a
  flip means one of the two producers is unsound there. See this theory's
  final section for the stop-condition check.
\<close>

definition classify_check_pair :: "check_result \<Rightarrow> check_result \<Rightarrow> verdict_parity_bucket" where
  "classify_check_pair base routed =
     (if base = routed then V_Same
      else if base = Check_Unknown then V_Routed_More_Precise
      else if routed = Check_Unknown then V_Routed_Less_Precise
      else V_Flip)"

definition sign_verdict_parity_report ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> check_result \<times> verdict_parity_bucket) list" where
  "sign_verdict_parity_report p =
     map (\<lambda>((v, c, rb), (_, _, rr)). (v, c, rb, rr, classify_check_pair rb rr))
       (zip (analyse_sign_report p) (analyse_sign_ctx_report p))"

text \<open>Sanity check that the zip above lines up check-for-check: both reports
  walk the identical compiled CFG (\<open>prog_cfg prog_main_name p\<close>) through the
  same \<^const>\<open>classify_checks\<close> traversal, differing only in which result table
  each reads its per-node state from, so their \<open>(pp, exp)\<close> projections must
  already agree pointwise -- this lemma is the executable witness of that,
  checked once per fixture below rather than assumed.\<close>

definition check_sites_agree :: "imp_prog \<Rightarrow> bool" where
  "check_sites_agree p =
     (map (\<lambda>(v, c, _). (v, c)) (analyse_sign_report p) =
      map (\<lambda>(v, c, _). (v, c)) (analyse_sign_ctx_report p))"

section \<open>Two new corpus fixtures: recursion and a repeated call site\<close>

text \<open>
  Sign has zero regression fixtures anywhere that exercise recursion or a
  procedure called from two call sites -- exactly the mechanism Base and
  routed-unit differ on (how callee-entry values thread through the
  equation system: one flow-sensitive local unknown revisited per predecessor
  vs. a keyed-seed slot per callee entry). \<open>sign_factorial_prog\<close> mirrors
  Interval's own recursive-factorial regression
  (\<open>tests/regression/03-procedures/precision/06-recursive_factorial_dead_branch_no_bottom_leak.vimp\<close>)
  at Sign's coarser granularity; Sign has no \<open>--context\<close> flag, so there is no
  CLI parameter to fix here, only the domain-level program shape.
\<close>

definition sign_factorial_prog :: imp_prog where
  "sign_factorial_prog =
     program {
       void factorial(n) {
         __voblint_check(0 < n);
         if (n < 2) {
           return 1
         } else {
           r := factorial(n - 1);
           __voblint_check(0 < r);
           return n * r
         }
       }
       void main() {
         a := factorial(3);
         b := factorial(4);
         __voblint_check(0 < a);
         __voblint_check(0 < b)
       }
     }"

text \<open>
  \<open>sign_two_call_sites_prog\<close> mirrors
  \<open>tests/regression/03-procedures/known-imprecision/01-two_call_sites_same_procedure.vimp\<close>:
  one non-recursive procedure, two call sites, isolating repeated-entry-node
  evaluation without recursion's added complexity.
\<close>

definition sign_two_call_sites_prog :: imp_prog where
  "sign_two_call_sites_prog =
     program {
       void square(n) {
         return n * n
       }
       void main() {
         a := square(3);
         b := square(4);
         __voblint_check(0 < a);
         __voblint_check(0 < b)
       }
     }"

section \<open>Comparisons\<close>

text \<open>
  Every fixture below is \<open>check_sites_agree\<close>, \<open>Bucket_Identical\<close> at every
  covered point (with one \<open>Bucket_Both_Unreachable\<close> for the dead-branch
  fixture's own dead node), and \<open>V_Same\<close> at every check -- Base and
  routed-unit agree exactly on this entire corpus, including both new
  recursion/repeated-call-site fixtures. This is a real finding, not an
  artifact of a weak comparison: both producers solve with the identical
  solver rule (\<^const>\<open>TD_side_always_join_Interp_solve\<close>, see
  \<^const>\<open>analyse_sign_for\<close> and \<^const>\<open>sctx_sol\<close>), so the difference between
  them is purely the equation-generation architecture
  (\<^const>\<open>dg_gen_of\<close>'s unkeyed generator vs. the routed keyed-seed generator
  \<^const>\<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close>), and on Sign's seven-element
  lattice that architectural difference never separates the two fixpoints on
  any case tried here -- including \<open>sign_two_call_sites_prog\<close>, whose
  Interval analogue (\<open>tests/regression/03-procedures/known-imprecision/01-two_call_sites_same_procedure.vimp\<close>)
  genuinely does lose precision at a repeated call site under Interval's
  infinite-height carrier and its warrowing solver. Sign's finite height and
  the shared always-join rule are exactly why no such gap shows up here.
\<close>

subsection \<open>\<open>dispatch_demo_prog\<close>\<close>

lemma dispatch_demo_check_sites_agree: "check_sites_agree dispatch_demo_prog"
  unfolding check_sites_agree_def by eval

lemma dispatch_demo_state_parity_counts:
  "sign_state_parity_counts dispatch_demo_prog =
     [(Bucket_Identical, 7), (Bucket_Routed_More_Precise, 0), (Bucket_Routed_Less_Precise, 0),
      (Bucket_Incomparable, 0), (Bucket_Both_Unreachable, 0)]"
  by eval

lemma dispatch_demo_verdict_parity:
  "sign_verdict_parity_report dispatch_demo_prog =
     [(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved, Check_Proved, V_Same),
      (Statement 3, Less (N 0) (V (STR ''y'')), Check_Refuted, Check_Refuted, V_Same)]"
  by eval

subsection \<open>\<open>proc_demo_prog\<close>\<close>

lemma proc_demo_check_sites_agree: "check_sites_agree proc_demo_prog"
  unfolding check_sites_agree_def by eval

lemma proc_demo_state_parity_counts:
  "sign_state_parity_counts proc_demo_prog =
     [(Bucket_Identical, 12), (Bucket_Routed_More_Precise, 0), (Bucket_Routed_Less_Precise, 0),
      (Bucket_Incomparable, 0), (Bucket_Both_Unreachable, 0)]"
  by eval

lemma proc_demo_verdict_parity:
  "sign_verdict_parity_report proc_demo_prog =
     [(Statement 5, Less (N 0) (V (STR ''total'')), Check_Proved, Check_Proved, V_Same),
      (Statement 6, Less (V (STR ''total'')) (N 100), Check_Unknown, Check_Unknown, V_Same)]"
  by eval

subsection \<open>\<open>dg_probe_prog\<close>\<close>

lemma dg_probe_check_sites_agree: "check_sites_agree dg_probe_prog"
  unfolding check_sites_agree_def by eval

lemma dg_probe_state_parity_counts:
  "sign_state_parity_counts dg_probe_prog =
     [(Bucket_Identical, 12), (Bucket_Routed_More_Precise, 0), (Bucket_Routed_Less_Precise, 0),
      (Bucket_Incomparable, 0), (Bucket_Both_Unreachable, 0)]"
  by eval

lemma dg_probe_verdict_parity:
  "sign_verdict_parity_report dg_probe_prog =
     [(Statement 5, Less (N 0) (V (STR ''x'')), Check_Proved, Check_Proved, V_Same),
      (Statement 6, Less (N 0) (V (STR ''g'')), Check_Proved, Check_Proved, V_Same),
      (Statement 7, Less (N 0) (V (STR ''y'')), Check_Proved, Check_Proved, V_Same)]"
  by eval

subsection \<open>\<open>global_initial_value_remains_in_summary_prog\<close>\<close>

lemma global_initial_value_remains_in_summary_check_sites_agree:
  "check_sites_agree global_initial_value_remains_in_summary_prog"
  unfolding check_sites_agree_def by eval

lemma global_initial_value_remains_in_summary_state_parity_counts:
  "sign_state_parity_counts global_initial_value_remains_in_summary_prog =
     [(Bucket_Identical, 5), (Bucket_Routed_More_Precise, 0), (Bucket_Routed_Less_Precise, 0),
      (Bucket_Incomparable, 0), (Bucket_Both_Unreachable, 0)]"
  by eval

lemma global_initial_value_remains_in_summary_verdict_parity:
  "sign_verdict_parity_report global_initial_value_remains_in_summary_prog =
     [(Statement 1, Less (N 0) (V (STR ''g'')), Check_Proved, Check_Proved, V_Same)]"
  by eval

subsection \<open>\<open>no_call_two_step_prog\<close>\<close>

lemma no_call_two_step_check_sites_agree: "check_sites_agree no_call_two_step_prog"
  unfolding check_sites_agree_def by eval

lemma no_call_two_step_state_parity_counts:
  "sign_state_parity_counts no_call_two_step_prog =
     [(Bucket_Identical, 6), (Bucket_Routed_More_Precise, 0), (Bucket_Routed_Less_Precise, 0),
      (Bucket_Incomparable, 0), (Bucket_Both_Unreachable, 0)]"
  by eval

lemma no_call_two_step_verdict_parity:
  "sign_verdict_parity_report no_call_two_step_prog =
     [(Statement 2, Less (N 0) (V (STR ''x'')), Check_Proved, Check_Proved, V_Same)]"
  by eval

subsection \<open>\<open>state_wiring_ex_prog\<close>\<close>

lemma state_wiring_ex_check_sites_agree: "check_sites_agree state_wiring_ex_prog"
  unfolding check_sites_agree_def by eval

lemma state_wiring_ex_state_parity_counts:
  "sign_state_parity_counts state_wiring_ex_prog =
     [(Bucket_Identical, 5), (Bucket_Routed_More_Precise, 0), (Bucket_Routed_Less_Precise, 0),
      (Bucket_Incomparable, 0), (Bucket_Both_Unreachable, 0)]"
  by eval

lemma state_wiring_ex_verdict_parity:
  "sign_verdict_parity_report state_wiring_ex_prog =
     [(Statement 1, Less (N 0) (V (STR ''x'')), Check_Proved, Check_Proved, V_Same)]"
  by eval

subsection \<open>\<open>state_wiring_ex_dead_prog\<close>\<close>

text \<open>The one \<open>Bucket_Both_Unreachable\<close> point anywhere in this corpus: the
  dead \<open>then\<close>-branch check node, unreachable on both sides for the same
  reason (\<open>x < 0\<close> is infeasible under \<open>SPos\<close>).\<close>

lemma state_wiring_ex_dead_check_sites_agree: "check_sites_agree state_wiring_ex_dead_prog"
  unfolding check_sites_agree_def by eval

lemma state_wiring_ex_dead_state_parity_counts:
  "sign_state_parity_counts state_wiring_ex_dead_prog =
     [(Bucket_Identical, 6), (Bucket_Routed_More_Precise, 0), (Bucket_Routed_Less_Precise, 0),
      (Bucket_Incomparable, 0), (Bucket_Both_Unreachable, 1)]"
  by eval

lemma state_wiring_ex_dead_verdict_parity:
  "sign_verdict_parity_report state_wiring_ex_dead_prog =
     [(Statement 2, Less (N 0) (V (STR ''x'')), Check_Proved, Check_Proved, V_Same)]"
  by eval

subsection \<open>\<open>sign_factorial_prog\<close> (new: recursion)\<close>

lemma sign_factorial_check_sites_agree: "check_sites_agree sign_factorial_prog"
  unfolding check_sites_agree_def by eval

lemma sign_factorial_state_parity_counts:
  "sign_state_parity_counts sign_factorial_prog =
     [(Bucket_Identical, 15), (Bucket_Routed_More_Precise, 0), (Bucket_Routed_Less_Precise, 0),
      (Bucket_Incomparable, 0), (Bucket_Both_Unreachable, 0)]"
  by eval

text \<open>The entry check \<open>0 < n\<close> stays \<open>Check_Unknown\<close> on both sides: Sign has
  no context-sensitivity feature at all (unlike Interval's entry-state/call-string
  variants), so the callee entry always joins over every call site's argument,
  here \<open>3\<close> and \<open>4\<close>, regardless of which equation-generation architecture
  solves it.\<close>

lemma sign_factorial_verdict_parity:
  "sign_verdict_parity_report sign_factorial_prog =
     [(Statement 0, Less (N 0) (V (STR ''n'')), Check_Unknown, Check_Unknown, V_Same),
      (Statement 4, Less (N 0) (V (STR ''r'')), Check_Proved, Check_Proved, V_Same),
      (Statement 9, Less (N 0) (V (STR ''a'')), Check_Proved, Check_Proved, V_Same),
      (Statement 10, Less (N 0) (V (STR ''b'')), Check_Proved, Check_Proved, V_Same)]"
  by eval

lemma sign_factorial_no_incomparable_points:
  "sign_state_incomparable_detail sign_factorial_prog = []"
  by eval

subsection \<open>\<open>sign_two_call_sites_prog\<close> (new: repeated call site)\<close>

lemma sign_two_call_sites_check_sites_agree: "check_sites_agree sign_two_call_sites_prog"
  unfolding check_sites_agree_def by eval

lemma sign_two_call_sites_state_parity_counts:
  "sign_state_parity_counts sign_two_call_sites_prog =
     [(Bucket_Identical, 10), (Bucket_Routed_More_Precise, 0), (Bucket_Routed_Less_Precise, 0),
      (Bucket_Incomparable, 0), (Bucket_Both_Unreachable, 0)]"
  by eval

lemma sign_two_call_sites_verdict_parity:
  "sign_verdict_parity_report sign_two_call_sites_prog =
     [(Statement 4, Less (N 0) (V (STR ''a'')), Check_Proved, Check_Proved, V_Same),
      (Statement 5, Less (N 0) (V (STR ''b'')), Check_Proved, Check_Proved, V_Same)]"
  by eval

lemma sign_two_call_sites_no_incomparable_points:
  "sign_state_incomparable_detail sign_two_call_sites_prog = []"
  by eval

end
