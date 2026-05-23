section \<open>Example: CFG collecting semantics at a concrete program\<close>

text \<open>\label{sec:example-cfg-collecting}\<close>

theory Example_CFG_Collecting_Equiv
  imports CFG_Collecting
begin

text \<open>
  Demonstrates the CFG collecting semantics on a concrete program.
  After ``\<open>x := 5; y := x + 1\<close>'' the exit pp of the compiled graph
  contains the store \<open>{x = 5, y = 6}\<close>.

  Since \<^const>\<open>cfg_collect\<close> is the spec the analyzer is sound against
  (see \<^const>\<open>runs_to\<close>), this doubles as a sanity check on the CFG
  construction + fixpoint.
\<close>

(* \<midarrow>\<midarrow> Program and stores \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

definition collecting_example_prog :: com where
  "collecting_example_prog =
     (''x'' ::= N 5) ;; (''y'' ::= Plus (V ''x'') (N 1))"

text \<open>\<^verbatim>\<open>x := 5;
y := x + 1\<close>\<close>

definition collecting_example_s0 :: store where
  "collecting_example_s0 = (\<lambda>_. 0)"

definition collecting_example_t :: store where
  "collecting_example_t = (collecting_example_s0(''x'' := 5))(''y'' := 6)"

text \<open>
  Compiled graph: PP0 \<open>--[x:=5]-->\<close> PP1 \<open>--[nop]-->\<close> PP2 \<open>--[y:=x+1]-->\<close> PP3 (exit).
\<close>

definition cfg where "cfg = to_cfg collecting_example_prog"
value cfg

subsection \<open>Exit-point collecting\<close>

text \<open>
  The exit point of \<^term>\<open>cfg\<close> contains \<^term>\<open>collecting_example_t\<close>.
  Stated against \<^const>\<open>runs_to\<close>, the source-level surface of CFG
  exit reachability.
\<close>

lemma collecting_example_runs_to:
  "runs_to collecting_example_prog collecting_example_s0 collecting_example_t"
proof -
  let ?s1 = "collecting_example_s0(''x'' := 5)"
  have step1: "(''x'' ::= N 5, collecting_example_s0) \<rightarrow>* (SKIP, ?s1)"
    by (auto intro: star.step)
  have step2: "(''y'' ::= Plus (V ''x'') (N 1), ?s1) \<rightarrow>* (SKIP, collecting_example_t)"
    unfolding collecting_example_t_def
    by (auto intro: star.step)
  have "(collecting_example_prog, collecting_example_s0) \<rightarrow>* (SKIP, collecting_example_t)"
    unfolding collecting_example_prog_def
    using seq_comp[OF step1 step2] .
  thus ?thesis by (rule small_step_runs_to)
qed

corollary collecting_example_in_cfg_collect:
  "collecting_example_t \<in> cfg_collect cfg {collecting_example_s0} (cfg_exit cfg)"
  using collecting_example_runs_to
  unfolding runs_to_def cfg_def .

end

