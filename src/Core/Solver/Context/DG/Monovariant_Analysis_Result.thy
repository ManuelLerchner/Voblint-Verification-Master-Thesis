theory Monovariant_Analysis_Result
  imports
    "Voblint_Core.Analysis_Result"
    "Voblint_Core.CFG_Enumeration"
    "Voblint_Core.Abstract_Checks"
    "Voblint_CFG.Compile_Invariants"
    Exec_DG_Bridge
begin

section \<open>One executable constructor for every monovariant \<open>AnalysisResult\<close>\<close>

text \<open>
  Sign, Interval, and \<open>int_dom\<close> each solve at \<open>unit\<close> context under three
  update-rule disciplines (always-join, per-origin, and -- Interval and
  \<open>int_dom\<close> only -- Apinis warrowing), and every one of those nine solves
  builds its \<^type>\<open>analysis_result\<close> the same way: every node of the
  program's own CFG as the key domain, and \<^const>\<open>normalize_point\<close>
  applied (after \<^const>\<open>canonicalize_lift\<close>) to whatever local unknown the
  solve function reports there. Only which native D/G solve function
  produces that local-unknown lookup differs. \<open>monovariant_analysis_result_for\<close>
  below factors the shared half out once, so a concrete adapter
  (\<open>Sign_Checks\<close>, \<open>Interval_Checks\<close>, \<open>Int_Checks\<close>) is a
  one-line partial application, not a fifth (through ninth) copy of the
  same three-line \<^const>\<open>Analysis_Result\<close>/\<^const>\<open>normalize_point\<close> body.

  The key domain is \<^const>\<open>cfg_node_list\<close> of the program's own CFG, not
  the solver's finite covered-key set (\<open>fst sol\<close>): a monovariant analysis'
  context space is \<open>unit\<close>, and the CFG already statically enumerates every
  program point, so nothing about which points are queryable needs to come
  from solver support. A node the solver never touches -- dead code -- is
  still a key, and reads as \<^const>\<open>Unreachable\<close> through \<^const>\<open>normalize_point\<close>'s
  own structural \<^const>\<open>Bot\<close> case, not through key absence. This keeps
  \<open>monovariant_analysis_result_for\<close>'s public lookup semantics independent
  of the solver-support membership that a raw-env read (\<open>analyse_sign_env_for\<close>
  and its siblings) never tested either.

  No locale: \<open>solve\<close> is already an ordinary function parameter of one
  definition, not a fixed context threaded through several dependent
  constants, so plain lemmas about \<open>monovariant_analysis_result_for\<close> --
  universally quantified over \<open>solve\<close> the same way the definition itself
  is -- give every concrete adapter the same proof reuse a locale
  interpretation would, without qualified-name/interpretation machinery a
  reader of the generated OCaml would otherwise have to see through.
\<close>

definition monovariant_analysis_result_for ::
    "((vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
        (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> ('a::computable_domain exec_dg_st lifted, 'a exec_dg_st lifted) dg_state))
     \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, 'a abs_state) analysis_result" where
  "monovariant_analysis_result_for solve gs p =
     (let sol = solve gs p; gl = declared_global_vars p;
          g = prog_cfg prog_main_name p
      in Analysis_Result (set (map (\<lambda>v. (v, ())) (cfg_node_list g)))
           (\<lambda>v ctx. normalize_point gs
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"


text \<open>
  \<open>solve\<close> is applied exactly once, bound by the \<open>let\<close>, and each concrete
  adapter is a bare partial application of \<open>monovariant_analysis_result_for\<close>
  -- so no adapter needs its own \<open>[code del]\<close>/\<open>[code]\<close> single-solve rewrite
  the way \<open>analyse_sign_report_for\<close> and its siblings still do for their own,
  differently-shaped \<open>classify_checks\<close> bodies.

  \<^const>\<open>lookup_context\<close> gates on key membership itself (\<open>lookup_context_def\<close>:
  a key outside the result table answers \<^const>\<open>Unreachable\<close> regardless of
  what \<open>result_at\<close> would say there), so \<open>lookup_context_monovariant_analysis_result_for\<close>
  below states that same gate against the CFG-node key domain, not against
  the solver's own covered-key set -- a genuine CFG node always reads
  through to its \<open>normalize_point\<close>/\<open>canonicalize_lift\<close> answer, live or dead.
\<close>

lemma lookup_context_monovariant_analysis_result_for:
  "lookup_context (monovariant_analysis_result_for solve gs p) v ctx =
     (if v \<in> set (cfg_node_list (prog_cfg prog_main_name p))
      then normalize_point gs
             (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
               (locals (snd (solve gs p) (Inl (v, ctx)))))
      else Unreachable)"
  by (auto simp: monovariant_analysis_result_for_def lookup_context_def Let_def)

lemma contexts_at_monovariant_analysis_result_for:
  "contexts_at (monovariant_analysis_result_for solve gs p) v =
     (if v \<in> set (cfg_node_list (prog_cfg prog_main_name p)) then {()} else {})"
  by (auto simp: monovariant_analysis_result_for_def contexts_at_def Let_def)


section \<open>The surface a solved table publishes\<close>

text \<open>
  What every domain, at every solver discipline, ends up publishing about a whole program:
  the state its solved table holds at a point, and the check report read off that. Both are
  the same assembly every time --- only the table and the domain's own classifier differ ---
  so they are stated once here and instantiated, rather than rewritten per domain and per
  discipline.

  That repetition was not free. The four solver disciplines were propagated by hand as each
  was added, and the propagation thinned: the newest discipline reached fewer domains than
  the oldest, and a solved table with no wrapper published for it is invisible to every
  caller that reads the surface rather than the solver. An interpretation cannot be
  partially present, so a discipline that is interpreted has its whole surface, or none of
  it and a name that fails to resolve.

  \<^const>\<open>bot\<close> at an \<^const>\<open>Unreachable\<close> point is the reading every existing report function
  already makes: nothing reaches the point, so no store does, and \<^const>\<open>bot\<close> is the
  abstract state whose concretisation is empty.
\<close>

text \<open>
  \<open>bot_state\<close> is a parameter rather than the \<^class>\<open>order_bot\<close> class operation, and that is
  a code-generation requirement, not a stylistic choice. A sort constraint here would make
  the surface's code equation polymorphic in \<open>'a::order_bot\<close>, and generating code for it at
  an abstract state --- a function type \<^typ>\<open>String.literal \<Rightarrow> 'b\<close> --- would demand an
  executable \<^const>\<open>bot\<close> arity for that function type, which needs the domain to be
  \<^class>\<open>enum\<close>. \<^typ>\<open>String.literal\<close> is not. Taking the element as a parameter keeps the
  equation free of sorts; every interpretation still passes \<^const>\<open>bot\<close>, where the concrete
  instance is executable exactly as it was before.
\<close>

locale analysis_surface =
  fixes table :: "imp_prog \<Rightarrow> (unit, 'a) analysis_result"
    and bot_state :: 'a
    and classify :: "exp \<Rightarrow> 'a \<Rightarrow> check_result"
begin

definition state_at :: "imp_prog \<Rightarrow> pp \<Rightarrow> 'a" where
  "state_at p v =
     (case lookup_context (table p) v () of Unreachable \<Rightarrow> bot_state | Reachable st \<Rightarrow> st)"

definition report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "report p = classify_checks (prog_cfg prog_main_name p) (state_at p) classify"

end

text \<open>
  Unfolds the surface down to the \<^const>\<open>classify_checks\<close> term it stands for. A caller
  proving one of its own report names equal to the surface needs both equations, and
  \<^const>\<open>analysis_surface.state_at\<close> in \<open>abs_def\<close> form because \<^const>\<open>analysis_surface.report\<close>
  passes it partially applied while the definition states it fully applied.
\<close>

lemmas surface_unfold =
  analysis_surface.report_def analysis_surface.state_at_def [abs_def]

text \<open>
  A locale constant carries no code equation of its own, so every report reading through
  the surface would drop out of the generated code and out of \<open>by eval\<close> alike. Both
  defining equations are already in executable shape --- \<^const>\<open>classify_checks\<close> over a
  \<^const>\<open>lookup_context\<close> reading --- so declaring them is all the code generator needs.
\<close>

declare analysis_surface.state_at_def [code]
declare analysis_surface.report_def [code]


end

