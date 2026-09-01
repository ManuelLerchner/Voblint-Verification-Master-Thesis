theory Monovariant_Analysis_Result
  imports
    "Voblint_Core.Analysis_Result"
    "Voblint_Core.CFG_Enumeration"
    "Voblint_Core.Check_Report"
    "Voblint_Compile.Compile_Invariants"
    Exec_DG_Generator
begin

section \<open>Normalizing a solved local unknown\<close>

text \<open>
  \<open>normalize_point\<close> is the sole entry point from the executable solver
  substrate into the result boundary: it relabels the local unknown exactly
  as the solver stores it (an \<^typ>\<open>'a resolved_st_q lifted\<close>) into a
  \<^typ>\<open>'a abs_state lifted\<close>, \<^const>\<open>Bot\<close> becoming \<^const>\<open>Bot\<close> and
  \<^const>\<open>Lifted\<close> becoming \<^const>\<open>Lifted\<close> of the projected state. It is a
  purely structural conversion with no bottom test of its own.

  Semantic deadness is normalized \<^emph>\<open>before\<close> this point, not here:
  \<^const>\<open>canonicalize_lift\<close> is the boundary that collapses a witness-bottom
  \<^const>\<open>Lifted\<close> payload to \<^const>\<open>Bot\<close>, and every public result adapter
  routes its raw solver value through \<open>canonicalize_lift\<close> first, so
  \<open>normalize_point\<close> itself never needs the declared globals as a list, nor
  \<^class>\<open>executable_domain\<close>'s executable witness-bottom test -- both were
  needed only for that test, which now lives one layer earlier.
\<close>

fun normalize_point ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('a::bot) resolved_st_q lifted \<Rightarrow> 'a abs_state lifted"
where
  "normalize_point gs Bot = Bot"
| "normalize_point gs (Lifted s) = Lifted (fun_of_resolved_st_q_for gs s)"

text \<open>
  \<open>normalize_point\<close> is exact for whatever the raw value already denotes,
  unconditionally: no premise on \<open>gs\<close>/declared globals is needed, since the
  conversion no longer inspects them to decide reachability, only to project
  the payload \<^const>\<open>fun_of_resolved_st_q_for\<close> already needs.
\<close>

lemma normalize_point_correct:
  "gamma_point (normalize_point gs s) =
     gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) s)"
  by (cases s) simp_all

text \<open>
  The other direction of the same relabeling, in the shape a consumer of a
  \<^const>\<open>Lifted\<close> point needs: the payload it hands out is literally the
  reader's image of the solved local unknown, so a fact proved about the raw
  lifted state transports to the normalized one without re-deciding
  reachability.
\<close>

lemma normalize_point_Reachable_map_lift:
  assumes "normalize_point gs s = Lifted st"
  shows "map_lift (fun_of_resolved_st_q_for gs) s = Lifted st"
  using assms by (cases s) auto

text \<open>
  The old, single-step reachability reading of a raw solver value (a
  \<^const>\<open>Bot\<close>, a witness-bottom \<^const>\<open>Lifted\<close>, and a live \<^const>\<open>Lifted\<close> all
  collapsed together) now factors into \<^const>\<open>canonicalize_lift\<close> followed by
  \<open>normalize_point\<close>. The lemmas below pin all three cases of that
  composition, with no premise on \<open>q\<close> beyond which case it is in: this is
  the exact old/new behavior-preservation fact, true for every raw value a
  solver could hand back, canonical or not.
\<close>

lemma normalize_point_canonicalize_lift_Bot:
  "normalize_point gs (canonicalize_lift empty_pred Bot) = Bot"
  by simp

lemma normalize_point_canonicalize_lift_Lifted_bot:
  assumes "empty_pred s"
  shows "normalize_point gs (canonicalize_lift empty_pred (Lifted s)) = Bot"
  using assms by simp

lemma normalize_point_canonicalize_lift_Lifted_live:
  assumes "\<not> empty_pred s"
  shows "normalize_point gs (canonicalize_lift empty_pred (Lifted s)) =
           Lifted (fun_of_resolved_st_q_for gs s)"
  using assms by simp

lemma normalize_point_canonicalize_lift_eq_old:
  "normalize_point gs (canonicalize_lift empty_pred q) =
     (case q of
        Bot \<Rightarrow> Bot
      | Lifted s \<Rightarrow> if empty_pred s then Bot
                    else Lifted (fun_of_resolved_st_q_for gs s))"
  by (cases q) simp_all

text \<open>
  The soundness-facing counterpart of \<open>normalize_point_canonicalize_lift_eq_old\<close>:
  canonicalizing before normalizing never shrinks what a raw solved value
  concretizes to, provided \<open>empty_pred\<close> only ever fires where the projected
  state genuinely is witness-bottom (\<open>bot_sound\<close>, exactly what
  \<open>resolved_st_q_is_bot_for_iff\<close> gives for \<open>resolved_st_q_is_bot_for gl\<close>).
  This is the one fact a report soundness proof needs to transport an
  existing raw-env node-soundness result across the
  \<^const>\<open>canonicalize_lift\<close>/\<open>normalize_point\<close> boundary: no premise here
  mentions solver support, so none of the three cases below needs one either.
\<close>

lemma gamma_point_normalize_point_canonicalize_lift:
  fixes q :: "'a::sound_domain resolved_st_q lifted"
  assumes bot_sound: "\<And>s. empty_pred s \<Longrightarrow> is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows "gamma_point (normalize_point gs (canonicalize_lift empty_pred q)) =
           gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) q)"
proof (cases q)
  case Bot
  then show ?thesis by simp
next
  case (Lifted s)
  show ?thesis
  proof (cases "empty_pred s")
    case True
    with bot_sound have "\<lbrakk>fun_of_resolved_st_q_for gs s\<rbrakk> = {}"
      using is_empty_state_gamma_state_empty by blast
    with Lifted True show ?thesis by simp
  next
    case False
    with Lifted show ?thesis by simp
  qed
qed

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
  still a key, and reads as \<^const>\<open>Bot\<close> through \<^const>\<open>normalize_point\<close>'s
  own structural \<^const>\<open>Bot\<close> case, not through key absence. This keeps
  \<open>monovariant_analysis_result_for\<close>'s public lookup semantics independent
  of solver-support membership, which a raw environment read never tested
  either.

  No locale: \<open>solve\<close> is already an ordinary function parameter of one
  definition, not a fixed context threaded through several dependent
  constants, so plain lemmas about \<open>monovariant_analysis_result_for\<close> --
  universally quantified over \<open>solve\<close> the same way the definition itself
  is -- give every concrete adapter the same proof reuse a locale
  interpretation would, without qualified-name/interpretation machinery a
  reader of the generated OCaml would otherwise have to see through.
\<close>

text \<open>
  The same solve's other half. A routed D/G system has two kinds of unknown, and
  \<^const>\<open>Analysis_Result\<close> keeps only the first: the local one at every
  \<open>Inl (v, ctx)\<close>. The global ones at \<open>Inr k\<close> are what an interprocedural
  analysis actually side-effects, and a result browser has nothing to show for them
  as long as this projection drops them.

  Which half of a global slot carries its payload depends on the key, and the two
  cannot be read uniformly. \<open>routed_cmb_g\<close> publishes the shared slot through
  \<open>publish_global\<close>, which writes \<^const>\<open>globs\<close>; it seeds a callee entry through
  \<open>side_effect\<close> with \<open>DG (enter_local \<dots>) bot\<close>, whose payload is in
  \<^const>\<open>locals\<close> and whose \<^const>\<open>globs\<close> half is \<^const>\<open>bot\<close> -- which is also how
  \<open>routed_extra_g\<close> reads it back. Reading \<^const>\<open>globs\<close> everywhere would report
  every seed as unreachable, and nothing would fail: the shared slot would still
  look right.

  So each key arrives with the projection its own writer used, rather than this
  constant guessing from the key's shape -- which it could not do anyway, being
  generic in \<open>'k\<close>.
\<close>

definition dg_globals_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> vname list
     \<Rightarrow> (pp \<times> 'c + 'k \<Rightarrow> ('a::executable_domain exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)
     \<Rightarrow> ('k \<times> String.literal
          \<times> (('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state \<Rightarrow> 'a exec_dg_st lifted)) list
     \<Rightarrow> (String.literal \<times> 'a abs_state lifted) list" where
  "dg_globals_for gs gl sigma keys =
     map (\<lambda>(k, label, payload).
            (label,
             normalize_point gs
               (canonicalize_lift (resolved_st_q_is_bot_for gl) (payload (sigma (Inr k))))))
         keys"

text \<open>Reading a key the solver never touched is \<^const>\<open>Bot\<close>, the same
  structural \<^const>\<open>Bot\<close> case a never-visited program point takes, so a caller can
  list every key the program could have without testing solver support first.\<close>

lemma length_dg_globals_for [simp]:
  "length (dg_globals_for gs gl sigma keys) = length keys"
  by (simp add: dg_globals_for_def)

lemma map_fst_dg_globals_for:
  "map fst (dg_globals_for gs gl sigma keys) = map (fst o snd) keys"
  by (simp add: dg_globals_for_def case_prod_beta comp_def)

text \<open>
  Which keys a routed unit-context solve can write, taking the two constructors as
  arguments the way \<^const>\<open>routed_extra_g\<close> already does. Every domain declares its own
  \<open>gk\<close>, but they agree on the shape the routed spine imposes --- a shared slot and one
  seed per callee entry --- so the enumeration is a fact about that spine, not about
  any domain, and does not need restating once per \<open>gk\<close>.

  \<^const>\<open>prog_main_name\<close> is included: \<open>main\<close> compiles through the same procedure
  wrapper as any other, and a procedure nothing calls simply reads
  \<^const>\<open>Bot\<close> rather than being absent.
\<close>

definition seed_global_keys ::
    "'k \<Rightarrow> (pp \<Rightarrow> 'c \<Rightarrow> 'k) \<Rightarrow> (pp \<Rightarrow> 'c list) \<Rightarrow> (pname \<Rightarrow> 'c \<Rightarrow> String.literal)
     \<Rightarrow> imp_prog \<Rightarrow> ('k \<times> String.literal \<times> (('d, 'd) dg_state \<Rightarrow> 'd)) list" where
  "seed_global_keys gk0 seed ctxs label p =
     (gk0, STR ''Global'', globs)
       # concat
           (map (\<lambda>f. map (\<lambda>c. (seed (FunctionEntry f) c, label f c, locals))
                         (ctxs (FunctionEntry f)))
                (prog_main_name # prog_procs p))"

text \<open>
  At the unit context every entry has exactly one seed, so the context list is a
  constant and the label is the procedure name alone. A context-sensitive caller
  passes \<open>result_contexts_at\<close> instead, which enumerates a solved table's own
  covered contexts without needing an order on the context type.
\<close>

definition unit_seed_global_keys ::
    "'k \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'k) \<Rightarrow> imp_prog
     \<Rightarrow> ('k \<times> String.literal \<times> (('d, 'd) dg_state \<Rightarrow> 'd)) list" where
  "unit_seed_global_keys gk0 seed =
     seed_global_keys gk0 seed (\<lambda>_. [()]) (\<lambda>f _. STR ''enter '' + f)"

text \<open>
  Both halves of one routed unit-context solve: the locals table every check report
  already reads, and the globals beside it. \<open>solve\<close> is a parameter for the same reason
  it is one in \<open>monovariant_analysis_result_for\<close> below --- which solver discipline
  produced the pair is an application-site choice, so each domain's instance is a
  partial application rather than another copy of this body.

  Binding \<open>sol\<close> once is what keeps a report that shows both halves from solving twice.
\<close>

definition ctx_solved_for ::
    "((vname \<Rightarrow> bool) \<Rightarrow> imp_prog
        \<Rightarrow> (pp \<times> unit) set
             \<times> (pp \<times> unit + 'k
                  \<Rightarrow> ('a::executable_domain exec_dg_st lifted, 'a exec_dg_st lifted) dg_state))
     \<Rightarrow> (imp_prog
          \<Rightarrow> ('k \<times> String.literal
                \<times> (('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state
                     \<Rightarrow> 'a exec_dg_st lifted)) list)
     \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, 'a abs_state) analysis_result
          \<times> (String.literal \<times> 'a abs_state lifted) list" where
  "ctx_solved_for solve keys gs p =
     (let sol = solve gs p; gl = declared_global_vars p
      in (Analysis_Result (fst sol)
            (\<lambda>v ctx. normalize_point gs
                       (canonicalize_lift (resolved_st_q_is_bot_for gl)
                         (locals (snd sol (Inl (v, ctx)))))),
          dg_globals_for gs gl (snd sol) (keys p)))"

text \<open>The locals half is exactly what every domain's own result constructor builds from
  the same solve, so publishing the globals beside it adds a column and changes no
  verdict. Each domain's \<open>fst_\<close> corollary is this equation at its own solver.\<close>

lemma fst_ctx_solved_for:
  "fst (ctx_solved_for solve keys gs p)
     = (let sol = solve gs p
        in Analysis_Result (fst sol)
             (\<lambda>v ctx. normalize_point gs
                        (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                          (locals (snd sol (Inl (v, ctx)))))))"
  by (simp add: ctx_solved_for_def Let_def)

definition monovariant_analysis_result_for ::
    "((vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow>
        (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> ('a::executable_domain exec_dg_st lifted, 'a exec_dg_st lifted) dg_state))
     \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (unit, 'a abs_state) analysis_result" where
  "monovariant_analysis_result_for solve gs p =
     (let sol = solve gs p; gl = declared_global_vars p;
          g = prog_cfg p
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
  a key outside the result table answers \<^const>\<open>Bot\<close> regardless of
  what \<open>result_at\<close> would say there), so \<open>lookup_context_monovariant_analysis_result_for\<close>
  below states that same gate against the CFG-node key domain, not against
  the solver's own covered-key set -- a genuine CFG node always reads
  through to its \<open>normalize_point\<close>/\<open>canonicalize_lift\<close> answer, live or dead.
\<close>

lemma lookup_context_monovariant_analysis_result_for:
  "lookup_context (monovariant_analysis_result_for solve gs p) v ctx =
     (if v \<in> set (cfg_node_list (prog_cfg p))
      then normalize_point gs
             (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
               (locals (snd (solve gs p) (Inl (v, ctx)))))
      else Bot)"
  by (auto simp: monovariant_analysis_result_for_def lookup_context_def Let_def)

lemma contexts_at_monovariant_analysis_result_for:
  "contexts_at (monovariant_analysis_result_for solve gs p) v =
     (if v \<in> set (cfg_node_list (prog_cfg p)) then {()} else {})"
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

  \<^const>\<open>bot\<close> at an \<^const>\<open>Bot\<close> point is the reading every existing report function
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
     (case lookup_context (table p) v () of Bot \<Rightarrow> bot_state | Lifted st \<Rightarrow> st)"

definition report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "report p = classify_checks (prog_cfg p) (state_at p) classify"

text \<open>
  The same table read with its reachability kept: \<open>True\<close> marks a node the solve never
  covered, which a report consumer suppresses instead of printing the bottom state's
  vacuous verdict. Exact for the same reason \<^const>\<open>state_at\<close> is -- it is the
  \<^const>\<open>lookup_context\<close> case split itself, not a second test on the raw unknown.
\<close>

definition reach_state_at :: "imp_prog \<Rightarrow> pp \<Rightarrow> bool \<times> 'a" where
  "reach_state_at p v =
     (case lookup_context (table p) v () of Bot \<Rightarrow> (True, bot_state) | Lifted st \<Rightarrow> (False, st))"

definition report_with_state :: "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> 'a) list" where
  "report_with_state p =
     classify_checks_with_state (prog_cfg p) (reach_state_at p)
       (\<lambda>c (_, s). classify c s)"

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
declare analysis_surface.reach_state_at_def [code]
declare analysis_surface.report_with_state_def [code]


end

