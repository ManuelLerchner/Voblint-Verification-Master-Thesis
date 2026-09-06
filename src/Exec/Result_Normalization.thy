theory Result_Normalization
  imports
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.CFG_Enumeration"
    "Voblint_Framework.Check_Report"
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

  This is a normalization boundary, not a totalization one. Which program points
  a published result answers for is the solve's own covered key set; nothing here
  adds a point the solver never reached. A covered key whose stored value is
  \<^const>\<open>Bot\<close> stays a key and reports \<^const>\<open>Bot\<close>, so coverage and
  reachability are separate properties of a result.

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

section \<open>The globals beside a solved locals table\<close>

text \<open>
  Sign, Interval and \<open>int_dom\<close> each solve at \<open>unit\<close> context under three
  update-rule disciplines (always-join, per-origin, and -- Interval and
  \<open>int_dom\<close> only -- Apinis warrowing), and every one of those nine solves
  builds its \<^type>\<open>analysis_result\<close> the same way: the solve's own covered
  key set as the key domain, and \<^const>\<open>normalize_point\<close> applied (after
  \<^const>\<open>canonicalize_lift\<close>) to whatever local unknown the solve reports
  there. Only the native D/G solve function differs, and each adapter writes
  that three-line \<^const>\<open>Analysis_Result\<close> body itself over its own solve.
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

text \<open>
  Which keys a routed unit-context solve can write, taking the two constructors as
  arguments the way \<^const>\<open>routed_entry_seed_tree\<close> already does. Every domain declares its own
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
  already reads, and the globals beside it. \<open>solve\<close> is a parameter because which solver discipline produced the pair is
  an application-site choice, so each domain's instance is a partial application
  rather than another copy of this body.

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

end

