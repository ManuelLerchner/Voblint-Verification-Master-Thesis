theory DG_Result_Construction
  imports
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.CFG_Enumeration"
    "Voblint_Framework.Check_Report"
    "Voblint_Framework.Seed_Global_Keys"
    "Voblint_Compile.Compile_Invariants"
    "Voblint_Exec.Exec_Result_Readback"
    "Voblint_Exec.Exec_DG_State"
    "Voblint_Exec.Exec_St_Reachability"
begin

section \<open>The globals beside a solved locals table\<close>

text \<open>
  Sign, Interval and \<open>int_dom\<close> each solve at \<open>unit\<close> context under three
  update-rule disciplines (always-join, per-origin, and -- Interval and
  \<open>int_dom\<close> only -- Apinis warrowing), and every one of those nine solves
  builds its \<^type>\<open>analysis_result\<close> the same way: the solve's own covered
  key set as the key domain, and \<^const>\<open>readback_result_value\<close> applied (after
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
             readback_result_value gs
               (canonicalize_lift (resolved_st_q_is_bot_for gl) (payload (sigma (Inr k))))))
         keys"
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
            (\<lambda>v ctx. readback_result_value gs
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
             (\<lambda>v ctx. readback_result_value gs
                        (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                          (locals (snd sol (Inl (v, ctx)))))))"
  by (simp add: ctx_solved_for_def Let_def)
end
