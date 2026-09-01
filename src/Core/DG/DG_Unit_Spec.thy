theory DG_Unit_Spec
  imports DG_Framework
begin

section \<open>The homogeneous unit analysis\<close>

text \<open>
  The unit instantiation of the D/G framework: an analysis that chooses
  \<open>D = G = 'a abs_state\<close>, so every Answer and every Side publication live
  in the same domain. Each step merges the local Answer with the shared
  Side fact, applies the ordinary transfer, then publishes the global
  restriction and returns the local restriction. \<open>unit_dg_spec_for\<close>
  packages an ordinary \<open>domain_transfer\<close> this way as a \<open>dg_spec\<close>;
  \<open>unit_combine_step_env_for\<close>/\<open>unit_combine_step_assign_for\<close> are its
  call-combine half, splitting a call's env-merge from its return-value
  assignment so the merge matches \<^const>\<open>combine_collect_abs\<close> once
  composed. A dead-code-aware variant is not a sibling construction: it is
  the generic reachability lifter applied to \<open>unit_dg_spec_for\<close>.
\<close>

text \<open>The unit env-merge/assign split (defined below as \<open>unit_combine_step_env_for\<close>/
  \<open>unit_combine_step_assign_for\<close>) computes the structural local/global
  merge and packages it the same way \<^const>\<open>unit_step_for\<close> packages every
  other edge, but writes no return value yet; the assign step reconstitutes
  the full state from that packaging, writes the callee-exit's return slot,
  and re-splits -- matching \<^const>\<open>combine_collect_abs\<close> exactly once
  composed.\<close>
definition unit_combine_step_assign_for ::
  "(vname => bool) =>
   call_info => 'a::bounded_semilattice_sup_bot abs_state
   => 'a abs_state => 'a abs_state \<times> 'a abs_state
   => 'a abs_state \<times> 'a abs_state"
where
  "unit_combine_step_assign_for gs ci de g merged =
     (let res = combine_assign (ci_dst ci) (de ret_var)
         (fst merged \<squnion> snd merged)
      in (restrict_global_for gs res, restrict_local_for gs res))"


definition unit_combine_step_env_for ::
  "(vname => bool) => call_info =>
   'a::bounded_semilattice_sup_bot abs_state => 'a abs_state
   => 'a abs_state => 'a abs_state \<times> 'a abs_state" where
  "unit_combine_step_env_for gs ci dc de g =
     (let m = combine_env gs dc g
      in (restrict_global_for gs m, restrict_local_for gs m))"

text \<open>
  The two halves of the environment merge rejoin to the merge itself, so a
  consumer that only needs \<^const>\<open>dgs_combine_assign\<close>'s \<open>fst \<squnion> snd\<close> argument
  never has to reason about the split.  \<^const>\<open>unit_combine_step_assign_for\<close> is
  monotone in exactly that argument and in the callee exit, so an analysis that
  replaces \<^const>\<open>dgs_combine_env\<close> by any merge above this one inherits
  soundness from this one instead of re-proving the return assignment.
\<close>

lemma unit_combine_step_env_for_join:
  "fst (unit_combine_step_env_for gs ci dc de g)
     \<squnion> snd (unit_combine_step_env_for gs ci dc de g)
   = combine_env gs dc g"
  unfolding unit_combine_step_env_for_def
  by (simp add: Let_def)

lemma unit_combine_step_assign_for_mono:
  fixes de1 de2 :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes de: "de1 \<le> de2"
    and m: "fst m1 \<squnion> snd m1 \<le> fst m2 \<squnion> snd m2"
  shows "fst (unit_combine_step_assign_for gs ci de1 g m1)
           \<le> fst (unit_combine_step_assign_for gs ci de2 g m2)"
    and "snd (unit_combine_step_assign_for gs ci de1 g m1)
           \<le> snd (unit_combine_step_assign_for gs ci de2 g m2)"
proof -
  have res: "combine_assign (ci_dst ci) (de1 ret_var) (fst m1 \<squnion> snd m1)
               \<le> combine_assign (ci_dst ci) (de2 ret_var) (fst m2 \<squnion> snd m2)"
    by (rule combine_assign_mono[OF le_funD[OF de] m])
  show "fst (unit_combine_step_assign_for gs ci de1 g m1)
          \<le> fst (unit_combine_step_assign_for gs ci de2 g m2)"
    unfolding unit_combine_step_assign_for_def Let_def fst_conv
    by (rule restrict_global_for_mono[OF res])
  show "snd (unit_combine_step_assign_for gs ci de1 g m1)
          \<le> snd (unit_combine_step_assign_for gs ci de2 g m2)"
    unfolding unit_combine_step_assign_for_def Let_def snd_conv
    by (rule restrict_local_for_mono[OF res])
qed

subsection \<open>The complete unit D/G specification\<close>

definition unit_dg_spec_for ::
  "(vname => bool) => 'a::sound_domain domain_transfer
   => ('a abs_state, 'a abs_state) dg_spec"
where
  "unit_dg_spec_for gs tf = \<lparr>
    dgs_skip       = unit_step_for gs (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_for gs (apply_tf tf (EA_Assign x e))),
    dgs_special    = (\<lambda>sc x. unit_step_for gs (apply_tf tf (EA_Special sc x))),
    dgs_branch     = (\<lambda>b pol. unit_step_for gs (branch\<^sup># tf b pol)),
    dgs_body       = (\<lambda>p. unit_step_for gs (body\<^sup># tf p)),
    dgs_return     = (\<lambda>e p. unit_step_for gs (return\<^sup># tf e p)),
    dgs_enter      = (\<lambda>ci. unit_step_for gs (snd o enter\<^sup># tf ci)),
    dgs_event      = (\<lambda>ev. unit_step_for gs (event\<^sup># tf ev)),
    dgs_caller_cont    = (\<lambda>_ d _. d),
    dgs_combine_env    = unit_combine_step_env_for gs,
    dgs_combine_assign = unit_combine_step_assign_for gs
  \<rparr>"

text \<open>Unlike the plain collecting semantics' \<^const>\<open>combine_collect_abs\<close>, the
  D/G-split combine cannot read the return value and the global effects from the
  same argument: the return slot is a local name owned by the callee's exit
  state \<open>de\<close>, while every global name is owned by the freshly-queried \<open>g\<close>, not
  by \<open>de\<close>'s own (locally-restricted) copy of it. \<^const>\<open>combine_env\<close> still
  supplies the ownership routing for the non-return names; \<open>de ret_var\<close> is
  read directly instead of routing it through that same combine.\<close>
lemma dgs_combine_unit_dg_spec_for:
  "dgs_combine (unit_dg_spec_for gs tf) ci dcont de g =
     (let res = combine_assign (ci_dst ci) (de ret_var) (combine_env gs dcont g)
      in (restrict_global_for gs res, restrict_local_for gs res))"
  unfolding dgs_combine_def unit_dg_spec_for_def
    unit_combine_step_assign_for_def Let_def
  by (simp add: unit_combine_step_env_for_join)

lemma dg_spec_step_unit_for:
  "dg_spec_step (unit_dg_spec_for gs tf) a = unit_step_for gs (apply_tf tf a)"
  unfolding unit_dg_spec_for_def
  by (cases a) simp_all

lemma dgs_enter_unit_dg_spec_for:
  "dgs_enter (unit_dg_spec_for gs tf) ci =
     unit_step_for gs (snd o enter\<^sup># tf ci)"
  unfolding unit_dg_spec_for_def
  by simp

end
