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
  composed. The \<open>_lifted\<close> siblings of every construction here repeat it
  over \<open>'a abs_state lifted\<close> for the dead-code carrier.
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

subsection \<open>The lifted combine split, alongside \<^const>\<open>unit_combine_step_env_for\<close>/\<^const>\<open>unit_combine_step_assign_for\<close>\<close>

text \<open>
  The two combine stages have different reachability disciplines. \<^const>\<open>unit_combine_step_env_for\<close>
  applies no domain transfer at all -- its body never reads \<open>de\<close> -- so it is pure
  structure-preserving reconstruction/projection: \<open>assemble_env_abs\<close> preserves whatever
  \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> status \<open>d\<close>/\<open>g\<close> already carry, with no \<open>empty_pred\<close> parameter, matching
  \<^const>\<open>unit_step_for_lifted\<close>'s own env-only case (\<open>unit_step_for_lifted_global_bot\<close>).

  \<^const>\<open>unit_combine_step_assign_for\<close> is where the callee-exit's reachability actually matters:
  it reads \<open>de ret_var\<close> directly. The soundness obligation this approximates
  (\<open>combine_sound\<close> in the \<open>sound_dg_spec\<close> locale: \<open>s \<in> gammaDG dc g \<Longrightarrow> t \<in> gammaDG de g \<Longrightarrow>
  combine_collect gs dst s t \<in> ...\<close>) is conditioned on \<open>t \<in> gammaDG de g\<close>; when that set is
  empty (an unreachable callee exit) the obligation is vacuous and \<^const>\<open>Bot\<close> is the tightest
  sound choice -- independent of whether the caller side is itself reachable. \<^const>\<open>transfer_lift2\<close>
  already has exactly this dominance (\<^const>\<open>Bot\<close> in either argument propagates), so no bespoke
  ternary combinator is needed here: reconstruct \<open>de\<close> against the env stage's rejoined output
  (\<open>fst merged \<squnion> snd merged\<close>, itself \<^const>\<open>Bot\<close>-preserving since both halves come from the same
  \<^const>\<open>map_lift\<close>-derived source), then transfer and normalize once via \<^const>\<open>transfer_lift2\<close>.

  \<^const>\<open>dg_combine_tree\<close> calls the two stages composed as a single \<open>comb\<close> application
  (\<^const>\<open>dgs_combine\<close>) and only ever observes that composed result -- the env stage's
  intermediate pair is never independently published -- so it is safe for the env stage to
  ignore \<open>de\<close>'s reachability entirely: it is enforced once, at the assign stage, the only place
  that actually consumes the callee exit.
\<close>

definition unit_combine_step_env_for_lifted ::
  "(vname => bool) => call_info
   => 'a::bounded_semilattice_sup_bot abs_state lifted => 'a abs_state lifted
   => 'a abs_state lifted \<times> 'a abs_state lifted"
where
  "unit_combine_step_env_for_lifted gs ci d g =
     (let m = assemble_env_abs gs d g
      in (map_lift (restrict_global_for gs) m, map_lift (restrict_local_for gs) m))"

lemma unit_combine_step_env_for_lifted_Bot_dominates_local [simp]:
  "unit_combine_step_env_for_lifted gs ci Bot g = (Bot, Bot)"
  unfolding unit_combine_step_env_for_lifted_def by simp

lemma unit_combine_step_env_for_lifted_global_bot:
  "unit_combine_step_env_for_lifted gs ci (Lifted d) Bot =
     (Lifted (restrict_global_for gs (combine_env gs d bot)),
      Lifted (restrict_local_for gs (combine_env gs d bot)))"
  unfolding unit_combine_step_env_for_lifted_def by simp

lemma unit_combine_step_env_for_lifted_agrees:
  "unit_combine_step_env_for_lifted gs ci (Lifted d) (Lifted g) =
     (Lifted (fst (unit_combine_step_env_for gs ci d de g)),
      Lifted (snd (unit_combine_step_env_for gs ci d de g)))"
  unfolding unit_combine_step_env_for_lifted_def unit_combine_step_env_for_def
  by (simp add: Let_def)

definition unit_combine_step_assign_for_lifted ::
  "(vname => bool)
   => call_info
   => ('a::bounded_semilattice_sup_bot abs_state => bool)
   => 'a abs_state lifted
   => 'a abs_state lifted \<times> 'a abs_state lifted
   => 'a abs_state lifted \<times> 'a abs_state lifted"
where
  "unit_combine_step_assign_for_lifted gs ci empty_pred de merged =
     (let joined = fst merged \<squnion> snd merged;
          res = transfer_lift2 empty_pred
                  (\<lambda>de0 env0. combine_assign (ci_dst ci) (de0 ret_var) env0) de joined
      in (map_lift (restrict_global_for gs) res, map_lift (restrict_local_for gs) res))"

lemma unit_combine_step_assign_for_lifted_de_bot [simp]:
  "unit_combine_step_assign_for_lifted gs ci empty_pred Bot merged = (Bot, Bot)"
  unfolding unit_combine_step_assign_for_lifted_def by simp

lemma unit_combine_step_assign_for_lifted_merged_bot [simp]:
  "unit_combine_step_assign_for_lifted gs ci empty_pred (Lifted de0) (Bot, Bot) = (Bot, Bot)"
  unfolding unit_combine_step_assign_for_lifted_def by simp

lemma unit_combine_step_assign_for_lifted_agrees:
  assumes "\<not> empty_pred (combine_assign (ci_dst ci) (de0 ret_var) (env0a \<squnion> env0b))"
  shows "unit_combine_step_assign_for_lifted gs ci empty_pred (Lifted de0) (Lifted env0a, Lifted env0b) =
           (Lifted (fst (unit_combine_step_assign_for gs ci de0 g (env0a, env0b))),
            Lifted (snd (unit_combine_step_assign_for gs ci de0 g (env0a, env0b))))"
  using assms
  unfolding unit_combine_step_assign_for_lifted_def unit_combine_step_assign_for_def
  by (simp add: Let_def)

lemma unit_combine_step_assign_for_lifted_collapses_bot:
  assumes "empty_pred (combine_assign (ci_dst ci) (de0 ret_var) (env0a \<squnion> env0b))"
  shows "unit_combine_step_assign_for_lifted gs ci empty_pred (Lifted de0) (Lifted env0a, Lifted env0b) = (Bot, Bot)"
  using assms
  unfolding unit_combine_step_assign_for_lifted_def
  by simp

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

subsection \<open>The complete lifted D/G specification, alongside \<^const>\<open>unit_dg_spec_for\<close>\<close>

text \<open>
  Assembles the three independently-validated lifted primitives into one \<^type>\<open>dg_spec\<close>
  record, additive so no existing consumer of \<^const>\<open>unit_dg_spec_for\<close> is affected.
  \<^const>\<open>dgs_combine_env\<close>/\<^const>\<open>dgs_combine_assign\<close> both formally take a \<open>de\<close>/\<open>g\<close> argument the
  record shape requires (\<^const>\<open>dgs_combine\<close> threads all four positionally); the env field
  drops \<open>de\<close> and the assign field drops \<open>g\<close>, exactly mirroring which parameters
  \<^const>\<open>unit_combine_step_env_for\<close>/\<^const>\<open>unit_combine_step_assign_for\<close> themselves leave unused.
\<close>

definition unit_dg_spec_for_lifted ::
  "(vname => bool)
   => ('a::sound_domain abs_state => bool)
   => 'a domain_transfer
   => ('a abs_state lifted, 'a abs_state lifted) dg_spec"
where
  "unit_dg_spec_for_lifted gs empty_pred tf = \<lparr>
    dgs_skip       = unit_step_for_lifted gs empty_pred (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. unit_step_for_lifted gs empty_pred (apply_tf tf (EA_Assign x e))),
    dgs_special    = (\<lambda>sc x. unit_step_for_lifted gs empty_pred (apply_tf tf (EA_Special sc x))),
    dgs_branch     = (\<lambda>b pol. unit_step_for_lifted gs empty_pred (branch\<^sup># tf b pol)),
    dgs_body       = (\<lambda>p. unit_step_for_lifted gs empty_pred (body\<^sup># tf p)),
    dgs_return     = (\<lambda>e p. unit_step_for_lifted gs empty_pred (return\<^sup># tf e p)),
    dgs_enter      = (\<lambda>ci. unit_step_for_lifted gs empty_pred (snd o enter\<^sup># tf ci)),
    dgs_event      = (\<lambda>ev. unit_step_for_lifted gs empty_pred (event\<^sup># tf ev)),
    dgs_caller_cont    = (\<lambda>_ d _. d),
    dgs_combine_env    = (\<lambda>ci dc de g. unit_combine_step_env_for_lifted gs ci dc g),
    dgs_combine_assign = (\<lambda>ci de g merged. unit_combine_step_assign_for_lifted gs ci empty_pred de merged)
  \<rparr>"

text \<open>Gate 1 -- record-level type sanity: the generic \<^const>\<open>dg_spec_step\<close>/\<^const>\<open>dgs_combine\<close>
  machinery accepts a \<^type>\<open>dg_spec\<close> whose carriers are \<^type>\<open>lifted\<close> exactly as it accepts the
  raw carrier, and dispatches to the staged primitives with no further reasoning about \<open>gs\<close>.\<close>

lemma dg_spec_step_unit_for_lifted:
  "dg_spec_step (unit_dg_spec_for_lifted gs empty_pred tf) a =
     unit_step_for_lifted gs empty_pred (apply_tf tf a)"
  unfolding unit_dg_spec_for_lifted_def
  by (cases a) simp_all

lemma dgs_enter_unit_dg_spec_for_lifted:
  "dgs_enter (unit_dg_spec_for_lifted gs empty_pred tf) ci =
     unit_step_for_lifted gs empty_pred (snd o enter\<^sup># tf ci)"
  unfolding unit_dg_spec_for_lifted_def by simp

lemma dgs_combine_unit_dg_spec_for_lifted:
  "dgs_combine (unit_dg_spec_for_lifted gs empty_pred tf) ci dc de g =
     unit_combine_step_assign_for_lifted gs ci empty_pred de
       (unit_combine_step_env_for_lifted gs ci dc g)"
  unfolding dgs_combine_def unit_dg_spec_for_lifted_def by simp

text \<open>Gate 2 -- whole-record agreement on reachable inputs whose transfer result is not itself
  witness-bottom: the lifted record reduces to \<^const>\<open>unit_dg_spec_for\<close>'s existing behaviour,
  wrapped in \<^const>\<open>Lifted\<close>.\<close>

lemma dg_spec_step_unit_for_lifted_agrees:
  assumes "\<not> empty_pred (apply_tf tf a (combine_env gs d g))"
  shows "dg_spec_step (unit_dg_spec_for_lifted gs empty_pred tf) a (Lifted d) (Lifted g) =
           (Lifted (fst (dg_spec_step (unit_dg_spec_for gs tf) a d g)),
            Lifted (snd (dg_spec_step (unit_dg_spec_for gs tf) a d g)))"
  using assms
  unfolding dg_spec_step_unit_for_lifted dg_spec_step_unit_for
  by (rule unit_step_for_lifted_agrees)

lemma dgs_combine_unit_dg_spec_for_lifted_agrees:
  assumes "\<not> empty_pred (combine_assign (ci_dst ci) (de ret_var) (combine_env gs dc g))"
  shows "dgs_combine (unit_dg_spec_for_lifted gs empty_pred tf) ci (Lifted dc) (Lifted de) (Lifted g) =
           (Lifted (fst (dgs_combine (unit_dg_spec_for gs tf) ci dc de g)),
            Lifted (snd (dgs_combine (unit_dg_spec_for gs tf) ci dc de g)))"
proof -
  have joined: "restrict_global_for gs (combine_env gs dc g) \<squnion> restrict_local_for gs (combine_env gs dc g)
                  = combine_env gs dc g"
    by (rule restrict_global_for_local_join)
  show ?thesis
    unfolding dgs_combine_unit_dg_spec_for_lifted dgs_combine_unit_dg_spec_for
      unit_combine_step_env_for_lifted_def unit_combine_step_env_for_def
      unit_combine_step_assign_for_lifted_def unit_combine_step_assign_for_def
    using assms
    by (simp add: Let_def joined)
qed

text \<open>Gate 3 -- whole-record strictness: both the unary and the return/combine semantic-bottom
  cases collapse to structural \<^const>\<open>Bot\<close>, and callee-exit unreachability dominates the combine
  independent of the caller side's own reachability (including through the env stage, which by
  construction never inspects \<open>de\<close>).\<close>

lemma dg_spec_step_unit_for_lifted_collapses_bot:
  assumes "empty_pred (apply_tf tf a (combine_env gs d g))"
  shows "dg_spec_step (unit_dg_spec_for_lifted gs empty_pred tf) a (Lifted d) (Lifted g) = (Bot, Bot)"
  using assms
  unfolding dg_spec_step_unit_for_lifted
  by (rule unit_step_for_lifted_collapses_bot)

lemma dgs_combine_unit_dg_spec_for_lifted_de_bot:
  "dgs_combine (unit_dg_spec_for_lifted gs empty_pred tf) ci dc Bot g = (Bot, Bot)"
  unfolding dgs_combine_unit_dg_spec_for_lifted by simp

lemma dgs_combine_unit_dg_spec_for_lifted_dc_bot:
  "dgs_combine (unit_dg_spec_for_lifted gs empty_pred tf) ci Bot (Lifted de) g = (Bot, Bot)"
  unfolding dgs_combine_unit_dg_spec_for_lifted by simp



end
