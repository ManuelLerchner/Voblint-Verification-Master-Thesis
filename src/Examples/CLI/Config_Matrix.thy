theory Config_Matrix
  imports "Voblint_CLI.Config_Tables"
begin

section \<open>What the resolver answers, pinned\<close>

text \<open>
  The resolver is generated from the analysis registry, so these are not a
  restatement of its equations: they are the CLI's observable behaviour written
  out independently of the table that produces it, and they fail if the registry
  changes what a domain publishes. That is the point of keeping them by hand.
\<close>


text \<open>
  Every currently-public combination and its resolution, as a regression
  against the CLI's actual observable behavior rather than a restatement of
  the equations above. \<open>Interval\<close> at \<open>Ctx_EntryState\<close> pins each of the
  three explicit-solver rejections individually, not just one
  representative: the CLI's solver/context exclusion is unconditional on
  the solver value, and only pinning \<open>Solver_Join\<close> (say) would leave
  \<open>Solver_Warrow\<close> -- the one value that happens to equal EntryState's own
  internal default -- unpinned, exactly the case most likely to
  accidentally become valid in a future edit.
\<close>

text \<open>
  Congruence, pinned the way the other four are. It publishes always-join and
  per-origin at \<open>Ctx_None\<close> and always-join at both context modes, and rejects
  the two widening rules everywhere: its modulus only ever coarsens, so an
  ascending chain is a divisor chain and terminates, leaving widening nothing
  to accelerate and no solved table behind it.
\<close>

lemma resolver_congruence_default:
  "resolve_analysis_config (default_config Congruence_Analysis Ctx_None)
     = Some (Plan_Congruence Solver_Join)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_congruence_per_origin_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_PerOrigin,
       cfg_context = Ctx_None \<rparr>
   = Some (Plan_Congruence Solver_PerOrigin)"
  by simp

lemma resolver_congruence_warrow_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_Warrow,
       cfg_context = Ctx_None \<rparr>
   = None"
  by simp

lemma resolver_congruence_warrow_per_origin_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
       cfg_context = Ctx_None \<rparr>
   = None"
  by simp

lemma resolver_congruence_entrystate_default_valid:
  "resolve_analysis_config (default_config Congruence_Analysis Ctx_EntryState)
     = Some (Plan_Congruence_EntryState Solver_Join)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_congruence_entrystate_per_origin_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_PerOrigin,
       cfg_context = Ctx_EntryState \<rparr>
   = None"
  by simp

lemma resolver_congruence_callstring_k1_valid:
  "resolve_analysis_config (default_config Congruence_Analysis (Ctx_CallString 1))
     = Some (Plan_Congruence_CallString Solver_Join 1)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_congruence_callstring_zero_invalid:
  "resolve_analysis_config (default_config Congruence_Analysis (Ctx_CallString 0)) = None"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_default:
  "resolve_analysis_config (default_config Sign_Analysis Ctx_None) = Some (Plan_Sign Solver_Join)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_interval_default:
  "resolve_analysis_config (default_config Interval_Analysis Ctx_None) = Some (Plan_Interval Solver_Warrow)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_int_default:
  "resolve_analysis_config (default_config Int_Analysis Ctx_None) = Some (Plan_Int Solver_Warrow)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_warrow_invalid:
  "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_None \<rparr> = None"
  by simp

lemma resolver_interval_entrystate_default_valid:
  "resolve_analysis_config (default_config Interval_Analysis Ctx_EntryState)
     = Some (Plan_Interval_EntryState Solver_Warrow)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_interval_entrystate_join_valid:
  "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Interval_EntryState Solver_Join)"
  by simp

lemma resolver_interval_entrystate_per_origin_valid:
  "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Interval_EntryState Solver_PerOrigin)"
  by simp

lemma resolver_interval_entrystate_warrow_valid:
  "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Interval_EntryState Solver_Warrow)"
  by simp

text \<open>
  Sign at \<open>Ctx_EntryState\<close>, pinned the same way \<open>Ctx_CallString\<close>'s own regressions are:
  valid at the implicit-default and explicit \<open>Solver_Join\<close> selections, invalid at the
  two solvers Sign's entry-state soundness does not prove.
\<close>

lemma resolver_sign_entrystate_default_valid:
  "resolve_analysis_config (default_config Sign_Analysis Ctx_EntryState)
     = Some (Plan_Sign_EntryState Solver_Join)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_entrystate_explicit_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
   = Some (Plan_Sign_EntryState Solver_Join)"
  by simp

lemma resolver_sign_entrystate_per_origin_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr>
   = None"
  by simp

lemma resolver_sign_entrystate_warrow_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
   = None"
  by simp

text \<open>
  Int at \<open>Ctx_EntryState\<close>: the implicit default resolves to \<open>Solver_Warrow\<close>, the
  explicit \<open>Solver_Warrow\<close>/\<open>Solver_Join\<close> selections are valid, and the two solvers
  Int's own entry-state soundness does not certify stay invalid.
\<close>

lemma resolver_int_entrystate_default_valid:
  "resolve_analysis_config (default_config Int_Analysis Ctx_EntryState)
     = Some (Plan_Int_EntryState Solver_Warrow)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_int_entrystate_explicit_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
   = Some (Plan_Int_EntryState Solver_Join)"
  by simp

lemma resolver_int_entrystate_per_origin_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr>
   = None"
  by simp

lemma resolver_int_entrystate_warrow_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
   = Some (Plan_Int_EntryState Solver_Warrow)"
  by simp

text \<open>
  Call-string, pinned the same way: \<open>k=1\<close>/\<open>k=2\<close> at the implicit default
  solver resolve to Warrow; \<open>k=0\<close> is rejected regardless of solver, even
  though \<open>cs_route 0\<close> (\<open>Call_String_Context\<close>) is itself a well-defined,
  well-typed route (it collapses every activation's context to \<open>[]\<close>,
  distinct from \<open>Ctx_None\<close>'s own, entirely separate flat equation system --
  \<open>k=0\<close> is not \<open>Ctx_None\<close> in disguise). Exposing it anyway would only
  invite exactly the confusion this decision avoids: a user who wants no
  context sensitivity already has \<open>Ctx_None\<close>; a \<open>call-string\<close> selection
  whose only well-typed positive-information use is separating at least two
  call sites needs \<open>k \<ge> 1\<close> to do that at all, so \<open>k=0\<close> has no positive
  reason to exist as a public value. Every explicit-solver pairing at \<open>k \<ge> 1\<close>
  is valid, exactly as \<open>Ctx_EntryState\<close>'s now is; Sign/Int at any \<open>k\<close> stay
  rejected, matching \<open>Ctx_EntryState\<close>'s.
\<close>

lemma resolver_interval_callstring_k1_valid:
  "resolve_analysis_config (default_config Interval_Analysis (Ctx_CallString 1))
     = Some (Plan_Interval_CallString Solver_Warrow 1)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_interval_callstring_k2_valid:
  "resolve_analysis_config (default_config Interval_Analysis (Ctx_CallString 2))
     = Some (Plan_Interval_CallString Solver_Warrow 2)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_interval_callstring_zero_invalid:
  "resolve_analysis_config (default_config Interval_Analysis (Ctx_CallString 0)) = None"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_interval_callstring_zero_explicit_solver_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 0 \<rparr>
   = None"
  by simp

lemma resolver_interval_callstring_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Interval_CallString Solver_Join 2)"
  by simp

lemma resolver_interval_callstring_per_origin_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Interval_CallString Solver_PerOrigin 2)"
  by simp

lemma resolver_interval_callstring_warrow_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Interval_CallString Solver_Warrow 2)"
  by simp

text \<open>
  Sign at \<open>Ctx_CallString\<close>: valid at \<open>k \<ge> 1\<close> under the one solver Sign's own
  routed call-string soundness actually proves (\<open>Solver_Join\<close>, matching the
  implicit default), \<open>k = 0\<close> rejected exactly as Interval's is, and
  \<open>Solver_PerOrigin\<close>/\<open>Solver_Warrow\<close> rejected -- unlike Interval, where every
  solver is proved at every context -- because Sign's call-string soundness
  currently proves only the always-join discipline.
\<close>

lemma resolver_sign_callstring_k1_valid:
  "resolve_analysis_config (default_config Sign_Analysis (Ctx_CallString 1))
     = Some (Plan_Sign_CallString Solver_Join 1)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_callstring_k2_valid:
  "resolve_analysis_config (default_config Sign_Analysis (Ctx_CallString 2))
     = Some (Plan_Sign_CallString Solver_Join 2)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_callstring_zero_invalid:
  "resolve_analysis_config (default_config Sign_Analysis (Ctx_CallString 0)) = None"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_callstring_explicit_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Sign_CallString Solver_Join 2)"
  by simp

lemma resolver_sign_callstring_per_origin_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString 2 \<rparr>
   = None"
  by simp

lemma resolver_sign_callstring_warrow_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 2 \<rparr>
   = None"
  by simp

text \<open>
  Int at \<open>Ctx_CallString\<close>: valid at \<open>k \<ge> 1\<close> under the implicit default (\<open>Solver_Warrow\<close>)
  and the explicit \<open>Solver_Warrow\<close>/\<open>Solver_Join\<close> selections, invalid at \<open>k = 0\<close> and at
  the two solvers Int's own call-string soundness does not certify.
\<close>

lemma resolver_int_callstring_k1_valid:
  "resolve_analysis_config (default_config Int_Analysis (Ctx_CallString 1))
     = Some (Plan_Int_CallString Solver_Warrow 1)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_int_callstring_k2_valid:
  "resolve_analysis_config (default_config Int_Analysis (Ctx_CallString 2))
     = Some (Plan_Int_CallString Solver_Warrow 2)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_int_callstring_zero_invalid:
  "resolve_analysis_config (default_config Int_Analysis (Ctx_CallString 0)) = None"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_int_callstring_explicit_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Int_CallString Solver_Join 2)"
  by simp

lemma resolver_int_callstring_per_origin_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString 2 \<rparr>
   = None"
  by simp

lemma resolver_int_callstring_warrow_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Int_CallString Solver_Warrow 2)"
  by simp



text \<open>
  Parity: supported at every context under \<open>Solver_Join\<close>, and
  additionally under \<open>Solver_PerOrigin\<close> at \<open>Ctx_None\<close> --- the solved tables its own
  routed instances build. Unsupported wherever it has no such instance. Pinned
  individually rather than as one blanket lemma, so a later instantiation has to
  update the specific line it actually makes valid.
\<close>

lemma resolver_parity_default_valid:
  "resolve_analysis_config (default_config Parity_Analysis Ctx_None) = Some (Plan_Parity Solver_Join)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_parity_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_None \<rparr>
   = Some (Plan_Parity Solver_Join)"
  by simp

lemma resolver_parity_per_origin_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_None \<rparr>
   = Some (Plan_Parity Solver_PerOrigin)"
  by simp

lemma resolver_parity_warrow_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_None \<rparr>
   = None"
  by simp

lemma resolver_parity_entrystate_valid:
  "resolve_analysis_config (default_config Parity_Analysis Ctx_EntryState)
   = Some (Plan_Parity_EntryState Solver_Join)"
  by (simp add: default_config_def mk_analysis_config_def)

text \<open>A zero-length call string is the unit context spelled twice, so it is
  rejected rather than silently answered by the flat route.\<close>

lemma resolver_parity_callstring_valid:
  "resolve_analysis_config (default_config Parity_Analysis (Ctx_CallString k))
   = (if k = 0 then None else Some (Plan_Parity_CallString Solver_Join k))"
  by (simp add: default_config_def mk_analysis_config_def)

lemma valid_analysis_config_eq_resolver:
  "valid_analysis_config cfg \<longleftrightarrow> resolve_analysis_config cfg \<noteq> None"
  by (simp add: valid_analysis_config_def)

end

