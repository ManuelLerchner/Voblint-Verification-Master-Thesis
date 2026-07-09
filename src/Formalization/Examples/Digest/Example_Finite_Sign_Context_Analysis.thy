theory Example_Finite_Sign_Context_Analysis
  imports
    Voblint_Analysis.Exec_Sign_Cmp_Keyed_Gen_Run
    Voblint_Analysis.Exec_Sign_Cmp_Seed_Sound
begin

section \<open>Finite sign-derived calling contexts\<close>

text \<open>
  This example uses a finite digest of the sign state as the calling context.  The
  context is computed from the sign value of global \<open>G\<close>; the full \<typ>\<open>sign st\<close>
  remains the value-domain state, while the context/key is a finite datatype.
\<close>

text \<open>
  \<^bold>\<open>Program: a Goblint sequential D/G/C scenario.\<close>  \<open>fctx_prog\<close> is \<open>void f() { GH :=
  G }; void main() { G := 0; f(); G := 1; f() }\<close> --- a procedure that reads a global
  under two distinct calling contexts.  It is analysed here \<^emph>\<open>three\<close> ways:

    \<^enum> \<^bold>\<open>Keyed \<^const>\<open>side_env_cmp\<close> (the obstruction, baseline).\<close>  With a finite
      context and the observation read \<^const>\<open>side_env_cmp\<close> \<open>= local \<squnion> global\<close>,
      \<open>ENTER_MONO\<close> is unprovable: the global summand pins \<open>G\<close> to \<^const>\<open>SNonNeg\<close> at
      the shared caller context (\<open>fctx_caller_read_G_imprecise\<close>).
    \<^enum> \<^bold>\<open>Value-refined caller contexts (\<open>fctxu\<close>, prototype).\<close>  An intra-edge context
      update splits \<open>main\<close> so calls 4/7 sit under \<open>GZero\<close>/\<open>GPos\<close> --- an orthogonal
      finite-context axis, no soundness claim.
    \<^enum> \<^bold>\<open>Seeded-clean (R_read) --- the certified Goblint-faithful resolution.\<close>  The
      section \<^bold>\<open>Migration\<close> below runs the seeded-clean spine
      (\<^const>\<open>side_cfg_T_eff_cmp_seed_st\<close> + \<^const>\<open>sign_etf_clean_st\<close> +
      \<^const>\<open>kgen_combine_rread\<close>) on the \<^emph>\<open>same\<close> \<open>fctx_prog\<close>.  It seeds the
      callee-entry \<^emph>\<open>local\<close> from the caller global and reads only that local, so the
      caller read of \<open>G\<close> is a \<^emph>\<open>point\<close> (\<^const>\<open>SZero\<close>/\<^const>\<open>SPos\<close>, strictly below
      the \<^const>\<open>SNonNeg\<close> the \<^const>\<open>side_env_cmp\<close> read is stuck at) and its
      soundness is certified (\<open>clean_ctx_collect_rread\<close>).

  Interpretations 1 and 2 stay as the conservative baseline and the comparison
  prototype; interpretation 3 is the seeded-clean default for this sequential D/G/C
  program.
\<close>

datatype sign_gctx = GZero | GPos | GNonNeg | GOther

lemma UNIV_sign_gctx: "(UNIV :: sign_gctx set) = {GZero, GPos, GNonNeg, GOther}"
  using sign_gctx.exhaust by blast

instance sign_gctx :: finite
  by intro_classes (simp add: UNIV_sign_gctx)


definition sign_gctx_of_sign :: "sign \<Rightarrow> sign_gctx" where
  "sign_gctx_of_sign s =
     (case s of SZero \<Rightarrow> GZero | SPos \<Rightarrow> GPos | SNonNeg \<Rightarrow> GNonNeg | _ \<Rightarrow> GOther)"

definition sign_gctx_of_st :: "sign st \<Rightarrow> sign_gctx" where
  "sign_gctx_of_st s = sign_gctx_of_sign (lookup_st (restrict_global_st s) ''G'')"

lemma sign_gctx_of_zero [simp]:
  "sign_gctx_of_st (update_st (bot :: sign st) ''G'' SZero) = GZero"
  by (simp add: sign_gctx_of_st_def sign_gctx_of_sign_def is_global_def restrict_global_def)

lemma sign_gctx_of_pos [simp]:
  "sign_gctx_of_st (update_st (bot :: sign st) ''G'' SPos) = GPos"
  by (simp add: sign_gctx_of_st_def sign_gctx_of_sign_def is_global_def restrict_global_def)


definition fctx_prog :: imp_prog where
  "fctx_prog = \<lbrakk>
     int G, GH;

     void f() {
       GH := G
     }
     void main() {
       G := 0;
       f();
       G := 1;
       f()
     }
   \<rbrakk>"

definition fctx_cfg :: cfg where
  "fctx_cfg = compile_prog (prog_table fctx_prog) (prog_procs fctx_prog) (prog_main fctx_prog)"

definition fctx_ec :: "sign_gctx \<Rightarrow> sign st \<Rightarrow> sign_gctx" where
  "fctx_ec ctx sc = sign_gctx_of_st sc"

definition fctx_ec_call :: "pp \<Rightarrow> sign_gctx \<Rightarrow> sign st \<Rightarrow> sign_gctx" where
  "fctx_ec_call cc ctx sc =
     (case sign_gctx_of_st sc of
        GZero \<Rightarrow> GZero
      | GPos \<Rightarrow> GPos
      | GNonNeg \<Rightarrow> (if cc = 4 then GZero else if cc = 7 then GPos else GNonNeg)
      | GOther \<Rightarrow> GOther)"

definition fctx_call_state :: "pp \<Rightarrow> sign st \<Rightarrow> sign st" where
  "fctx_call_state cc s =
     (if cc = 4 then update_st (update_st s ''G'' SZero) ''GH'' SBot
      else if cc = 7 then update_st (update_st s ''G'' SPos) ''GH'' SBot
      else s)"

definition unit_combine_tree_cmp_ctx_st ::
  "(pp \<Rightarrow> sign_gctx \<Rightarrow> sign st \<Rightarrow> sign_gctx) \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> sign_gctx
   \<Rightarrow> (pp \<times> sign_gctx, sign_gctx, sign st) strategy_tree"
where
  "unit_combine_tree_cmp_ctx_st ec cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG ctx (\<lambda>g.
       let caller = fctx_call_state cc (sc \<squnion> g);
           callee_ctx = ec cc ctx caller in
       Side callee_ctx (restrict_global_st caller)
         (QueryL (ex, callee_ctx) (\<lambda>se.
           let res = restrict_local_st caller \<squnion> restrict_global_st se in
           Side callee_ctx (restrict_global_st res)
             (Answer (restrict_local_st res))))))"
definition fctx_eqs :: "(pp \<times> sign_gctx, sign_gctx, sign st) eqsT" where
  "fctx_eqs = side_cfg_T_eff_cmp_st id
      (\<lambda>c cc ex. unit_combine_tree_cmp_ctx_st fctx_ec_call cc ex c)
      fctx_cfg sign_etf_st bot bot cinit_sign_st"

definition fctx_solution ::
  "(pp \<times> sign_gctx) set \<times> ((pp \<times> sign_gctx) + sign_gctx \<Rightarrow> sign st)" where
  "fctx_solution = TD_side_always_join_Interp_solve fctx_eqs (cfg_exit fctx_cfg, GOther)"

lemma fctx_runs: "fst fctx_solution \<noteq> {}"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
  by eval

text \<open>
  With call-enter edges filtered out of the intra fold, each callee context slot
  receives its globals only through the combine seed, so the two activations stay
  separated: the \<open>GZero\<close> context sees \<open>GH = SZero\<close>, the \<open>GPos\<close> context \<open>GH = SPos\<close>.
\<close>

lemma fctx_slot_zero_precise:
  "lookup_st (snd fctx_solution (Inr GZero)) ''GH'' = SZero"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

lemma fctx_slot_pos_precise:
  "lookup_st (snd fctx_solution (Inr GPos)) ''GH'' = SPos"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

lemma fctx_join_all:
  "lookup_st (snd fctx_solution (Inr GZero) \<squnion> snd fctx_solution (Inr GPos)) ''GH'' = SNonNeg"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

text \<open>
  The finite context type can instantiate the generic keyed theorem.  This theorem
  states the soundness-facing contract for any abstract post-fixpoint of the same
  conservative keyed generator shape.  The executable value-dependent context run
  above is the operational target; proving that run feeds this theorem is the next
  bridge toward a dedicated finite context-domain locale.
\<close>

definition fctx_abs_eqs :: "(pp \<times> sign_gctx, sign_gctx, sign abs_state) eqsT" where
  "fctx_abs_eqs =
     side_cfg_T_eff_cmp id
       (\<lambda>c cc ex. map_gtree (\<lambda>_. c)
          (map_ltree (\<lambda>w. (w, c)) (etf_combine sign_etf_unit cc ex)))
       fctx_cfg sign_etf_unit fresh_frame_sign bot (fun_of_st cinit_sign_st)"

theorem fctx_keyed_sound_if_post_fixpoint:
  fixes sigma :: "pp \<times> sign_gctx + sign_gctx \<Rightarrow> sign abs_state"
  assumes pp: "part_post_solution fctx_abs_eqs x sigma vars"
  assumes inr: "inr_slot_locals_bot_ctx sigma"
  assumes inl: "inl_slot_globals_bot_ctx sigma"
  assumes cover_edge: "\<And>u a v. (u, a, v) \<in> edges fctx_cfg \<Longrightarrow> (v, ctx) \<in> vars"
  assumes cover_comb: "\<And>cc ex ret. (cc, ex, ret) \<in> combines fctx_cfg \<Longrightarrow> (ret, ctx) \<in> vars"
  assumes cover_entry: "(cfg_entry fctx_cfg, ctx) \<in> vars"
  assumes S_sound: "S \<le> \<lbrakk>fun_of_st cinit_sign_st\<rbrakk>"
  shows "cfg_collect fctx_cfg S v0 \<le> \<lbrakk>side_env_cmp (=) sigma (v0, ctx)\<rbrakk>"
proof -
  have pp': "part_post_solution
      (side_cfg_T_eff_cmp id
        (\<lambda>c cc ex. map_gtree (\<lambda>_. c)
          (map_ltree (\<lambda>w. (w, c)) (etf_combine sign_etf_unit cc ex)))
        fctx_cfg sign_etf_unit fresh_frame_sign bot (fun_of_st cinit_sign_st))
      x sigma vars"
    using pp unfolding fctx_abs_eqs_def by simp
  have finE: "finite (edges fctx_cfg)"
    unfolding fctx_cfg_def fctx_prog_def using compile_prog_finite by simp
  have finC: "finite (combines fctx_cfg)"
    unfolding fctx_cfg_def fctx_prog_def using compile_prog_finite by simp
  show ?thesis
    by (rule side_cfg_T_eff_cmp_collect_sound_eq
          [OF sign_sound_etf_unit_framed inr inl S_sound pp' finE finC
              cover_edge cover_comb cover_entry])
qed

section \<open>Value-dependent (switching) combine contract, concretely\<close>

text \<open>
  The certified soundness kernel now takes the combine soundness obligation as a
  hypothesis: \<open>switching_combine_sound\<close> names precisely the
  bound ``\<open>etf_full (etf_combine etf cc ex) (pull_gk gkey ctx \<sigma>) \<le> side_env
  (pull_gk gkey ctx \<sigma>) ret\<close>'' that the combine branch of
  \<open>side_cfg_T_eff_cmp_collect_sound_gen\<close> consumes, and
  \<open>fixed_combine_satisfies_switching_combine_sound\<close> discharges it for the
  context-fixed combine (the degenerate Seidl 2026 eq. (6) instance \<open>context d c =
  c\<close>).  The precise executable witnesses (\<open>fctx_eqs\<close> here, \<open>kgen_eqs\<close>) use a
  value-\<^emph>\<open>dependent\<close> combine that \<open>Side\<close>s callee globals to a \<^emph>\<open>switched\<close> slot
  \<open>callee_ctx\<close>; the section below discharges the contract's obligations concretely
  for the two call sites of \<open>fctx_prog\<close>.
\<close>

subsection \<open>The example's switching route discharges the contract's obligations concretely\<close>

text \<open>
  The two call sites of \<open>fctx_prog\<close> are \<open>cc = 4\<close> (the \<open>G := 0; f()\<close>) and \<open>cc = 7\<close>
  (the \<open>G := 1; f()\<close>).  \<^const>\<open>fctx_call_state\<close> overwrites \<open>G\<close> before the call, so the
  routed callee context is determined \<^emph>\<open>independently of the solver state\<close>: site 4
  routes to \<open>GZero\<close>, site 7 to \<open>GPos\<close>.
\<close>

text \<open>
  Seidl et al. (FM 2026) notation: \<^const>\<open>fctx_ec_call\<close> is the paper's
  \<open>context\<^bsub>u,f,args\<^esub> : D[u] -> C -> C\<close> --- the value-dependent callee-context
  selector of equation (6).  This is the shape of the paper's Example 7
  (1-callstring / partial tabulation): the same procedure \<open>f\<close>, reached from two
  distinct call sites, is routed to two distinct finite contexts (\<open>GZero\<close> vs
  \<open>GPos\<close>) so the two instances prove separate facts (\<open>fctx_route_bound_zero\<close> /
  \<open>_pos\<close>).
\<close>

lemma fctx_route_call4: "fctx_ec_call 4 ctx (fctx_call_state 4 s) = GZero"
  by (simp add: fctx_ec_call_def fctx_call_state_def sign_gctx_of_st_def
        sign_gctx_of_sign_def is_global_def restrict_global_def)

lemma fctx_route_call7: "fctx_ec_call 7 ctx (fctx_call_state 7 s) = GPos"
  by (simp add: fctx_ec_call_def fctx_call_state_def sign_gctx_of_st_def
        sign_gctx_of_sign_def is_global_def restrict_global_def)

text \<open>
  The side contribution the switching combine emits into each routed slot --- the
  caller's surviving global \<open>G\<close> --- is bounded by that keyed slot in the generated
  solution: \<open>SZero\<close> lands in the \<open>GZero\<close> slot, \<open>SPos\<close> in the \<open>GPos\<close> slot.
\<close>

lemma fctx_route_bound_zero:
  "SZero \<le> lookup_st (snd fctx_solution (Inr GZero)) ''G''"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

lemma fctx_route_bound_pos:
  "SPos \<le> lookup_st (snd fctx_solution (Inr GPos)) ''G''"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

subsection \<open>Obstruction: the shared caller context defeats ENTER_MONO\<close>

text \<open>
  Both call sites (\<open>cc = 4\<close>, \<open>cc = 7\<close>) live in the caller context \<open>GOther\<close>
  (the reachable set contains only \<open>(4, GOther)\<close> and \<open>(7, GOther)\<close>), whose global
  slot \<open>Inr GOther\<close> joins the two activations.  The read of \<open>G\<close> at either call site
  is therefore \<open>SNonNeg = SZero \<squnion> SPos\<close>: its concretisation contains stores with
  \<open>G = 0\<close> (enter digest \<open>GZero\<close>) and with \<open>G = 1\<close> (enter digest \<open>GPos\<close>).

  The per-context kernel's \<open>ENTER_MONO\<close> obligation (\<^theory>\<open>Voblint_Analysis.TD_Side_Eff_Cmp_Sound\<close>)
  demands one routed context \<open>ec cl ctx read\<close> that \<open>(=)\<close>-matches the enter digest of
  \<^emph>\<open>every\<close> concretising store.  No value matches both \<open>GZero\<close> and \<open>GPos\<close>.  Making
  \<open>ec\<close> call-site-aware routes the \<^emph>\<open>return\<close> read (CMP_SOUND, where the call-state pin
  is fresh) but not the \<^emph>\<open>enter\<close> digest, which reads this polluted caller abstraction
  upstream of \<open>ec\<close>.  A sound fctx cover needs a caller context exact on \<open>G\<close> at the call
  site (value-refined / call-string caller context).
\<close>

lemma fctx_caller_read_G_imprecise:
  "lookup_st (snd fctx_solution (Inl (4, GOther)) \<squnion> snd fctx_solution (Inr GOther)) ''G'' = SNonNeg"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

lemma sign_zero_pos_join: "(SZero :: sign) \<squnion> SPos = SNonNeg"
  by eval



subsection \<open>Investigation: why no call-boundary context scheme makes Obs exact on G\<close>

text \<open>
  The required first step: locate precisely why \<open>ENTER_MONO\<close> is unprovable here, and
  why it is a context-scheme limit rather than a retain limit.

  \<open>ENTER_MONO\<close> (\<^theory>\<open>Voblint_Analysis.TD_Side_Eff_Cmp_Sound\<close>) quantifies over the
  \<^emph>\<open>observation\<close> concretisation \<open>gamma (side_env_cmp gcmp sigma (cl, ctx))\<close> at each
  call node \<open>cl\<close> under the caller context \<open>ctx\<close>, and demands ONE routed callee context
  that \<open>(=)\<close>-matches the enter digest of \<^emph>\<open>every\<close> concretising store.  For that to hold
  the observation read must be exact on the digest variable \<open>G\<close>.

  It is not, and no call-boundary context scheme can make it so on this program:
  \<^item> Both call nodes \<open>4\<close> and \<open>7\<close> live under a single caller context \<open>GOther\<close>
    (\<open>fctx_call4_only_GOther\<close>, \<open>fctx_call7_only_GOther\<close>).  This is structural, not
    accidental: context changes only at call boundaries, and \<open>4\<close>/\<open>7\<close> are interior
    points of one \<open>main\<close> activation, so every trace reaching them carries \<open>main\<close>'s
    single entry digest.  No call-boundary \<open>ec\<close> can assign interior points distinct
    contexts.
  \<^item> The keyed global slot \<open>Inr GOther\<close> aggregates every \<open>G\<close>-write performed under that
    context flow-INSENSITIVELY, so it joins \<open>main\<close>'s \<open>G := 0\<close> and \<open>G := 1\<close> to
    \<^const>\<open>SNonNeg\<close> (\<open>fctx_GOther_slot_joins_G\<close>).
  \<^item> \<^const>\<open>side_env_cmp\<close> reads \<open>sigma (Inl (cl, ctx)) \<squnion> sigma (Inr ctx)\<close>; the global
    summand pins the observation of \<open>G\<close> at every call node to \<^const>\<open>SNonNeg\<close>
    (\<open>fctx_caller_read_G_imprecise\<close> at \<open>4\<close>, \<open>fctx_caller_read_G_imprecise7\<close> at \<open>7\<close>),
    regardless of the local slot's precision.

  Retain sharpens only the routing read \<^const>\<open>route_read_cmp\<close> (the local slot); it
  cannot remove the flow-insensitive global summand \<^const>\<open>side_env_cmp\<close> adds.  Each
  candidate call-boundary scheme collapses the same way --- call-site-refined
  (\<open>call_site option \<times> sign_gctx\<close>): \<open>main\<close>'s context is one value, the call-site
  component refines the CALLEE key, not \<open>main\<close>; call-string: \<open>main\<close> is the root, both
  \<open>f\<close>-calls share caller string \<open>[]\<close>; entry-store: \<open>main\<close> has one entry store, one
  context.  In every case \<open>Inr (context of main)\<close> joins both \<open>G\<close>-writes.  A per-program-point
  distinction (\<open>G = 0\<close> at \<open>4\<close> vs \<open>G = 1\<close> at \<open>7\<close>) is flow-sensitivity WITHIN one
  activation --- expressible only by an intra-edge context update (\<open>step_ctx\<close>), which the
  call-only protocol excludes.  Hence: stop; the fix is not a call-boundary context scheme.
\<close>

lemma fctx_caller_read_G_imprecise7:
  "lookup_st (snd fctx_solution (Inl (7, GOther)) \<squnion> snd fctx_solution (Inr GOther)) ''G'' = SNonNeg"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

lemma fctx_call4_only_GOther:
  "(4, GOther) \<in> fst fctx_solution
   \<and> (4, GZero) \<notin> fst fctx_solution
   \<and> (4, GPos) \<notin> fst fctx_solution
   \<and> (4, GNonNeg) \<notin> fst fctx_solution"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

lemma fctx_call7_only_GOther:
  "(7, GOther) \<in> fst fctx_solution
   \<and> (7, GZero) \<notin> fst fctx_solution
   \<and> (7, GPos) \<notin> fst fctx_solution
   \<and> (7, GNonNeg) \<notin> fst fctx_solution"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

lemma fctx_GOther_slot_joins_G:
  "lookup_st (snd fctx_solution (Inr GOther)) ''G'' = SNonNeg"
  unfolding fctx_solution_def fctx_eqs_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

section \<open>Prototype: value-refined caller contexts split before the calls\<close>

text \<open>
  The example-local fix for the \<open>ENTER_MONO\<close> obstruction.  The keyed generator keys
  every interior point of one activation under a single context.  Here we let the caller
  context be updated on \<^emph>\<open>selected context-relevant edges only\<close> --- the two constant
  \<open>G\<close>-assignments in \<open>main\<close> --- so \<open>main\<close> is analysed under \<open>GZero\<close> after \<open>G := 0\<close> and
  \<open>GPos\<close> after \<open>G := 1\<close>.  Call node \<open>4\<close> then sits under \<open>GZero\<close> and call node \<open>7\<close> under
  \<open>GPos\<close>, so each caller context's keyed global slot sees only its own \<open>G\<close>-write --- the
  observation read is exact, and \<open>ENTER_MONO\<close> becomes provable.

  This is a bounded intra-edge context update (a \<^emph>\<open>value-refined\<close> context), not an
  arbitrary \<open>step_ctx\<close>: the transition \<open>fctx_ctx_step\<close> is the identity on every
  edge except the two \<open>G := 0\<close> / \<open>G := 1\<close> assignments.  Prototype only --- no soundness
  claim yet; the point is to exhibit that the split is realisable in the real solver.
\<close>

subsection \<open>A context-updating keyed generator (example-local)\<close>

text \<open>
  The keyed generator \<^const>\<open>side_cfg_T_eff_cmp_st\<close> keys each intra predecessor under the
  current unknown's context (\<open>map_ltree (\<lambda>w. (w, c))\<close>).  This variant threads a
  context transition \<open>cstep\<close> instead: unknown \<open>(v, c)\<close> reads predecessor \<open>u\<close> under every
  predecessor context \<open>cp\<close> with \<open>cstep a cp = c\<close> (enumerated from the finite \<open>clist\<close>).
  On a non-context-relevant edge \<open>cstep a cp = cp\<close>, so the filter keeps only \<open>cp = c\<close> and
  the equation coincides with \<^const>\<open>side_cfg_T_eff_cmp_st\<close>; on a \<open>G\<close>-assignment edge the
  successor context is switched.  Dependencies stay static (a finite, statically-determined
  predecessor set per unknown) and the right-hand side stays monotone (joins of queries).
\<close>

definition side_cfg_T_eff_cmp_ctxupd_st ::
  "('c \<Rightarrow> 'g) \<Rightarrow> 'c list \<Rightarrow> (edge_action \<Rightarrow> 'c \<Rightarrow> 'c)
   \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a st) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> (unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> 'a st
   \<Rightarrow> (pp \<times> 'c, 'g, 'a st) eqsT"
where
  "side_cfg_T_eff_cmp_ctxupd_st gkey clist cstep cmb g etf fresh_frame_st bot0_st s0_st =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
                   \<squnion> (if is_frame_entry g v then fresh_frame_st else \<bottom>);
            intra = concat (map (\<lambda>(u, a).
                          map (\<lambda>cp. map_gtree (\<lambda>_. gkey c)
                                (map_ltree (\<lambda>w. (w, cp)) (apply_etf_st etf a u)))
                              (filter (\<lambda>cp. cstep a cp = c) clist))
                        (non_enter_predecessor_list g v));
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx_st acc0 (intra @ comb)
        in if v = cfg_entry g then Side (gkey c) (restrict_global_st s0_st) t else t)"

subsection \<open>The finite context transition and the solved run\<close>

text \<open>
  Context-relevant edges: after \<open>G := 0\<close> route to \<open>GZero\<close>, after \<open>G := 1\<close> to \<open>GPos\<close>.
  The transition is \<^emph>\<open>deterministic\<close> on the trigger edges: \<open>G := 0\<close> switches only its
  real predecessor context \<open>GOther\<close> to \<open>GZero\<close>, and \<open>G := 1\<close> only \<open>GZero\<close> to \<open>GPos\<close>.
  Any other predecessor context on a trigger edge is dumped into the never-demanded
  \<open>GNonNeg\<close> sink, so the demand solver materialises no spurious context copy (which
  would otherwise re-run the pinning combine and pollute the keyed slot).
\<close>
definition fctx_ctx_step :: "edge_action \<Rightarrow> sign_gctx \<Rightarrow> sign_gctx" where
  "fctx_ctx_step a cx =
     (case a of EA_Assign v e \<Rightarrow>
          (if v = ''G'' \<and> e = IMP2_Syntax.N 0 then (if cx = GOther then GZero else GNonNeg)
           else if v = ''G'' \<and> e = IMP2_Syntax.N 1 then (if cx = GZero then GPos else GNonNeg)
           else cx)
        | _ \<Rightarrow> cx)"

definition fctx_ctx_list :: "sign_gctx list" where
  "fctx_ctx_list = [GZero, GPos, GNonNeg, GOther]"

definition fctxu_eqs :: "(pp \<times> sign_gctx, sign_gctx, sign st) eqsT" where
  "fctxu_eqs = side_cfg_T_eff_cmp_ctxupd_st id fctx_ctx_list fctx_ctx_step
      (\<lambda>c cc ex. unit_combine_tree_cmp_ctx_st fctx_ec_call cc ex c)
      fctx_cfg sign_etf_st bot bot cinit_sign_st"

text \<open>The value-refined context propagates forward, so \<open>main\<close>'s exit (pp 8) is under \<open>GPos\<close>.\<close>
definition fctxu_solution ::
  "(pp \<times> sign_gctx) set \<times> ((pp \<times> sign_gctx) + sign_gctx \<Rightarrow> sign st)" where
  "fctxu_solution = TD_side_always_join_Interp_solve fctxu_eqs (cfg_exit fctx_cfg, GPos)"

lemma fctxu_runs: "fst fctxu_solution \<noteq> {}"
  unfolding fctxu_solution_def fctxu_eqs_def side_cfg_T_eff_cmp_ctxupd_st_def
    fctx_ctx_step_def fctx_ctx_list_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

lemma fctxu_solves:
  "TD_side_always_join_Interp_solve_c fctxu_eqs (cfg_exit fctx_cfg, GPos) \<noteq> None"
  unfolding fctxu_eqs_def side_cfg_T_eff_cmp_ctxupd_st_def
    fctx_ctx_step_def fctx_ctx_list_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

subsection \<open>The split, machine-checked: calls 4/7 land under GZero/GPos, exactly\<close>

text \<open>Call node 4 is analysed under \<open>GZero\<close> and NOT under the joined \<open>GOther\<close>.\<close>
lemma fctxu_call4_GZero:
  "(4, GZero) \<in> fst fctxu_solution \<and> (4, GOther) \<notin> fst fctxu_solution"
  unfolding fctxu_solution_def fctxu_eqs_def side_cfg_T_eff_cmp_ctxupd_st_def
    fctx_ctx_step_def fctx_ctx_list_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

text \<open>Call node 7 is analysed under \<open>GPos\<close> and NOT under the joined \<open>GOther\<close>.\<close>
lemma fctxu_call7_GPos:
  "(7, GPos) \<in> fst fctxu_solution \<and> (7, GOther) \<notin> fst fctxu_solution"
  unfolding fctxu_solution_def fctxu_eqs_def side_cfg_T_eff_cmp_ctxupd_st_def
    fctx_ctx_step_def fctx_ctx_list_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

text \<open>
  The payoff: the caller's observation read of \<open>G\<close> at each call node is now EXACT,
  where the monovariant \<open>GOther\<close> scheme joined both writes to \<^const>\<open>SNonNeg\<close>
  (\<open>fctx_caller_read_G_imprecise\<close>).  This is what makes \<open>ENTER_MONO\<close> provable.
\<close>
lemma fctxu_caller_read_G4_exact:
  "lookup_st (snd fctxu_solution (Inl (4, GZero)) \<squnion> snd fctxu_solution (Inr GZero)) ''G'' = SZero"
  unfolding fctxu_solution_def fctxu_eqs_def side_cfg_T_eff_cmp_ctxupd_st_def
    fctx_ctx_step_def fctx_ctx_list_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

lemma fctxu_caller_read_G7_exact:
  "lookup_st (snd fctxu_solution (Inl (7, GPos)) \<squnion> snd fctxu_solution (Inr GPos)) ''G'' = SPos"
  unfolding fctxu_solution_def fctxu_eqs_def side_cfg_T_eff_cmp_ctxupd_st_def
    fctx_ctx_step_def fctx_ctx_list_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

text \<open>The callee separation carries through: \<open>f\<close>@\<open>GZero\<close> gives \<open>GH = SZero\<close>, \<open>f\<close>@\<open>GPos\<close> gives \<open>GH = SPos\<close>.\<close>
lemma fctxu_fGZero_GH_zero:
  "lookup_st (snd fctxu_solution (Inr GZero)) ''GH'' = SZero"
  unfolding fctxu_solution_def fctxu_eqs_def side_cfg_T_eff_cmp_ctxupd_st_def
    fctx_ctx_step_def fctx_ctx_list_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

lemma fctxu_fGPos_GH_pos:
  "lookup_st (snd fctxu_solution (Inr GPos)) ''GH'' = SPos"
  unfolding fctxu_solution_def fctxu_eqs_def side_cfg_T_eff_cmp_ctxupd_st_def
    fctx_ctx_step_def fctx_ctx_list_def fctx_cfg_def fctx_prog_def fctx_ec_def
    fctx_ec_call_def fctx_call_state_def unit_combine_tree_cmp_ctx_st_def
    sign_gctx_of_st_def sign_gctx_of_sign_def
  by eval

section \<open>Migration: the seeded-clean (R_read) spine resolves the same program, certified\<close>

text \<open>
  The Goblint-faithful resolution of the obstruction, on the \<^emph>\<open>same\<close> \<open>fctx_prog\<close>.
  Instead of a finite context read through \<^const>\<open>side_env_cmp\<close> (interpretation 1,
  which the global summand pins to \<^const>\<open>SNonNeg\<close>) or an intra-edge context update
  (interpretation 2, \<open>fctxu\<close>), the seeded-clean spine keys the context on the caller
  \<^emph>\<open>global\<close> state (\<^const>\<open>restrict_global_st\<close>, which \<^const>\<open>enter_state\<close> preserves),
  seeds that into the callee-entry \<^emph>\<open>local\<close>, and reads only the local
  (\<^const>\<open>sign_etf_clean_st\<close>).  Same generator/combine as \<open>Example_Seed_Clean_Context\<close>,
  now on the global-reading program \<open>f() { GH := G }\<close>.  Its soundness against the
  context-sliced collecting semantics is certified by \<open>clean_ctx_collect_rread\<close>.
\<close>

definition fctx_seed_clean_eqs :: "(pp \<times> sign st, sign st, sign st) eqsT" where
  "fctx_seed_clean_eqs = side_cfg_T_eff_cmp_seed_st id
     (\<lambda>c cc ex. kgen_combine_rread cc ex c)
     restrict_global_st fctx_cfg sign_etf_clean_st bot cinit_sign_st"

definition fctx_seed_clean_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + sign st \<Rightarrow> sign st)" where
  "fctx_seed_clean_solution = TD_side_always_join_Interp_solve fctx_seed_clean_eqs (cfg_exit fctx_cfg, bot)"

lemma fctx_seed_clean_runs: "fst fctx_seed_clean_solution \<noteq> {}"
  unfolding fctx_seed_clean_solution_def fctx_seed_clean_eqs_def fctx_cfg_def fctx_prog_def
    kgen_ec_def kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>
  \<^bold>\<open>The split, certified spine.\<close>  The callee \<open>f\<close> reads \<open>G\<close> (delivered by the seed into
  its local) and writes \<open>GH\<close>: context \<open>{G:SZero}\<close> gives \<open>GH = SZero\<close>, context
  \<open>{G:SPos}\<close> gives \<open>GH = SPos\<close> --- the same precise separation \<open>fctxu\<close> achieves
  (\<open>fctxu_fGZero_GH_zero\<close> / \<open>fctxu_fGPos_GH_pos\<close>), now on the seeded-clean spine whose
  soundness is proved, not prototyped.
\<close>

lemma fctx_seed_clean_split:
  "lookup_st (snd fctx_seed_clean_solution (Inr (Abs_st (SBot, SBot, [(''G'', SZero)])))) ''GH'' = SZero
   \<and> lookup_st (snd fctx_seed_clean_solution (Inr (Abs_st (SBot, SBot, [(''G'', SPos)])))) ''GH'' = SPos"
  unfolding fctx_seed_clean_solution_def fctx_seed_clean_eqs_def fctx_cfg_def fctx_prog_def
    kgen_ec_def kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

text \<open>
  \<^bold>\<open>Strictly sharper than the \<^const>\<open>side_env_cmp\<close> baseline.\<close>  Where interpretation 1's
  observation read of \<open>G\<close> at each call site is \<^const>\<open>SNonNeg\<close>
  (\<open>fctx_caller_read_G_imprecise\<close> at 4, \<open>fctx_caller_read_G_imprecise7\<close> at 7 --- the
  join of both \<open>G\<close>-writes), the seeded-clean caller \<^emph>\<open>local\<close> read is the point
  \<^const>\<open>SZero\<close> at call 4 and \<^const>\<open>SPos\<close> at call 7, each strictly below
  \<^const>\<open>SNonNeg\<close>.  The seed makes the routing read exact; this is exactly the
  \<open>ENTER_MONO\<close>-enabling precision the obstruction study identified as missing.
\<close>

lemma fctx_seed_clean_caller_G_exact:
  "lookup_st (snd fctx_seed_clean_solution (Inl (4, bot::sign st))) ''G'' = SZero
   \<and> lookup_st (snd fctx_seed_clean_solution (Inl (7, bot::sign st))) ''G'' = SPos"
  unfolding fctx_seed_clean_solution_def fctx_seed_clean_eqs_def fctx_cfg_def fctx_prog_def
    kgen_ec_def kgen_combine_rread_def sign_etf_clean_st_def clean_edge_tree_st_def
    side_cfg_T_eff_cmp_seed_st_def by eval

theorem fctx_seed_clean_strictly_sharper:
  "lookup_st (snd fctx_seed_clean_solution (Inl (4, bot::sign st))) ''G'' = SZero
   \<and> lookup_st (snd fctx_seed_clean_solution (Inl (7, bot::sign st))) ''G'' = SPos
   \<and> lookup_st (snd fctx_solution (Inl (4, GOther)) \<squnion> snd fctx_solution (Inr GOther)) ''G'' = SNonNeg
   \<and> SZero < SNonNeg \<and> SPos < SNonNeg"
  using fctx_seed_clean_caller_G_exact fctx_caller_read_G_imprecise sign_strict_precision by simp

end
