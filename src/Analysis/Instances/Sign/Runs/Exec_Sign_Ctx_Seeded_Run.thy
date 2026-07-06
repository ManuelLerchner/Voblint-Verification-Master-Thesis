theory Exec_Sign_Ctx_Seeded_Run
  imports Exec_Sign_Ctx_Gen_Run
begin

section \<open>Frame-entry context seeding: executable precision witness (sign)\<close>

text \<open>
  The generator \<^const>\<open>side_cfg_T_eff_ctx_seeded_st\<close> seeds a frame-entry node's
  locals from the call context (\<open>ent\<close>) rather than resetting them through the
  uniform \<^const>\<open>EA_Enter\<close> transfer.  With \<open>ent = id\<close> and the Goblint context
  \<open>ec ctx sc = sc\<close> (full caller state), a callee that reads a caller-set local is
  analysed per-context: the two call sites stay separate where the monovariant
  generator collapses them to \<^const>\<open>STop\<close>.

  \<^bold>\<open>Unsound by construction.\<close>  This per-context split does not over-approximate
  the concrete semantics; it is kept only as an illustration of the
  local-context failure mode.  See the closing note for the argument.
\<close>

subsection \<open>Runnability on the single-call program\<close>

definition gseed_eqs1 :: "(pp \<times> sign st, unit, sign st) eqsT" where
  "gseed_eqs1 = side_cfg_T_eff_ctx_seeded_st
                  (\<lambda>c cc ex. unit_combine_tree_ctx_st sign_ctx_ec cc ex c)
                  id
                  gctx_cfg sign_etf_st bot cinit_sign_st ()"

definition gseed_solution1 ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + unit \<Rightarrow> sign st)" where
  "gseed_solution1 = TD_side_always_join_Interp_solve gseed_eqs1 (cfg_exit gctx_cfg, bot)"

text \<open>The seeded generator code-generates and runs through the real side solver.\<close>

lemma gseed_run1: "lookup_st (snd gseed_solution1 (Inr ())) ''G'' = SZero"
  by eval

subsection \<open>Two-call program: callee reads a caller-set local\<close>

text \<open>
  \<open>f\<close> writes the global \<open>G\<close> from the local \<open>x\<close>; \<open>main\<close> calls it twice, once
  with \<open>x = 0\<close> and once with \<open>x = 1\<close>.  Under the reset (monovariant) entry the
  callee's \<open>x\<close> is \<^const>\<open>STop\<close>, so \<open>G\<close> becomes \<^const>\<open>STop\<close>; under the seeded
  entry the two activations carry their caller context and stay separate.
\<close>

definition tcseed_prog :: imp_prog where
  "tcseed_prog = \<lbrakk>
     int G;

     void f() {
       G := x
     }
     void main() {
       x := 0;
       f();
       x := 1;
       f()
     }
   \<rbrakk>"

definition tcseed_cfg :: cfg where
  "tcseed_cfg = compile_prog (prog_table tcseed_prog) (prog_procs tcseed_prog) (prog_main tcseed_prog)"

text \<open>
  Context = the local part of the caller state at the call.  With only \<open>x\<close> local
  in \<open>main\<close>, the two call sites give the two clean contexts \<^term>\<open>c0\<close> / \<^term>\<open>c1\<close>.
\<close>

definition seed_ec :: "sign st \<Rightarrow> sign st \<Rightarrow> sign st" where
  "seed_ec ctx sc = restrict_local_st sc"

definition tcseed_eqs :: "(pp \<times> sign st, unit, sign st) eqsT" where
  "tcseed_eqs = side_cfg_T_eff_ctx_seeded_st
                  (\<lambda>c cc ex. unit_combine_tree_ctx_st seed_ec cc ex c)
                  id
                  tcseed_cfg sign_etf_st bot cinit_sign_st ()"

definition tcseed_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + unit \<Rightarrow> sign st)" where
  "tcseed_solution = TD_side_always_join_Interp_solve tcseed_eqs (cfg_exit tcseed_cfg, bot)"

definition tcmono_eqs :: "(pp \<times> sign st, unit, sign st) eqsT" where
  "tcmono_eqs = side_cfg_T_eff_ctx_st
                  (\<lambda>c cc ex. unit_combine_tree_ctx_st seed_ec cc ex c)
                  tcseed_cfg sign_etf_st bot cinit_sign_st ()"

definition tcmono_solution ::
  "(pp \<times> sign st) set \<times> ((pp \<times> sign st) + unit \<Rightarrow> sign st)" where
  "tcmono_solution = TD_side_always_join_Interp_solve tcmono_eqs (cfg_exit tcseed_cfg, bot)"

subsection \<open>The precision payoff, machine-checked\<close>

text \<open>
  Program point \<^term>\<open>0::pp\<close> is \<open>f\<close>'s frame-entry node: it occurs in the solved
  variable set only under the two callee contexts, never under the bottom
  (\<open>main\<close>) context.  The observable is the callee local \<open>x\<close> there, gathered over
  every context the solver materialised at that point.
\<close>

definition fbody_pp :: pp where "fbody_pp = 0"

definition seed_fbody_x :: "sign set" where
  "seed_fbody_x = (\<lambda>qc. lookup_st (snd tcseed_solution (Inl qc)) ''x'')
                    ` {qc \<in> fst tcseed_solution. fst qc = fbody_pp}"

definition mono_fbody_x :: "sign set" where
  "mono_fbody_x = (\<lambda>qc. lookup_st (snd tcmono_solution (Inl qc)) ''x'')
                    ` {qc \<in> fst tcmono_solution. fst qc = fbody_pp}"

text \<open>
  Seeded: the two activations keep their caller-set local, \<open>x \<in> {SZero, SPos}\<close>.
  Monovariant: the \<^const>\<open>EA_Enter\<close> reset forces \<open>x = STop\<close> at both -- the entry
  local information the seeding recovers.
\<close>

lemma seed_fbody_x_eval: "seed_fbody_x = {SZero, SPos}"
  unfolding seed_fbody_x_def fbody_pp_def by eval

lemma mono_fbody_x_eval: "mono_fbody_x = {STop}"
  unfolding mono_fbody_x_def fbody_pp_def by eval

text \<open>
  The executable precision payoff, sealed by the code generator: at the callee
  frame entry the seeded analysis is non-trivial and \<^emph>\<open>strictly\<close> below the
  monovariant value in every context -- context sensitivity recovers precision
  the \<^const>\<open>EA_Enter\<close> reset destroys.  (A precision statement about the solved
  values, exactly like the hand-built \<open>fctx_context_strictly_more_precise\<close>; it is
  not a soundness claim for arbitrary \<open>ent\<close>.)
\<close>

theorem seeded_strictly_more_precise:
  "seed_fbody_x = {SZero, SPos}
   \<and> mono_fbody_x = {STop}
   \<and> (\<forall>s \<in> seed_fbody_x. \<forall>m \<in> mono_fbody_x. s < m)"
  unfolding seed_fbody_x_def mono_fbody_x_def fbody_pp_def by eval

text \<open>
  \<^bold>\<open>Why this precision is unsound.\<close>  \<^const>\<open>enter_state\<close> resets every local to
  \<open>0\<close>, so a concrete activation of \<open>f\<close> enters with \<open>x = 0\<close> at both call sites and
  \<open>G := x\<close> writes \<open>0\<close> each time.  The monovariant value \<^const>\<open>STop\<close> soundly
  over-approximates that; the seeded per-context \<open>{SZero, SPos}\<close> does not --- it
  reconstructs a caller local the callee never receives, because \<open>ent = id\<close>
  seeds locals that the \<^const>\<open>EA_Enter\<close> reset erases.  Hence
  \<open>seeded_strictly_more_precise\<close> is a statement about the solver's \<^emph>\<open>computed\<close>
  output only; it is \<^emph>\<open>not\<close> a soundness claim, and the configuration it
  exercises is unsound.

  Caller locals are the wrong context channel: procedures are parameterless,
  parameters pass through globals, and only the global state survives
  \<^const>\<open>enter_state\<close>.  The sound form of per-context precision reads globals per
  context through \<open>side_env_cmp\<close> (\<open>Global_Cmp_Read\<close>) and rests on \<open>CMP_SOUND\<close> in
  \<open>post_fixpoint_sound_at_ctx_semantic_cmp_final\<close>; the collecting-level witness
  with a global context is \<open>Example_Entry_Store_Context_Precision\<close>.
\<close>

end
