theory Numeric_Ops
  imports
    Special_Ops
    "Voblint_Framework.DG_Local_State_Spec"
    "Voblint_Exec.Exec_St_Restriction_Refinement"
begin

section \<open>The primitives one abstract value per variable is built from\<close>

text \<open>
  Say what an expression evaluates to, what the whole-value element is, how the
  two special calls combine two values, and how a guard filters the executable
  store the solver actually holds --- and every edge of a compiled graph is
  already determined up to the guard. \<open>numeric_ops\<close> is that bundle, written
  once per domain and read by both layers: the abstract transfer in
  \<open>Nonrelational_Transfer\<close>, which fixes one such bundle, and the executable
  mirror below.

  Two constructions follow from it here. \<open>generic_enter_st_for\<close> is procedure
  entry on the executable store: evaluate the actuals in the caller's state,
  reset the callee frame to the whole-value element, bind the formals.
  \<open>generic_tf_st_for\<close> is the per-edge executable step, and
  \<open>generic_tf_st_for_commute\<close> says it agrees with \<open>generic_tf_abs\<close> --- the
  abstract dispatcher the same bundle determines --- once the executable store
  is read back. Only the guard case needs anything further: \<open>n_bfilter\<close> must
  commute with the abstract branch on the state at hand.

  The abstract branch is the one primitive the bundle does not carry, and the
  reason is code generation. A bundle is a single value, so anything in it is
  serialized wherever the bundle is; an abstract branch runs through
  \<open>is_empty_state\<close>, which quantifies over \<^typ>\<open>vname\<close> and therefore has no
  code equation by design. It is passed alongside the bundle instead --- as
  \<open>generic_tf_abs\<close>'s second argument, and as \<open>nonrelational_transfer\<close>'s one
  remaining loose parameter. \<open>n_bfilter\<close> is not its image either way: the
  abstract branch works on a function from variable to value, the executable
  one on \<^typ>\<open>'a resolved_st_q\<close>, and neither is computable from the other. A
  domain whose branch degenerates to the identity --- Parity's does --- supplies
  the identity for both rather than needing an option type, exactly as
  \<^theory>\<open>Voblint_Nonrelational.Special_Ops\<close> lets a domain supply a trivial
  primitive.
\<close>

text \<open>
  Constrained to \<open>'a::bot\<close> only -- exactly what \<^const>\<open>fun_of_resolved_st_q_for\<close>/
  \<^const>\<open>bind_formals_resolved_q\<close>/\<^const>\<open>enter_frame_D_resolved_q\<close> actually
  need -- rather than \<open>'a::sound_domain\<close>. This is deliberate, not merely
  weaker-than-necessary: \<open>sound_domain\<close> also fixes \<open>gamma\<close> as a class
  operation, and code generation for a \<open>'a::sound_domain\<close>-constrained
  definition must resolve every fixed operation's code equation for the
  concrete type, including \<open>gamma\<close>, even though nothing here ever calls it.
  \<open>ivl\<close>'s own \<open>gamma_ivl\<close> code equation is not actually well-sorted
  (\<open>int\<close> is not of sort \<open>enum\<close>), so pulling in that unused obligation broke
  unrelated \<open>by eval\<close> proofs downstream that never triggered it before.
  This theory is purely about executable structure, not soundness, so it
  has no reason to need \<open>gamma\<close> at all.
\<close>

record 'a::bot numeric_ops =
  n_aval    :: "exp => (vname => 'a) => 'a"
  n_special :: "'a special_ops"
  n_bfilter :: "(vname => bool) => exp => bool => 'a resolved_st_q => 'a resolved_st_q"
  n_top     :: "'a"

subsection \<open>Procedure entry\<close>

definition generic_enter_st_for ::
    "'a::bot numeric_ops => (vname => bool) => call_info =>
       'a resolved_st_q => 'a resolved_st_q" where
  "generic_enter_st_for ops \<G> ci s =
     bind_formals_resolved_q \<G> (ci_formals ci)
       (map (\<lambda>e. n_aval ops e (fun_of_resolved_st_q_for \<G> s)) (ci_args ci))
       (enter_frame_D_resolved_q (n_top ops) s)"

subsection \<open>The per-edge step, on both stores\<close>

fun generic_tf_st_for ::
    "'a::bot numeric_ops => (vname => bool) => edge_action =>
       'a resolved_st_q => 'a resolved_st_q" where
    "generic_tf_st_for ops \<G> EA_Nop s = s"
  | "generic_tf_st_for ops \<G> (EA_Assign x a) s =
       update_resolved_st_q s (location_of \<G> x)
         (n_aval ops a (fun_of_resolved_st_q_for \<G> s))"
  | "generic_tf_st_for ops \<G> (EA_Special sc x) s =
       update_resolved_st_q s (location_of \<G> x)
         (case sc of
            Nondet_Int => n_top ops
          | Min a b => special_min (n_special ops)
                         (n_aval ops a (fun_of_resolved_st_q_for \<G> s))
                         (n_aval ops b (fun_of_resolved_st_q_for \<G> s))
          | Max a b => special_max (n_special ops)
                         (n_aval ops a (fun_of_resolved_st_q_for \<G> s))
                         (n_aval ops b (fun_of_resolved_st_q_for \<G> s)))"
  | "generic_tf_st_for ops \<G> (EA_Assume b) s = n_bfilter ops \<G> b True s"
  | "generic_tf_st_for ops \<G> (EA_AssumeNot b) s = n_bfilter ops \<G> b False s"
  | "generic_tf_st_for ops \<G> (EA_Body p) s = s"
  | "generic_tf_st_for ops \<G> (EA_Ret None p) s = s"
  | "generic_tf_st_for ops \<G> (EA_Ret (Some a) p) s =
       update_resolved_st_q s (location_of \<G> ret_var)
         (n_aval ops a (fun_of_resolved_st_q_for \<G> s))"
  | "generic_tf_st_for ops \<G> (EA_Check cnd) s = s"

definition generic_tf_abs ::
    "'a::bot numeric_ops => (exp => bool => 'a abs_state => 'a abs_state) =>
       edge_action => 'a abs_state => 'a abs_state" where
  "generic_tf_abs ops br =
     local_spec_step
       (\<lambda>sigma. sigma)
       (\<lambda>x a sigma. sigma(x := n_aval ops a sigma))
       (\<lambda>sc x sigma. sigma(x := (case sc of
            Nondet_Int => n_top ops
          | Min a b => special_min (n_special ops) (n_aval ops a sigma) (n_aval ops b sigma)
          | Max a b => special_max (n_special ops) (n_aval ops a sigma) (n_aval ops b sigma))))
       br
       (\<lambda>p sigma. sigma)
       (\<lambda>eo p sigma. case eo of None => sigma | Some a => sigma(ret_var := n_aval ops a sigma))
       (\<lambda>evt sigma. sigma)"

lemma generic_tf_abs_simps [simp]:
  "generic_tf_abs ops br EA_Nop sigma = sigma"
  "generic_tf_abs ops br (EA_Assign x a) sigma = sigma(x := n_aval ops a sigma)"
  "generic_tf_abs ops br (EA_Special sc x) sigma =
     sigma(x := (case sc of
        Nondet_Int => n_top ops
      | Min a b => special_min (n_special ops) (n_aval ops a sigma) (n_aval ops b sigma)
      | Max a b => special_max (n_special ops) (n_aval ops a sigma) (n_aval ops b sigma)))"
  "generic_tf_abs ops br (EA_Assume b) = br b True"
  "generic_tf_abs ops br (EA_AssumeNot b) = br b False"
  "generic_tf_abs ops br (EA_Body p) sigma = sigma"
  "generic_tf_abs ops br (EA_Ret None p) sigma = sigma"
  "generic_tf_abs ops br (EA_Ret (Some a) p) sigma = sigma(ret_var := n_aval ops a sigma)"
  "generic_tf_abs ops br (EA_Check cnd) sigma = sigma"
  by (simp_all add: generic_tf_abs_def)

text \<open>
  Every case but the guard rewrites by \<^const>\<open>fun_of_resolved_st_q_for\<close>'s own
  update equation, which is what leaves the guard as the only obligation an
  instance still has to discharge.
\<close>

theorem generic_tf_st_for_commute:
  fixes ops :: "'a::bot numeric_ops"
  assumes branch:
    "\<And>b pol. fun_of_resolved_st_q_for \<G> (n_bfilter ops \<G> b pol s) =
               br b pol (fun_of_resolved_st_q_for \<G> s)"
  shows
    "fun_of_resolved_st_q_for \<G> (generic_tf_st_for ops \<G> a s) =
     generic_tf_abs ops br a (fun_of_resolved_st_q_for \<G> s)"
proof (cases a)
  case EA_Nop
  then show ?thesis by simp
next
  case (EA_Assign x e)
  then show ?thesis by simp
next
  case (EA_Special sc x)
  then show ?thesis by (cases sc) simp_all
next
  case (EA_Assume b)
  then show ?thesis by (simp add: branch)
next
  case (EA_AssumeNot b)
  then show ?thesis by (simp add: branch)
next
  case (EA_Body p)
  then show ?thesis by simp
next
  case (EA_Ret eo p)
  then show ?thesis by (cases eo) simp_all
next
  case (EA_Check cnd)
  then show ?thesis by simp
qed

end
