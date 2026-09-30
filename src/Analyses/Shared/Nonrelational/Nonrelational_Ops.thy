theory Nonrelational_Ops
  imports
    Special_Ops
    Exec_Backward
    "Voblint_Framework.DG_Local_State_Spec"
    "Voblint_Exec.Default_St_Restriction_Refinement"
begin

unbundle default_st_syntax

section \<open>The primitives one abstract value per variable is built from\<close>

text \<open>
  Say what an expression evaluates to, which comparisons the domain decides, how
  a guard refines its operands, how the two special calls combine two values,
  and every edge of a compiled graph is determined; the whole-value element is
  the class \<^const>\<open>top\<close>. \<open>nonrelational_ops\<close> is that bundle of primitive choices, written
  once per domain. Everything else is derived from it: the guard filter on the
  executable store here, the abstract branch and the transfer in
  \<open>Nonrelational_Transfer\<close>, which certifies one such bundle.

  Two constructions follow from it here. \<open>generic_enter_st_for\<close> is procedure
  entry on the executable store: evaluate the actuals in the caller's state,
  reset the callee frame to the whole-value element, bind the formals.
  \<open>generic_tf_st_for\<close> is the per-edge executable step, and
  \<open>generic_tf_st_for_commute\<close> says it agrees with the abstract dispatcher
  \<open>generic_tf_abs\<close> on the function the executable store represents, provided the guard
  filter commutes with the abstract branch on the state at hand.

  \<open>generic_tf_abs\<close> takes the abstract branch as a separate argument so this
  commutation lemma needs no soundness locale. For a certified bundle the branch
  is not an independent choice: \<open>sound_nonrelational_ops\<close> instantiates
  it with the backward branch of \<open>n_aval\<close> and \<open>n_refine\<close> and discharges the
  guard obligation once, generically.
\<close>

text \<open>
  The bundle is constrained to \<open>'a::{bot, top}\<close> and the executable step to
  \<open>'a::executable_domain\<close>, never \<open>'a::numeric_domain\<close>. \<open>numeric_domain\<close> fixes
  \<open>gamma\<close> as a class operation, and code generation for a definition at that
  sort must resolve \<open>gamma\<close>'s code equation for the concrete type even though
  nothing here calls it. \<open>ivl\<close>'s \<open>gamma_ivl\<close> has no well-sorted code equation
  (\<open>int\<close> is not of sort \<open>enum\<close>), so that unused obligation breaks unrelated
  \<open>by eval\<close> proofs downstream.
\<close>

text \<open>
  The comparisons a domain decides, each answering \<open>None\<close> when it cannot tell.
\<close>

record 'a query_ops =
  q_less :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"
  q_eq   :: "'a \<Rightarrow> 'a \<Rightarrow> bool option"

record ('a::"{bot, top}") nonrelational_ops =
  n_aval    :: "exp => (vname => 'a) => 'a"
  n_query   :: "'a query_ops"
  n_refine  :: "'a refine_ops"
  n_special :: "'a special_ops"

text \<open>
  The guard filter on the executable store is derived from the evaluator and the
  refinement operations, never supplied: the bundle determines it.
\<close>

abbreviation n_bfilter ::
  "'a::executable_domain nonrelational_ops
   \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> exp \<Rightarrow> bool \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st" where
  "n_bfilter ops \<equiv> branch_st_with (n_aval ops) (n_refine ops)"

subsection \<open>Procedure entry\<close>

definition generic_enter_st_for ::
    "'a::{bot, top} nonrelational_ops => (vname => bool) => call_info =>
       'a default_st => 'a default_st" where
  "generic_enter_st_for ops \<G> ci s =
     bind_formals_default_st \<G> (ci_formals ci)
       (map (\<lambda>e. n_aval ops e (default_st_to_fun \<G> s)) (ci_args ci))
       (enter_frame_D_default_st top s)"

subsection \<open>The per-edge step, on both stores\<close>

fun generic_tf_st_for ::
    "'a::executable_domain nonrelational_ops => (vname => bool) => edge_action =>
       'a default_st => 'a default_st" where
    "generic_tf_st_for ops \<G> EA_Nop s = s"
  | "generic_tf_st_for ops \<G> (EA_Assign x a) s =
       s\<langle>location_of \<G> x := n_aval ops a (default_st_to_fun \<G> s)\<rangle>"
  | "generic_tf_st_for ops \<G> (EA_Special sc x) s =
       s\<langle>location_of \<G> x :=
         (case sc of
            Nondet_Int => top
          | Min a b => special_min (n_special ops)
                         (n_aval ops a (default_st_to_fun \<G> s))
                         (n_aval ops b (default_st_to_fun \<G> s))
          | Max a b => special_max (n_special ops)
                         (n_aval ops a (default_st_to_fun \<G> s))
                         (n_aval ops b (default_st_to_fun \<G> s)))\<rangle>"
  | "generic_tf_st_for ops \<G> (EA_Assume b) s = n_bfilter ops \<G> b True s"
  | "generic_tf_st_for ops \<G> (EA_AssumeNot b) s = n_bfilter ops \<G> b False s"
  | "generic_tf_st_for ops \<G> (EA_Body p) s = s"
  | "generic_tf_st_for ops \<G> (EA_Ret None p) s = s"
  | "generic_tf_st_for ops \<G> (EA_Ret (Some a) p) s =
       s\<langle>location_of \<G> ret_var := n_aval ops a (default_st_to_fun \<G> s)\<rangle>"
  | "generic_tf_st_for ops \<G> (EA_Check l cnd) s = s"

definition generic_tf_abs ::
    "'a::{bot, top} nonrelational_ops => (exp => bool => 'a abs_state => 'a abs_state) =>
       edge_action => 'a abs_state => 'a abs_state" where
  "generic_tf_abs ops br =
     local_spec_step
       (\<lambda>sigma. sigma)
       (\<lambda>x a sigma. sigma(x := n_aval ops a sigma))
       (\<lambda>sc x sigma. sigma(x := (case sc of
            Nondet_Int => top
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
        Nondet_Int => top
      | Min a b => special_min (n_special ops) (n_aval ops a sigma) (n_aval ops b sigma)
      | Max a b => special_max (n_special ops) (n_aval ops a sigma) (n_aval ops b sigma)))"
  "generic_tf_abs ops br (EA_Assume b) = br b True"
  "generic_tf_abs ops br (EA_AssumeNot b) = br b False"
  "generic_tf_abs ops br (EA_Body p) sigma = sigma"
  "generic_tf_abs ops br (EA_Ret None p) sigma = sigma"
  "generic_tf_abs ops br (EA_Ret (Some a) p) sigma = sigma(ret_var := n_aval ops a sigma)"
  "generic_tf_abs ops br (EA_Check l cnd) sigma = sigma"
  by (simp_all add: generic_tf_abs_def)

text \<open>
  Every case but the guard rewrites by \<^const>\<open>default_st_to_fun\<close>'s own
  update equation, which is what leaves the guard as the only obligation an
  instance still has to discharge.
\<close>

theorem generic_tf_st_for_commute:
  fixes ops :: "'a::executable_domain nonrelational_ops"
  assumes branch:
    "\<And>b pol. default_st_to_fun \<G> (n_bfilter ops \<G> b pol s) =
               br b pol (default_st_to_fun \<G> s)"
  shows
    "default_st_to_fun \<G> (generic_tf_st_for ops \<G> a s) =
     generic_tf_abs ops br a (default_st_to_fun \<G> s)"
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
  case (EA_Check l cnd)
  then show ?thesis by simp
qed

unbundle no default_st_syntax

end
