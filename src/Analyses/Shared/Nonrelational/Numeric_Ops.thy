theory Numeric_Ops
  imports "Voblint_Exec.Exec_St_Restriction_Refinement"
begin

section \<open>Generic executable procedure entry\<close>

text \<open>
  Sign, Interval, Parity and \<open>int_dom\<close> each need an \<open>X_enter_st_for\<close> of identical
  shape modulo the domain's own \<open>aval_X\<close> and \<open>top\<close>: evaluate the actuals in the
  caller's state, reset the callee frame, bind the formals. \<open>numeric_ops\<close> packages
  those primitives so the construction is written once, mirroring \<open>Special_Ops\<close>'s
  record-of-primitives shape.

  \<open>n_bfilter\<close> is a field but has no construction over it: each domain applies it
  directly as its own \<open>branch_X_st_for\<close>, since a branch transfer *is* a backward
  filter and wrapping that in a generic constant would only rename it. It is
  carried here so a domain's primitives travel as one value, and so a domain
  whose branch transfer degenerates to the identity -- Parity's does -- supplies
  the identity rather than needing an option type, exactly as \<open>Special_Ops\<close> lets a
  domain supply a trivial primitive.
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
  n_bfilter :: "(vname => bool) => exp => bool => 'a resolved_st_q => 'a resolved_st_q"
  n_top     :: "'a"

definition generic_enter_st_for ::
    "'a::bot numeric_ops => (vname => bool) => call_info =>
       'a resolved_st_q => 'a resolved_st_q" where
  "generic_enter_st_for ops gs ci s =
     bind_formals_resolved_q gs (ci_formals ci)
       (map (\<lambda>e. n_aval ops e (fun_of_resolved_st_q_for gs s)) (ci_args ci))
       (enter_frame_D_resolved_q (n_top ops) s)"

end
