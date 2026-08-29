theory Numeric_Ops
  imports Exec_Refinement
begin

section \<open>Generic executable branch/enter construction\<close>

text \<open>
  Sign, Interval, and Parity each define their own \<open>branch_X_st_for\<close>
  (Sign/Interval only -- Parity's branch transfer is the identity, so it has
  none) and \<open>X_enter_st_for\<close> with an identical shape modulo the domain's own
  \<open>aval_X\<close>/\<open>bfilter_X_st\<close>/\<open>top\<close>. This theory captures that shared
  state-transformer structure once, mirroring \<open>Special_Ops\<close>'s
  record-of-primitives shape: each domain supplies its own evaluator,
  backward filter, and top value, and the two generic constructions below
  are defined once against them.

  \<open>n_bfilter\<close> is not optional even for a domain like Parity whose branch
  transfer degenerates to the identity: \<open>generic_branch_st_for\<close> stays
  uniform by taking the identity function as Parity's own \<open>n_bfilter\<close>
  value, the same way \<open>Special_Ops\<close> lets a domain with nothing special
  to do supply a trivial primitive rather than needing an option type.
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

definition generic_branch_st_for ::
    "'a::bot numeric_ops => (vname => bool) => exp => bool =>
       'a resolved_st_q => 'a resolved_st_q" where
  "generic_branch_st_for ops gs b pol s = n_bfilter ops gs b pol s"

definition generic_enter_st_for ::
    "'a::bot numeric_ops => (vname => bool) => vname list => exp list =>
       'a resolved_st_q => 'a resolved_st_q" where
  "generic_enter_st_for ops gs xs es s =
     bind_formals_resolved_q gs xs
       (map (\<lambda>e. n_aval ops e (fun_of_resolved_st_q_for gs s)) es)
       (enter_frame_D_resolved_q (n_top ops) s)"

end
