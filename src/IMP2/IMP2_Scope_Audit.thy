theory IMP2_Scope_Audit
  imports IMP2_Proc
begin

section \<open>Audit witness: a source Scope resets outer locals\<close>

text \<open>
  Concrete evidence for the scope-reconciliation audit.  The source \<^const>\<open>Scope\<close> follows AFP
  IMP2's local-variable block: the bridge \<open>IMP2_Bridge_Cmd\<close> wraps every procedure body in
  \<open>Syntax.Scope\<close>, and its \<open>Scope\<close> case runs the body from \<^const>\<open>enter_state\<close> and recombines
  with \<^const>\<open>combine_states\<close>.  So entering a scope resets every non-global variable to 0, and
  leaving it keeps the body's globals while restoring the caller's locals (\<open><saved | body>\<close>).
  An outer local is therefore invisible inside a scope: a read yields 0, not the outer value.

  The program \<open>x := 5; Scope (y := x)\<close> makes this observable.  Inside the scope \<open>x\<close> reads as
  0, so \<open>y\<close> is assigned 0; on exit that local write is discarded and the whole program
  completes with store \<open>s0(x := 5)\<close> --- the scope has no net effect on the caller.
\<close>

abbreviation prog_x5 :: com where
  "prog_x5 \<equiv> Assign ''x'' (BaseN (AExp.N 5))"

abbreviation prog_scope :: com where
  "prog_scope \<equiv> Scope (Assign ''y'' (BaseN (AExp.V ''x'')))"

text \<open>Inside the scope, the reset entry store reads the outer local \<open>x\<close> as 0.\<close>
lemma scope_reads_outer_local_as_zero:
  "aval (BaseN (AExp.V ''x'')) (enter_state (s0(''x'' := 5))) = 0"
  by (simp add: enter_state_def is_global_def)

text \<open>Entering the scope resets locals: control reaches the scope body at
  \<open>enter_state (s0(x := 5))\<close>, saving the pre-scope store in a lexical frame.\<close>
lemma scope_audit_entry:
  "psteps \<Pi> (Seq prog_x5 prog_scope, s0, [])
     (Seq (Assign ''y'' (BaseN (AExp.V ''x''))) Restore,
      enter_state (s0(''x'' := 5)), [Frame (s0(''x'' := 5)) None LexicalFrame])"
proof -
  have e1: "pstep \<Pi> (prog_x5, s0, []) (SKIP, s0(''x'' := 5), [])"
  proof -
    have "pstep \<Pi> (prog_x5, s0, []) (SKIP, s0(''x'' := aval (BaseN (AExp.N 5)) s0), [])"
      by (rule pstep.Assign)
    thus ?thesis by simp
  qed
  have a: "pstep \<Pi> (Seq prog_x5 prog_scope, s0, []) (Seq SKIP prog_scope, s0(''x'' := 5), [])"
    by (rule Seq2[OF e1])
  have b: "pstep \<Pi> (Seq SKIP prog_scope, s0(''x'' := 5), []) (prog_scope, s0(''x'' := 5), [])"
    by (rule Seq1)
  have c: "pstep \<Pi> (prog_scope, s0(''x'' := 5), [])
     (Seq (Assign ''y'' (BaseN (AExp.V ''x''))) Restore,
      enter_state (s0(''x'' := 5)), [Frame (s0(''x'' := 5)) None LexicalFrame])"
    by (rule Scope)
  show ?thesis using a b c by (meson star.refl star.step)
qed

text \<open>The scope body then assigns \<open>y := 0\<close> (because \<open>x\<close> read as 0), and on exit the whole
  program completes with store \<open>s0(x := 5)\<close>: the local write to \<open>y\<close> is discarded and the
  reset of \<open>x\<close> is undone by the restore.\<close>
lemma scope_audit_completes:
  "psteps \<Pi> (Seq prog_x5 prog_scope, s0, []) (SKIP, s0(''x'' := 5), [])"
proof -
  let ?s1 = "s0(''x'' := 5)"
  let ?se = "enter_state ?s1"
  let ?sb = "?se(''y'' := 0)"
  let ?Fl = "Frame ?s1 None LexicalFrame"
  have body: "pstep \<Pi> (Seq (Assign ''y'' (BaseN (AExp.V ''x''))) Restore, ?se, [?Fl])
                       (Seq SKIP Restore, ?sb, [?Fl])"
  proof (rule Seq2)
    have "pstep \<Pi> (Assign ''y'' (BaseN (AExp.V ''x'')), ?se, [?Fl])
                  (SKIP, ?se(''y'' := aval (BaseN (AExp.V ''x'')) ?se), [?Fl])"
      by (rule Assign)
    thus "pstep \<Pi> (Assign ''y'' (BaseN (AExp.V ''x'')), ?se, [?Fl]) (SKIP, ?sb, [?Fl])"
      by (simp add: enter_state_def is_global_def)
  qed
  have seq1: "pstep \<Pi> (Seq SKIP Restore, ?sb, [?Fl]) (Restore, ?sb, [?Fl])"
    by (rule Seq1)
  have restore: "pstep \<Pi> (Restore, ?sb, [?Fl]) (SKIP, <?s1 | ?sb>, [])"
  proof -
    have "pstep \<Pi> (Restore, ?sb, [?Fl]) (SKIP, combine_assign None (?sb ret_var) (<?s1 | ?sb>), [])"
      by (rule RestoreStep)
    thus ?thesis by simp
  qed
  have net: "<?s1 | ?sb> = s0(''x'' := 5)"
    by (rule ext) (auto simp: enter_state_def is_global_def)
  have chain: "psteps \<Pi> (Seq (Assign ''y'' (BaseN (AExp.V ''x''))) Restore, ?se, [?Fl])
                        (SKIP, <?s1 | ?sb>, [])"
    using body seq1 restore by (meson star.refl star.step)
  have "psteps \<Pi> (Seq prog_x5 prog_scope, s0, []) (SKIP, <?s1 | ?sb>, [])"
    using scope_audit_entry chain by (rule star_trans)
  thus ?thesis using net by simp
qed

text \<open>The audit conclusion: reading an outer local inside a scope yields 0, not the outer
  value.  This is intentional and faithful to AFP IMP2 (the bridge depends on it), so the
  divergence from the flattening compiler must be reconciled on the CFG side, not by changing
  this semantics.  See \<open>docs/SCOPE_RECONCILIATION_DESIGN.md\<close>.\<close>

end

