theory Int_Warrowing
  imports
    "Voblint_Domain.Int_Lattice"
    "Voblint_Analysis_Sign.Sign_Warrowing"
    "Voblint_Analysis_Parity.Parity_Warrowing"
    "Voblint_Analysis_Interval.Interval_Warrowing"
    "Voblint_Analysis_Congruence.Congruence_Warrowing"
begin

section \<open>Composite widening and narrowing\<close>

text \<open>
  Purely componentwise, with no reduced-product refinement attached to
  either operation. Widening already matches Goblint's own \<open>~norefine:true\<close>
  choice for \<open>join\<close>/\<open>widen\<close>. Narrowing is a deliberate divergence from
  Goblint's \<open>IntDomTuple\<close>, forced by the vendored TD solver's interface:

  \<open>narrow_ge: b <= a ==> b <= a \<Delta> b\<close>
  \<open>narrow_le: b <= a ==> a \<Delta> b <= a\<close>

  Suppose componentwise narrowing gives \<open>b <= narrow_raw a b <= a\<close> and
  refinement is then applied on top, Goblint-style:
  \<open>refine mode (narrow_raw a b)\<close>. Refinement is reductive
  (\<open>Int_Refinement_Control.refine_reductive\<close>), so the result stays \<open><= narrow_raw a
  b <= a\<close> and \<open>narrow_le\<close> survives -- but there is no general reason for
  \<open>b <= refine mode (narrow_raw a b)\<close> to hold. Refinement may push the
  result strictly below \<open>b\<close>.

  The tempting escape is a stability argument: if \<open>b\<close> were already
  refinement-stable (\<open>refine mode b = b\<close>) and refinement is monotone, then
  \<open>b = refine mode b <= refine mode (narrow_raw a b)\<close> would follow from
  \<open>b <= narrow_raw a b\<close>. But that needs every value reaching narrowing to
  already be refinement-stable, and this carrier has no such invariant:
  \<open>Int_Backward\<close>'s own composite examples exercise values such as
  \<open>STop \<times> [-1,0] \<times> PEven \<times> top\<close>, where \<open>refine mode b ~= b\<close>. Join and
  widening deliberately do not refine either (mirroring Goblint's
  \<open>~norefine:true\<close> for both), so a value reaching narrowing by way of a
  widened solver state is not guaranteed stable. Building narrowing on an
  invariant the type does not enforce would be unsound at the class
  instance, not merely imprecise.

  Composite widening and narrowing therefore run no refinement at all,
  matching every other component's own choice (\<open>Sign_Warrowing\<close>,
  \<open>Interval_Warrowing\<close>, \<open>Parity_Warrowing\<close>, \<open>Congruence_Warrowing\<close>):
  each component widens/narrows on its own terms, and the composite record
  update runs no cross-component step afterward.
\<close>

text \<open>
  The lattice instance in \<open>Int_Lattice\<close> sits on the record scheme
  \<open>'a int_dom_scheme\<close>, so \<open>widen\<close>/\<open>narrow\<close> follow the same route and need
  \<open>warrowing\<close> on the scheme's \<open>more\<close> field too. \<open>unit\<close>, the \<open>more\<close> type of
  the closed \<open>int_dom\<close>, gets the trivial instance.
\<close>

instantiation unit :: warrowing
begin
definition widen_unit :: "unit => unit => unit" where "(a \<nabla> b) = ()"
definition narrow_unit :: "unit => unit => unit" where "(a \<Delta> b) = ()"
instance by intro_classes simp_all
end

instantiation int_dom_ext :: ("{bounded_lattice, warrowing}") warrowing
begin

definition widen_int_dom_ext :: "'a int_dom_scheme => 'a int_dom_scheme => 'a int_dom_scheme" where
  "((a :: 'a int_dom_scheme) \<nabla> b) =
     int_dom.extend
       (int_dom.truncate
         (a\<lparr>
           int_sign := ((int_sign a) \<nabla> (int_sign b)),
           int_ivl := ((int_ivl a) \<nabla> (int_ivl b)),
           int_parity := ((int_parity a) \<nabla> (int_parity b)),
           int_congruence := ((int_congruence a) \<nabla> (int_congruence b))
         \<rparr>))
       ((int_dom.more a) \<nabla> (int_dom.more b))"

definition narrow_int_dom_ext :: "'a int_dom_scheme => 'a int_dom_scheme => 'a int_dom_scheme" where
  "((a :: 'a int_dom_scheme) \<Delta> b) =
     int_dom.extend
       (int_dom.truncate
         (a\<lparr>
           int_sign := ((int_sign a) \<Delta> (int_sign b)),
           int_ivl := ((int_ivl a) \<Delta> (int_ivl b)),
           int_parity := ((int_parity a) \<Delta> (int_parity b)),
           int_congruence := ((int_congruence a) \<Delta> (int_congruence b))
         \<rparr>))
       ((int_dom.more a) \<Delta> (int_dom.more b))"

lemma int_dom_extend_truncate_select [simp]:
  "int_sign (int_dom.extend (int_dom.truncate r) m) = int_sign r"
  "int_ivl (int_dom.extend (int_dom.truncate r) m) = int_ivl r"
  "int_parity (int_dom.extend (int_dom.truncate r) m) = int_parity r"
  "int_congruence (int_dom.extend (int_dom.truncate r) m) = int_congruence r"
  "int_dom.more (int_dom.extend (int_dom.truncate r) m) = m"
  by (simp_all add: int_dom.defs)

instance proof intro_classes
  fix a b :: "'a int_dom_scheme"
  assume ba: "b <= a"
  have hb: "int_sign b <= int_sign a" "int_ivl b <= int_ivl a"
           "int_parity b <= int_parity a" "int_congruence b <= int_congruence a"
           "int_dom.more b <= int_dom.more a"
    using ba by (simp_all add: less_eq_int_dom_ext_def)
  have s: "int_sign b <= ((int_sign a) \<Delta> (int_sign b))"
    by (rule narrow_ge[OF hb(1)])
  have i: "int_ivl b <= ((int_ivl a) \<Delta> (int_ivl b))"
    by (rule narrow_ge[OF hb(2)])
  have p: "int_parity b <= ((int_parity a) \<Delta> (int_parity b))"
    by (rule narrow_ge[OF hb(3)])
  have c: "int_congruence b <= ((int_congruence a) \<Delta> (int_congruence b))"
    by (rule narrow_ge[OF hb(4)])
  have m: "int_dom.more b <= ((int_dom.more a) \<Delta> (int_dom.more b))"
    by (rule narrow_ge[OF hb(5)])
  show "b <= (a \<Delta> b)"
    unfolding narrow_int_dom_ext_def less_eq_int_dom_ext_def
    using s i p c m by simp
next
  fix a b :: "'a int_dom_scheme"
  assume ba: "b <= a"
  have hb: "int_sign b <= int_sign a" "int_ivl b <= int_ivl a"
           "int_parity b <= int_parity a" "int_congruence b <= int_congruence a"
           "int_dom.more b <= int_dom.more a"
    using ba by (simp_all add: less_eq_int_dom_ext_def)
  have s: "((int_sign a) \<Delta> (int_sign b)) <= int_sign a"
    by (rule narrow_le[OF hb(1)])
  have i: "((int_ivl a) \<Delta> (int_ivl b)) <= int_ivl a"
    by (rule narrow_le[OF hb(2)])
  have p: "((int_parity a) \<Delta> (int_parity b)) <= int_parity a"
    by (rule narrow_le[OF hb(3)])
  have c: "((int_congruence a) \<Delta> (int_congruence b)) <= int_congruence a"
    by (rule narrow_le[OF hb(4)])
  have m: "((int_dom.more a) \<Delta> (int_dom.more b)) <= int_dom.more a"
    by (rule narrow_le[OF hb(5)])
  show "(a \<Delta> b) <= a"
    unfolding narrow_int_dom_ext_def less_eq_int_dom_ext_def
    using s i p c m by simp
next
  fix a b :: "'a int_dom_scheme"
  have s: "int_sign a <= ((int_sign a) \<nabla> (int_sign b))"
    by (rule widen_ge1)
  have i: "int_ivl a <= ((int_ivl a) \<nabla> (int_ivl b))"
    by (rule widen_ge1)
  have p: "int_parity a <= ((int_parity a) \<nabla> (int_parity b))"
    by (rule widen_ge1)
  have c: "int_congruence a <= ((int_congruence a) \<nabla> (int_congruence b))"
    by (rule widen_ge1)
  have m: "int_dom.more a <= ((int_dom.more a) \<nabla> (int_dom.more b))"
    by (rule widen_ge1)
  show "a <= (a \<nabla> b)"
    unfolding widen_int_dom_ext_def less_eq_int_dom_ext_def
    using s i p c m by simp
next
  fix a b :: "'a int_dom_scheme"
  have s: "int_sign b <= ((int_sign a) \<nabla> (int_sign b))"
    by (rule widen_ge2)
  have i: "int_ivl b <= ((int_ivl a) \<nabla> (int_ivl b))"
    by (rule widen_ge2)
  have p: "int_parity b <= ((int_parity a) \<nabla> (int_parity b))"
    by (rule widen_ge2)
  have c: "int_congruence b <= ((int_congruence a) \<nabla> (int_congruence b))"
    by (rule widen_ge2)
  have m: "int_dom.more b <= ((int_dom.more a) \<nabla> (int_dom.more b))"
    by (rule widen_ge2)
  show "b <= (a \<nabla> b)"
    unfolding widen_int_dom_ext_def less_eq_int_dom_ext_def
    using s i p c m by simp
qed

end

section \<open>Numeric domain instance\<close>

text \<open>\<open>numeric_domain\<close> extends \<open>executable_domain\<close>, which includes the solver's
  \<open>warrowing\<close>, so the composite instance asks the same of the \<open>more\<close> field
  as the widening and narrowing above.\<close>

instantiation int_dom_ext ::
  ("{bounded_lattice, warrowing}") numeric_domain
begin

definition gamma_abs_int_dom_ext [simp]:
  "\<gamma> (d :: 'a int_dom_scheme) = gamma_int_dom d"

definition is_empty_int_dom_ext [simp]:
  "is_empty (d :: 'a int_dom_scheme) = is_bottom_int_dom d"

definition to_string_int_dom_ext [simp]:
  "to_string (d :: 'a int_dom_scheme) = string_of_int_dom d"

instance
proof intro_classes
  show "\<gamma> (bot :: 'a int_dom_scheme) = {}"
    by (simp add: gamma_int_dom_def bot_int_dom_ext_def
          bot_sign_def bot_ivl_def bot_parity_def)
next
  show "\<gamma> (top :: 'a int_dom_scheme) = UNIV"
    by (simp add: gamma_int_dom_def top_int_dom_ext_def
          gamma_sign_top gamma_ivl_top top_ivl_def gamma_parity_top)
next
  fix a b :: "'a int_dom_scheme"
  show "a \<le> b \<Longrightarrow> \<gamma> a \<subseteq> \<gamma> b"
    by (simp add: gamma_int_dom_mono)
next
  fix a :: "'a int_dom_scheme"
  show "is_empty a \<longleftrightarrow> \<gamma> a = {}"
    by (simp add: is_bottom_int_dom_correct)
qed

end

end
