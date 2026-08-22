theory Int_Warrowing
  imports Int_Domain Interval_Warrowing Congruence_Warrowing "TD.Update_rules"
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
  (\<open>Int_Refinement.refine_reductive\<close>), so the result stays \<open><= narrow_raw a
  b <= a\<close> and \<open>narrow_le\<close> survives -- but there is no general reason for
  \<open>b <= refine mode (narrow_raw a b)\<close> to hold. Refinement may push the
  result strictly below \<open>b\<close>.

  The tempting escape is a stability argument: if \<open>b\<close> were already
  refinement-stable (\<open>refine mode b = b\<close>) and refinement is monotone, then
  \<open>b = refine mode b <= refine mode (narrow_raw a b)\<close> would follow from
  \<open>b <= narrow_raw a b\<close>. But that needs every value reaching narrowing to
  already be refinement-stable, and this carrier has no such invariant:
  \<open>Int_Backward.thy\<close>'s own composite examples exercise values such as
  \<open>STop \<times> [-1,0] \<times> PEven \<times> top\<close>, where \<open>refine mode b ~= b\<close>. Join and
  widening deliberately do not refine either (mirroring Goblint's
  \<open>~norefine:true\<close> for both), so a value reaching narrowing by way of a
  widened solver state is not guaranteed stable. Building narrowing on an
  invariant the type does not enforce would be unsound at the class
  instance, not merely imprecise.

  Composite widening and narrowing therefore run no refinement at all,
  matching every other component's own choice (\<open>Sign_Lattice.thy\<close>,
  \<open>Interval_Warrowing.thy\<close>, \<open>Parity_Domain.thy\<close>, \<open>Congruence_Warrowing.thy\<close>):
  each component widens/narrows on its own terms, and the composite record
  update runs no cross-component step afterward.
\<close>

text \<open>
  The composite carrier's \<open>sound_domain\<close> instance (\<open>Int_Domain.thy\<close>) is
  registered on the extensible record scheme \<open>'a int_dom_scheme\<close>, not the
  closed \<open>int_dom\<close> type alias, so \<open>widen\<close>/\<open>narrow\<close> follow the same route:
  \<open>int_dom_record_lattice\<close> alone has no \<open>widen\<close>/\<open>narrow\<close> for the scheme's
  \<open>more\<close> field, so this bundles \<open>warrowing\<close> into the sort the record
  update needs and discharges it trivially for \<open>unit\<close>, matching that
  file's own \<open>instance unit :: int_dom_record_lattice\<close>.
\<close>

class int_dom_record_warrowing = int_dom_record_lattice + warrowing

instantiation unit :: warrowing
begin
definition widen_unit :: "unit => unit => unit" where "widen a b = ()"
definition narrow_unit :: "unit => unit => unit" where "narrow a b = ()"
instance by intro_classes simp_all
end

instance unit :: int_dom_record_warrowing ..

instantiation int_dom_ext :: (int_dom_record_warrowing) warrowing
begin

definition widen_int_dom_ext :: "'a int_dom_scheme => 'a int_dom_scheme => 'a int_dom_scheme" where
  "widen (a :: 'a int_dom_scheme) b =
     int_dom.extend
       (int_dom.truncate
         (a\<lparr>
           int_sign := widen (int_sign a) (int_sign b),
           int_ivl := widen (int_ivl a) (int_ivl b),
           int_parity := widen (int_parity a) (int_parity b),
           int_congruence := widen (int_congruence a) (int_congruence b)
         \<rparr>))
       (widen (int_dom.more a) (int_dom.more b))"

definition narrow_int_dom_ext :: "'a int_dom_scheme => 'a int_dom_scheme => 'a int_dom_scheme" where
  "narrow (a :: 'a int_dom_scheme) b =
     int_dom.extend
       (int_dom.truncate
         (a\<lparr>
           int_sign := narrow (int_sign a) (int_sign b),
           int_ivl := narrow (int_ivl a) (int_ivl b),
           int_parity := narrow (int_parity a) (int_parity b),
           int_congruence := narrow (int_congruence a) (int_congruence b)
         \<rparr>))
       (narrow (int_dom.more a) (int_dom.more b))"

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
  have s: "int_sign b <= narrow (int_sign a) (int_sign b)"
    by (rule narrow_ge[OF hb(1)])
  have i: "int_ivl b <= narrow (int_ivl a) (int_ivl b)"
    by (rule narrow_ge[OF hb(2)])
  have p: "int_parity b <= narrow (int_parity a) (int_parity b)"
    by (rule narrow_ge[OF hb(3)])
  have c: "int_congruence b <= narrow (int_congruence a) (int_congruence b)"
    by (rule narrow_ge[OF hb(4)])
  have m: "int_dom.more b <= narrow (int_dom.more a) (int_dom.more b)"
    by (rule narrow_ge[OF hb(5)])
  show "b <= narrow a b"
    unfolding narrow_int_dom_ext_def less_eq_int_dom_ext_def
    using s i p c m by simp
next
  fix a b :: "'a int_dom_scheme"
  assume ba: "b <= a"
  have hb: "int_sign b <= int_sign a" "int_ivl b <= int_ivl a"
           "int_parity b <= int_parity a" "int_congruence b <= int_congruence a"
           "int_dom.more b <= int_dom.more a"
    using ba by (simp_all add: less_eq_int_dom_ext_def)
  have s: "narrow (int_sign a) (int_sign b) <= int_sign a"
    by (rule narrow_le[OF hb(1)])
  have i: "narrow (int_ivl a) (int_ivl b) <= int_ivl a"
    by (rule narrow_le[OF hb(2)])
  have p: "narrow (int_parity a) (int_parity b) <= int_parity a"
    by (rule narrow_le[OF hb(3)])
  have c: "narrow (int_congruence a) (int_congruence b) <= int_congruence a"
    by (rule narrow_le[OF hb(4)])
  have m: "narrow (int_dom.more a) (int_dom.more b) <= int_dom.more a"
    by (rule narrow_le[OF hb(5)])
  show "narrow a b <= a"
    unfolding narrow_int_dom_ext_def less_eq_int_dom_ext_def
    using s i p c m by simp
next
  fix a b :: "'a int_dom_scheme"
  have s: "int_sign a <= widen (int_sign a) (int_sign b)"
    by (rule widen_ge1)
  have i: "int_ivl a <= widen (int_ivl a) (int_ivl b)"
    by (rule widen_ge1)
  have p: "int_parity a <= widen (int_parity a) (int_parity b)"
    by (rule widen_ge1)
  have c: "int_congruence a <= widen (int_congruence a) (int_congruence b)"
    by (rule widen_ge1)
  have m: "int_dom.more a <= widen (int_dom.more a) (int_dom.more b)"
    by (rule widen_ge1)
  show "a <= widen a b"
    unfolding widen_int_dom_ext_def less_eq_int_dom_ext_def
    using s i p c m by simp
next
  fix a b :: "'a int_dom_scheme"
  have s: "int_sign b <= widen (int_sign a) (int_sign b)"
    by (rule widen_ge2)
  have i: "int_ivl b <= widen (int_ivl a) (int_ivl b)"
    by (rule widen_ge2)
  have p: "int_parity b <= widen (int_parity a) (int_parity b)"
    by (rule widen_ge2)
  have c: "int_congruence b <= widen (int_congruence a) (int_congruence b)"
    by (rule widen_ge2)
  have m: "int_dom.more b <= widen (int_dom.more a) (int_dom.more b)"
    by (rule widen_ge2)
  show "b <= widen a b"
    unfolding widen_int_dom_ext_def less_eq_int_dom_ext_def
    using s i p c m by simp
qed

end

instance int_dom_ext :: (int_dom_record_warrowing) bounded_warrowing ..

end
