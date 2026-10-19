#import "../lib/math.typ": *
#import "../lib/code.typ": isacmd, isaconst, isai, isalocale, isasession, isathm, isatype
#import "../lib/sources.typ": proved, thy

= Reading the Isabelle Listings <sec:isabelle>

// The declarations below are examples, set smaller than the running text.
#show raw.where(block: true): set text(size: 6.5pt)

This appendix explains the Isabelle/HOL syntax @nipkow14 of the listings that
the chapters lift from the theories. Readers who know Isabelle can skip it.

HOL is a typed logic of total functions. The thesis writes $x :: tau$ for "$x$ has type
$tau$", $tau_1 => tau_2$ for the type of functions from $tau_1$ to $tau_2$,
#isai("'a") for a type variable, and $lambda x. t$ for the function that maps
$x$ to $t$. A function is applied by juxtaposition, as in $f med x med y$. A
_datatype_ declares a type by its constructors, such as #isatype("gcom")
(@sec:vimp). A _record_ is a tuple with named fields, such as
#isatype("dg_spec"), and a #isai("type_synonym") gives a new name for an
existing type.

A #isai("definition") gives a new constant by one equation whose
right-hand side does not mention the constant, so it only names an existing
term and needs no proof. The right-hand side may be any term, for instance a
set comprehension ${s. P med s}$ over an infinite type, so a definition need
not be computable. Below, $forall x$ ranges over all variables:
// deps: preview -- shown for its syntax; @sec:nonrel-state introduces abstract states.
#thy("gamma_state")
A #isai("fun") may instead give one equation per constructor pattern and may
call itself, and Isabelle proves that the recursion terminates. The function below has one equation
for the empty list #isai("[]") and one for a list #isai("q # qs") with head
#isai("q") and tail #isai("qs"). Its result type #isai("'b option") has the
values #isai("None") and #isai("Some y"), which #isai("case") distinguishes:
// deps: preview -- shown for its syntax; @sec:reduced-product uses it.
#thy("first_deciding")

Every HOL function is total, so an ordinary recursive definition needs a
termination proof. Otherwise a definition such as $f(n) = f(n) + 1$ would yield
$0 = 1$ @nipkow14[§2.3.4]. Isabelle's function package can also define a
recursive function without one. The result is still a total HOL constant, but
its defining equations are proved only on its _domain_, the arguments on which
the recursion terminates, and theorems about it assume membership in that
domain. The vendored solver is defined this way, with the domain
#isaconst("solve_dom", thy: "TD_side_upd_rule").

// The explanation and the theorem it introduces stay on one page.
#block(breakable: false)[
  A theorem declares its variables and their types after #isai("fixes"),
  introduces abbreviations local to the statement after #isai("defines"), lists
  its premises after #isai("assumes") and states its conclusion after
  #isai("shows"). The source-level theorem of @sec:headline uses all four:
  // deps: preview -- shown for its syntax; @sec:headline introduces what it uses.
  #proved("run_voblint_source_sound")
]
Inside a proposition, $A ==> B$ is implication and $exists$, $and$, $or$ are
the usual connectives. Subscripts, superscripts, and symbols such as $tack.r$
and $gt.closed$ are notation for a constant applied to its arguments, and the
text names the constant at first use.

A _type class_ collects operations and laws that an instance proves once for a
type @haftmann07. The class #isalocale("widening") fixes an operator, written
infix as $widen$, after #isai("fixes") and states its laws after
#isai("assumes"):
#thy("widening")
The annotation #isai("(infixl \"\<nabla>\" 65)") declares $widen$ as
left-associative infix notation with precedence 65, and #isai("'a :: order")
restricts the type variable to types with an order. Each assumption carries a
name, such as #isai("widen_ge1"), by which proofs cite it. A type has at most
one instance of each class.

A _locale_ fixes parameters and assumptions in the same syntax, and
interpreting it for concrete parameters proves the assumptions and yields its
theorems @ballarin14. Unlike a class, a locale can be interpreted several times
for one type. The locale below fixes one operation. The attribute
#isai("[intro]") after an assumption's name registers it with Isabelle's
automatic proof methods:
#thy("sound_intersection")

An _inductive definition_ is the least relation closed under its rules, and
#isacmd("inductive_set") defines a set the same way. Each rule is a named
implication, and $A ==> B ==> C$ reads "from $A$ and $B$, infer $C$".
_Rule induction_ proves a property of every element with one case
per rule. The set below has a base rule and a step rule:
#thy("reach")
Later chapters define execution relations such as #isaconst("pstep") and
#isaconst("cstep") by rules and write the reflexive–transitive closure of a
step relation $->$ as $scripts(->)^*$.

_Code equations_ determine what code generation emits @haftmann10. One
#isacmd("export_code") declaration emits OCaml from them, and
#isacmd("code_printing") maps a constant to target-language code, such as
integers to OCaml's arbitrary-precision numbers. The generated code is trusted,
not proved (@fig:intro-trust). Theories are grouped into _sessions_, which
Isabelle builds and checks as units, and which later chapters cite as the home
of a construction. The control-flow graph, for instance, lives in
#isasession("Voblint_CFG"), which builds on #isasession("Voblint_VIMP").
