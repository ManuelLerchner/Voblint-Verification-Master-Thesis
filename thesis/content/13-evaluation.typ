#import "../lib/code.typ": *
#import "../lib/stats.typ": stat
#import "../lib/math.typ": absval, conc, ivl, parity-name, signval
#import "../lib/claims.typ": (
  claim-check, claim-ref, claim-snapshot, claim-timed-out, snapshot-verdict,
)
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": verdict


= Analysis Strength and Precision <ch:evaluation>

@ch:results proved that every report #isaconst("run_voblint") returns is
sound. A machine-checked theorem can still hold for uninteresting reasons. Its
premises may never hold together, its obligations may exclude no error a real
analyzer makes, and an analyzer that answers #verdict("UNKNOWN") everywhere
satisfies it as well (#isathm("unknown_everywhere_sound")). Following
#cite(<kim26regulatory>, form: "prose", supplement: [§6]), this chapter first
checks that the premises can hold and that the obligations exclude real
errors. It then shows on concrete programs what precision the analyzer reaches,
and how the code outside the theorem is tested. Several facts below concern one
fixed program and are proved by `eval`, which runs generated code and therefore
also trusts the code generator (@fig:intro-trust).

== The premises can hold #thy-badge("Voblint_Examples", "Example_Non_Vacuity") <sec:nonvacuity>

A theorem whose premises can never hold together is true but says nothing. The
end-to-end theorem has three premises: an initial store, a source run from it,
and an #isaconst("Analysed") answer. The last one needs care, because the
analyzer answers only if its solve terminates, and termination is not proved in
general (@sec:certificate). The direct way to show that the premises are
consistent is to exhibit a program that meets all of them, as
#cite(<marmsoler26stark>, form: "prose", supplement: [§9]) does for the locale
assumptions of a formal model.

We take the two-call program of @fig:program-to-equations and analyze it with
Interval, entry-state contexts, and warrowing. The theory builds a source run
that returns from `bump(5)` and `bump(4)` and stops before the first check.
Evaluation shows that the analyzer answers and that both checks are
#verdict("PROVED"). With these facts, #isathm("nv_source_certified")
instantiates #isathm("run_voblint_source_sound") with every premise discharged.
Its counterpart for single checks, #isathm("nv_check_proved_sound"), does the
same for #isathm("run_voblint_check_sound") at the check `a == 6`.

A #verdict("DEAD") verdict needs its own instance, since its theorem concludes
that no run reaches a node rather than that a condition holds there. A second
program sets `x = 1` and guards a check by `x < 0`. The analyzer marks the
check #verdict("DEAD"), and #isathm("nv_dead_unreached") instantiates
#isathm("run_voblint_dead_check_unreached") to show that the collecting
semantics at that node is empty. In all three instances, the source runs are
proved by rule application, while `eval` computes the compiled graphs and the
analyzer's answers. The main theorems therefore do not hold vacuously, since
each applies to at least one program on which the solve actually terminates.

== The obligations exclude real errors <sec:eval-1161>

Non-vacuity does not show that the obligations are strong enough to reject a
wrong analysis. One way to test them is against a real error. @ch:intro opened
with #link("https://github.com/goblint/analyzer/issues/1156")[issue 1156], in
which Goblint claimed `c % 2 == 1` for $c in {-5, -7}$, although C's truncating
remainder gives $-1$ for both values.
#link("https://github.com/goblint/analyzer/pull/1161")[Pull request 1161]
restricted when the congruence domain returns a constant remainder and added
the program as regression test `37-congruence/14-negative.c` @goblint1161.


In Voblint, the defective operator could not have been proved sound. Every
Congruence remainder must meet #isathm("congruence_mod_sound"), which requires
the remainder #isaconst("c_mod") of any two concrete values to lie in the
concretization of the abstract remainder. Since #isaconst("c_mod") truncates
toward zero, as C11 specifies (@sec:vimp-vs-c), the pre-fix answer, the
constant $1$ for $absval(1 + 2ZZ) mod 2$, violates the obligation at $-5$
(#isathm("prefix_congruence_mod_unsound")). This theorem covers every abstract
remainder that returns the constant, so it also rules out Goblint's pre-fix
operator. @fig:goblint-1161 runs the regression test transliterated into VIMP.
Congruence alone knows only $c in conc(absval(1 + 2ZZ))$ and decides neither check.
Int also knows that $c$ lies in $conc(absval(ivl(-7, -5)))$, so it refutes the first
check and proves the second.

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    show raw: set text(size: 7.5pt)
    let program = json("/shared/generated/vimp-claims.json").at("goblint-1161-int").program
    // Verdict and state of one check, as the registered claim prints them;
    // the product's state is broken at its components.
    let cell(name, cond) = {
      let r = claim-check(name, cond)
      let tone = if r.at(3) == "PROVED" { vb.proved } else if r.at(3) == "REFUTED" {
        vb.unproved
      } else { vb.unstable }
      // The abstract value follows the last `=` or `:` of each component.
      let piece(s) = {
        let m = s.match(regex("^(.*[=:])([^=:]*)$"))
        if m == none { raw(s) } else {
          let (key, val) = m.captures
          if key == "parities:" { val = parity-name(val) }
          [#raw(key)#absval(raw(val))]
        }
      }
      [#text(fill: tone, weight: "bold", r.at(3)) \ #(
          r.at(4).split("; ").map(piece).join(linebreak())
        )]
    }
    let conds = ("c % 2 == 1", "c % 2 == -1")
    grid(
      columns: (58mm, 1fr),
      column-gutter: 10pt,
      align: horizon,
      listing(program, lang: "c", claim: "goblint-1161-int"),
      table(
        columns: (auto, auto, auto),
        inset: (x: 4pt, y: 3pt),
        table.hline(stroke: 0.5pt),
        [*check*], [*Congruence*], [*Int*],
        table.hline(stroke: 0.4pt),
        ..conds
          .map(c => (
            raw(c),
            cell("goblint-1161-congruence", c),
            cell("goblint-1161-int", c),
          ))
          .flatten(),
        table.hline(stroke: 0.5pt),
      ),
    )
  },
  kind: image,
  caption: [Goblint's regression test for #link("https://github.com/goblint/analyzer/pull/1161")[pull request 1161] in VIMP, and the
    verdict and state at each check with Congruence alone and with the Int
    product, both without contexts. Concretely, `c % 2` evaluates to $-1$ on
    both executions.],
) <fig:goblint-1161>

== Precision on concrete programs <sec:eval-precision>

The theorem says nothing about precision, so the examples below measure it on
single programs whose concrete behavior is known.

#let _k99 = claim-snapshot("cost-down-k99")
#let _k100 = claim-snapshot("cost-down-k100")

=== Contexts <sec:eval-contexts>

Contexts trade analysis time for precision. In the program of @fig:ctx-nest,
`f` passes its argument on to `g`, and `main` calls `f` with a positive and a
negative value. With call strings of length 1, a context of `g` records only
its call site in `f`, so both activations of `g` share one context. Sign joins
#signval("+") and #signval("-") there to $absval(top)$, and neither check is
proved. Call strings of length 2 also record the call in `main`, keep the two
activations apart, and prove both checks. The price is a second copy of `g`.
The theories prove the same separation at the entry of `g`
(#isathm("sign_k2_strictly_more_precise_than_k1_at_g")).

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    let program = json("/shared/generated/vimp-claims.json").at("ctx-nest-k2").program
    let cell(name, cond) = {
      let r = claim-check(name, cond)
      let m = r.at(4).match(regex("^(.*=)([^=]*)$"))
      [#verdict(r.at(3)) #raw(m.captures.at(0))#absval(raw(m.captures.at(1)))]
    }
    grid(
      columns: (64mm, 1fr),
      column-gutter: 10pt,
      align: horizon,
      listing(program, lang: "c", claim: "ctx-nest-k2"),
      table(
        columns: (auto, auto, auto),
        inset: (x: 4pt, y: 3pt),
        stroke: none,
        table.hline(stroke: 0.5pt),
        [*check*], [*length 1*], [*length 2*],
        table.hline(stroke: 0.4pt),
        ..("0 < x", "y < 0")
          .map(c => (raw(c), cell("ctx-nest-k1", c), cell("ctx-nest-k2", c)))
          .flatten(),
        table.hline(stroke: 0.5pt),
      ),
    )
  },
  kind: image,
  caption: [Sign with call strings of length 1 and 2 (claims
    #claim-ref("ctx-nest-k1") and #claim-ref("ctx-nest-k2")). Concretely,
    $x = 6$ and $y = -20$.],
) <fig:ctx-nest>

More contexts also cost more, since every context of a procedure gets its own
copy of the procedure's unknowns. The program `down(100)`, which recurses down
to `down(0)` and checks `n >= 0` at every level, shows that this cost does not
buy precision gradually. With call strings of length 100, every level gets its
own context, and the check is #verdict(snapshot-verdict(_k100, "n >= 0")) with
#_k100.clusters.len() procedure copies. With length 99, the analyzer still
builds #_k99.clusters.len() copies, but the deepest calls share one context.
Widening there loses the lower bound of `n`, and the check is
#verdict(snapshot-verdict(_k99, "n >= 0")) (claims #claim-ref("cost-down-k99")
and #claim-ref("cost-down-k100")). Nearly the whole cost is thus paid before
any precision is gained.

With entry-state contexts, the number of contexts need not even be finite.
Under the unit context and under bounded call strings, a compiled program has
finitely many unknowns (#isathm("compiled_unit_vars_finite"),
#isathm("compiled_call_strings_finite")). Entry-state contexts under Interval
have no such bound. A recursion that changes its argument at every
level demands a fresh context at every level, and widening bounds the values
of unknowns but not their number (#fixture(
  "21-context-sensitivity/01-unbounded_context_chain_diverges.vimp",
  label: "01-unbounded_context_chain_diverges",
)). The solve exceeds its time limit, and we expect, without proof, that it
diverges. Goblint's configuration for the SV-COMP competition avoids this
explosion by omitting intervals from the contexts of recursive functions
@saan26phd[§3.4.3].

=== Update rules <sec:eval-rules>

#let _verdict(key, rule, cond) = {
  let name = "rules-" + key + "-" + rule
  // A solve that times out has no listing data; its program is that of the
  // other cells in its row, run at this cell's rule.
  let sibling = ("join", "per-origin", "warrow", "warrow-per-origin", "bounded-narrowing")
    .map(r => "rules-" + key + "-" + r)
    .find(k => k in _vimp-claims)
  let button = vimp-button(playground-link(
    _vimp-claims.at(sibling).program,
    globals: rule,
    ctx: "none",
  ))
  if claim-timed-out(name) { return [#text(fill: vb.unproved)[no answer \ in 5~s] #button] }
  let r = claim-check(name, cond)
  // Every run is Interval, so the printer's domain prefix is dropped.
  let st = r.at(4).split(": ").slice(1).join(": ")
  let m = st.match(regex("^(.*=)([^=]*)$"))
  let state = if m == none { raw(st) } else {
    [#raw(m.captures.at(0))#absval(raw(m.captures.at(1)))]
  }
  [#verdict(r.at(3)) #button \ #state]
}


@fig:rules-programs runs the five update rules of @sec:update-rules on four
programs. Every check holds in every execution, so each #verdict("UNKNOWN") in
the table is lost precision. The first two rules only join contributions to a
global unknown, and the last three also widen them.

In the first row, `p(1)` and `p(2)` publish to the same entry seed. Warrow
joins the two contributions before widening, so the second looks like growth,
and the upper bound of `x` jumps to $+infinity$. The per-origin rules widen each
call site's contribution separately, and since each site writes one constant,
nothing grows. The joining rules never widen and keep $absval(ivl(1, 2))$ as
well. The call in a loop shows the same pattern, and again only Warrow loses
the bound.

The two recursions separate the joining rules from the widening ones. On the
growing recursion, the argument grows without bound, and the joining rules give
no answer within the limit. We expect their solve to diverge, although the
timeout alone does not show this. The widening rules stop at
$absval(ivl(0, +infinity))$, which suffices for `x >= 0`. On the shrinking
recursion, in contrast, per-origin warrowing widens the recursive call's own
contribution to $-infinity$, so `a + 2` may be zero and the division loses all
information. Warrow keeps the lower bound, which we attribute to its joining in
`main`'s argument $-1$ first, and the joining rules keep
$absval(ivl(-1, 9))$. No rule is therefore best on every row. Bounded
narrowing, at its default bound 5, matches per-origin warrowing on all four
programs.

#figure(
  {
    set text(size: 8pt)
    set par(first-line-indent: 0pt, justify: false)
    show raw: set text(size: 7.5pt)
    let rules = ("join", "per-origin", "warrow", "warrow-per-origin", "bounded-narrowing")
    let progs = (
      ("two-sites", "x <= 2", [two call sites: `p(1); p(2);`, check `x <= 2` in `p`]),
      ("loop-call", "x < 10", [call in a loop: `g(x)` for `x` from 0 to 9, check `x < 10` in `g`]),
      ("grows", "x >= 0", [growing recursion: `f(x)` calls `f(x + 1)` from `f(0)`, check `x >= 0`]),
      (
        "shrinks",
        "a <= 9",
        [shrinking recursion: `f(a)` calls `f(9 / (a + 2))` while `a < 4`,
          from `f(-1)`, check `a <= 9`],
      ),
    )
    table(
      columns: (2.2fr, 1fr, 1fr, 1fr, 1fr, 1fr),
      align: (
        left + horizon,
        center + horizon,
        center + horizon,
        center + horizon,
        center + horizon,
        center + horizon,
      ),
      stroke: none,
      inset: (x: 3pt, y: 3pt),
      table.hline(stroke: 0.5pt),
      [*program*], [*join*], [*join per origin*], [*warrow*], [*warrow per origin*],
      [*bounded narrowing*],
      table.hline(stroke: 0.4pt),
      ..progs
        .enumerate()
        .map(((i, (key, cond, what))) => (
          what,
          ..rules.map(r => _verdict(key, r, cond)),
          ..if i + 1 < progs.len() { (table.hline(stroke: 0.25pt + luma(190)),) },
        ))
        .flatten(),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  caption: [Update rules on four programs (Interval, no contexts, bounded
    narrowing at bound 5), as on the #link(site("#globals"))[project site]. Each
    cell gives the verdict and state at the row's check, and its button opens
    the run. "No answer in 5 s": stopped by `--timeout 5`.],
) <fig:rules-programs>

=== Further precise answers <sec:eval-coop>

Earlier chapters already showed precise answers. Narrowing recovers the bound of the counting loop after widening
(@sec:widening), entry-state contexts keep the two calls of `bump` apart
(@fig:eq-policies), and only the reduced product proves `v == 51` on the
stride-2 loop (@fig:stride2). Analyses that cooperate through queries decide
checks that each leaves unknown alone (@ch:cooperation,
#isathm("order_asks_needs_both")). Beyond these, the corpus holds
#stat("corpus.kinds.precision") fixtures that pin a definite verdict
(@sec:eval-corpus). Searching the
#link(site("playground.html"))[playground]'s examples for "precision" lists
them.

== Tests of the unverified parts <sec:eval-corpus>

The theorem stops at the generated analyzer, so the handwritten OCaml around it
(@tab:sizes) is tested rather than proved. A
#link(repo-blob + "tests/regression")[regression corpus] runs the analyzer end
to end. It holds #stat("corpus.cases") VIMP fixtures in #stat("corpus.groups")
groups, part of them adapted from Goblint's regression tests, as each header
records. Each fixture states its command-line flags and the verdict expected at
each check.  In
`soundness/`, the program has executions on both sides of the check, so
#verdict("UNKNOWN") is the only sound answer. In `known-imprecision/`, the
concrete result is fixed, but the abstraction cannot establish it, and the
header names the mechanism that loses the information. The remaining #stat("corpus.kinds.other") fixtures pin other output, such as graph snapshots.

The runner matches results by source line, which tests the position
bookkeeping of @sec:ocaml-boundary.
#link(repo-blob + "tests/solver-trace")[Golden files] pin the solver trace
(@sec:tracing) of three programs step by step. When
#link(
  "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/pull/256",
)[pull request 256]
published a call's seed before reading its exit at nodes where one call
returns, as Goblint does, the trace
of the running example shrank from 241 to 155 steps.

The parser is trusted to hand the analyzer the program the user wrote.
Property tests print random syntax trees, built from the constructors exported
from Isabelle, and require the parser to read back the same tree and to finish
on mutated programs without a crash.
