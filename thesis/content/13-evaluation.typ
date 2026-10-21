#import "../lib/code.typ": *
#import "../lib/stats.typ": stat
#import "../lib/math.typ": absval, conc, ivl, parity-name, signval
#import "../lib/claims.typ": (
  claim-check, claim-ref, claim-snapshot, claim-text, claim-timed-out, snapshot-verdict,
)
#import "../lib/theme.typ": vb
#import "../lib/figures.typ": verdict
#import "../lib/profiling.typ": (
  prof-exp, prof-growth, prof-int, prof-list, prof-ms, prof-runs, prof-value, scaling-plot,
)


= Evaluation of Strength and Precision <ch:evaluation>

@ch:results proved that every report #isaconst("run_voblint") returns is
sound. A machine-checked theorem can still hold for uninteresting reasons. Its
premises may never hold together, its obligations may exclude no error a real
analyzer makes, and an analyzer that answers #verdict("UNKNOWN") everywhere
satisfies it as well (#isathm("unknown_everywhere_sound")). Following
#cite(<kim26regulatory>, form: "prose", supplement: [§6]), this chapter first
checks that the premises can hold and that the obligations exclude real
errors. It then shows, on concrete programs, what precision the analyzer reaches
and where it ends. Several facts below concern one
fixed program and are proved by `eval`, which runs generated code and therefore
also trusts the code generator (@fig:intro-trust).

== The soundness theorems are not vacuous #thy-badge("Voblint_Examples", "Example_Non_Vacuity") <sec:nonvacuity>

A theorem whose premises can never hold together is true but says nothing. The
end-to-end soundness theorem has three premises: an initial store, a source execution from it,
and an #isaconst("Analysed") answer. The last one needs care, because the
analyzer answers only if its solve terminates, and termination is not proved in
general (@sec:certificate). The direct way to show that the premises are
consistent is to exhibit a program that meets all of them, as
#cite(<marmsoler26stark>, form: "prose", supplement: [§9]) does for the locale
assumptions of a formal model.

Here, the two-call program of @fig:program-to-equations is analyzed with
Interval, entry-state contexts, and the _warrow_ update rule. The theory builds a source execution
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
semantics at that node is empty. In all three instances, the source executions are
proved by rule application, while `eval` computes the compiled graphs and the
analyzer's answers. The end-to-end soundness theorem and its companions therefore do not hold vacuously, since
each applies to at least one program on which the solve actually terminates.

== The obligations reject a real Goblint bug <sec:eval-1161>

Non-vacuity does not show that the obligations are strong enough to reject a
wrong analysis. One way to test them is to check them against a real error. @ch:intro opened
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
    verdict and state at each check with Congruence alone and with Int, both
    under the unit context policy. Concretely, `c % 2` evaluates to $-1$ on
    both executions.],
) <fig:goblint-1161>

== Measuring precision on concrete programs <sec:eval-precision>

The theorem says nothing about precision, so the examples below measure it on
single programs whose concrete behavior is known.

Earlier chapters already showed precise answers. Narrowing recovers the bound of the counting loop after widening
(@sec:widening), entry-state contexts keep the two calls of `bump` apart
(@fig:eq-policies), and only Int proves `v == 51` on the
stride-2 loop (@fig:stride2). Analyses that cooperate through queries decide
checks that each alone leaves unknown (@ch:cooperation,
#isathm("order_asks_needs_both")). Beyond these, the corpus holds
#stat("corpus.kinds.precision") fixtures that pin a definite verdict
(@sec:eval-corpus). Searching the
#link(site("playground.html"))[playground]'s examples for "precision" lists
them.

#let _k99 = claim-snapshot("cost-down-k99")
#let _k100 = claim-snapshot("cost-down-k100")

=== Precision and cost of calling contexts <sec:eval-contexts>

Contexts trade analysis time for precision. In the program of @fig:ctx-nest,
`f` passes its argument on to `g`, and `main` calls `f` with a positive and a
negative value. With call strings of length 1, a context of `g` records only
its call site in `f`, so both activations of `g` share one context. Sign joins
#signval("+") and #signval("-") there to $absval(top)$, and neither check is
proved. Call strings of length 2 also record the call in `main`, keep the two
activations apart, and prove both checks. The price is a second copy of `g`.
Evaluating #isaconst("run_voblint") on this program in Isabelle gives the same
verdicts, so the comparison is a theorem about the analyzer itself
(#isathm("run_voblint_call_string_2_decides")). With the soundness theorem, the
two length-2 verdicts then hold for every store that reaches the checks
(#isathm("cs_nest_checks_hold")). A second theorem shows the separation at the
entry of `g` on hand-built equation systems
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
Under the unit context policy and bounded call strings, a compiled program has
finitely many unknowns (#isathm("compiled_unit_vars_finite"),
#isathm("compiled_call_strings_finite")). Entry-state contexts under Interval
have no such bound. A recursion that changes its argument at every
level demands a fresh context at every level, and widening bounds the values
of unknowns but not their number (#fixture(
  "21-context-sensitivity/01-unbounded_context_chain_diverges.vimp",
  label: "01-unbounded_context_chain_diverges",
)). The solve exceeds its time limit, and it is expected, without proof, to
diverge. Goblint's configuration for the SV-COMP competition avoids this
explosion by omitting intervals from the contexts of recursive functions
@saan26phd[§3.4.3].

=== Comparing the update rules for global unknowns <sec:eval-rules>

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
  let st = r.at(4)
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

In the first row, `p(1)` and `p(2)` publish to the same seed. _Warrow_
joins the two contributions before widening, so the second looks like growth,
and the upper bound of `x` jumps to $+infinity$. The per-origin rules widen each
call site's contribution separately, and since each site writes one constant,
nothing grows. The joining rules never widen and keep $absval(ivl(1, 2))$ as
well. The call in a loop shows the same pattern, and again, only _warrow_ loses
the bound.

The two recursions separate the joining rules from the warrowing ones. On the
growing recursion, the argument grows without bound, and the joining rules give
no answer within the limit. Their solve is expected to diverge, although the
timeout alone does not show this. The warrowing rules stop at
$absval(ivl(0, +infinity))$, which suffices for `x >= 0`. On the shrinking
recursion, in contrast, _warrow per origin_ widens the recursive call's own
contribution to $-infinity$, so `a + 2` may be zero and the division loses all
information. _Warrow_ keeps the lower bound, which the author attributes to its joining in
`main`'s argument $-1$ first, and the joining rules keep
$absval(ivl(-1, 9))$. No rule is therefore best on every row. _Bounded
narrowing_, at its default bound 5, matches _warrow per origin_ on all four
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
  caption: [Update rules on four programs (Interval, unit context policy, bounded
    narrowing at bound 5), as on the #link(site("#globals"))[project site]. Each
    cell gives the verdict and state at the row's check, and its button opens
    the run. "No answer in 5 s": stopped by `--timeout 5`.],
) <fig:rules-programs>

== Comparing precision with Goblint <sec:eval-flavors>

#let _gob = {
  let rows = (:)
  for line in read("../shared/code/goblint-flavors/results.tsv").split("\n") {
    let cells = line.split("\t")
    if cells.len() == 3 { rows.insert(cells.at(0) + "/" + cells.at(1), cells.at(2)) }
  }
  rows
}
// One check of one Goblint run, in the thesis's verdict words.
// A path-sensitive run prints one verdict per path, so a check is proved only
// if every path's verdict succeeds.
#let _gv(prog, config, cond) = {
  let outs = _gob.at(prog + "/" + config).split(";").filter(c => c.starts-with(cond + ":"))
  assert(outs.len() > 0, message: "results.tsv has no check " + cond + " for " + prog)
  verdict(if outs.all(o => o.ends-with("will succeed")) { "PROVED" } else { "UNKNOWN" })
}
#let _vv(name, cond) = verdict(claim-check(name, cond).at(3))
#let _flavor(name) = listing(_vimp-claims.at(name).program, lang: "c", claim: name)


The programs of @sec:eval-precision were selected because a mechanism succeeds
on them, which biases them toward Voblint's strengths. Its limits are better
measured on programs selected by someone else. Monniaux's tutorial on the flavors of abstract
interpretation walks through finite lattices, relational domains, widening and
narrowing, and alternatives to iterative solving. For each, it gives a small
program on which a standard analysis gains or loses precision @monniaux24.
Every program of the tutorial that VIMP can express is transliterated into a
regression fixture of
#link(repo-blob + "tests/regression/28-flavors")[`28-flavors`], and Voblint's
verdicts on them are registered as claims. Each check holds in every execution, so each
#verdict("UNKNOWN") below is lost precision.

#figure(
  {
    set text(size: 7.5pt)
    set par(first-line-indent: 0pt, justify: false)
    // (header, Voblint claim suffix, check, Goblint program); the reset at
    // bound has two checks, so it has two columns.
    let progs = (
      ([rule of \ signs], "vanilla", "z < 0", "vanilla"),
      ([not \ inductive], "not-inductive", "i > 0", "sign_not_inductive"),
      ([absolute \ value], "coffee", "x != 0", "coffee_bounded"),
      ([bounded \ loop], "fudge", "i == 10", "fudge"),
      ([reset at \ bound], "reset-bound", "i <= 9", "narrow_works_lb"),
      ([reset at \ bound], "reset-bound", "i >= 0", "narrow_works_lb"),
      ([skipped \ increment], "skipped", "i <= 9", "blackcurrant"),
      ([reset at \ equality], "reset-eq", "i <= 9", "reset_eq"),
    )
    let voblint = (
      ([Sign], "sign"),
      ([Interval], "interval"),
      ([Int], "int"),
      ([Int, Order], "int-order"),
    )
    let goblint = (
      ([Interval], "interval"),
      ([delay 10], "interval+gas10"),
      ([Int, delay 3], "int+gas3"),
      ([thresholds], "interval+thresholds"),
      ([comparisons], "interval+thresholds-comparisons"),
      ([octagons], "octagon"),
      ([octagons, paths], "octagon+branches"),
    )
    let group(name, n) = table.cell(rowspan: n, align: left + horizon, rotate(
      -90deg,
      reflow: true,
      strong(name),
    ))
    table(
      columns: (auto, auto) + (1fr,) * progs.len(),
      align: (left + horizon, left + horizon) + (center + horizon,) * progs.len(),
      stroke: none,
      inset: (x: 2pt, y: 2pt),
      table.hline(start: 2, stroke: 0.5pt),
      [], [],
      // The column groups are the paragraphs that discuss them below.
      ..(
        ([finite lattices], 2),
        ([paths and \ convexity], 1),
        ([widening and narrowing], 3),
        ([narrowing foiled], 2),
      ).map(((name, n)) => table.cell(colspan: n, emph(name))),
      ..(2, 4, 5, 8, 10).map(x => table.vline(x: x, stroke: 0.25pt)),
      ..range(4).map(i => {
        let starts = (2, 4, 5, 8)
        let ends = (4, 5, 8, 10)
        table.hline(start: starts.at(i), end: ends.at(i), stroke: 0.25pt)
      }),
      [], [], ..progs.map(((what, _, _, _)) => what),
      [], [], ..progs.map(((_, key, _, _)) => vimp-button(claim-playground(
        "flavors-" + key + "-interval",
      ))),
      [], [*check*], ..progs.map(((_, _, cond, _)) => raw(cond)),
      table.hline(stroke: 0.4pt),
      ..voblint
        .enumerate()
        .map(((i, (label, cfg))) => (
          ..if i == 0 { (group("Voblint", voblint.len()),) },
          label,
          ..progs.map(((_, key, cond, _)) => _vv("flavors-" + key + "-" + cfg, cond)),
        ))
        .flatten(),
      table.hline(stroke: 0.4pt),
      ..goblint
        .enumerate()
        .map(((i, (label, cfg))) => (
          ..if i == 0 { (group("Goblint", goblint.len()),) },
          label,
          ..progs.map(((_, _, cond, gprog)) => _gv(gprog, cfg, cond)),
        ))
        .flatten(),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  placement: auto,
  caption: [The flavors programs @monniaux24 under each analysis setting of
    Voblint (#link(repo-blob + "tests/regression/28-flavors")[`28-flavors`]) and
    of Goblint (#link(repo-blob + "thesis/shared/code/goblint-flavors")[C
      versions], #link(repo-blob + "thesis/shared/code/goblint-flavors/results.tsv")[`results.tsv`]). Each VIMP button opens the program in the
    playground. Goblint's "will succeed" is shown as
    #verdict("PROVED"), "is unknown" as #verdict("UNKNOWN").],
) <tab:flavors>


For comparison, Goblint at revision
#link(
  "https://github.com/goblint/analyzer/tree/6127869c56c61fa184a830a3fcfb7df44de33829",
)[`6127869`]
ran on C versions of the same programs (@tab:flavors). VIMP's integers are
unbounded (@sec:vimp-vs-c), whereas Goblint analyzes C's `int`. On these
programs, the difference does not change what the programs compute, since no
execution leaves the range of `int`. It can still change an analysis result,
because an abstract value may reach the limit of `int` although no execution
does. Goblint then applies its default setting `assume_top` of
#link("https://github.com/goblint/analyzer/blob/6127869c56c61fa184a830a3fcfb7df44de33829/src/config/options.schema.json#L1640")[`sem.int.signed_overflow`], which gives a
signed operation that may overflow the whole range of its type. This happens
for one check, discussed in @sec:flavors-widening.

The settings of @tab:flavors are chosen such that each analyzer has its best
chance on each flavor. Voblint runs Sign, Interval, Int, the reduced product of its four
non-relational domains (@sec:reduced-product), and Int with the order
analysis, its only relational information. No other Voblint option affects
these programs. Its solver has neither widening delays nor thresholds, and
calling contexts and the update rules for global unknowns need procedures,
which a second benchmark compares (@tab:flavors-ctx). The Goblint rows
"delay 10", "thresholds", and "comparisons" apply the repairs the literature
proposes for failed narrowing, and $10$ is the smallest delay that proves a
check Interval leaves unknown. In "Int, delay 3", Goblint's closest
counterpart of Voblint's Int, Interval and Congruence refine each other. The last two rows add Apron's octagons @jeannet09apron, the second together with Goblint's
#link("https://github.com/goblint/analyzer/blob/6127869c56c61fa184a830a3fcfb7df44de33829/src/analyses/branchSet.ml")[`branchSet`] analysis, which keeps
a separate state for each set of branches taken.

The following subsections discuss the column groups of @tab:flavors from left
to right.

=== Finite lattices <sec:flavors-lattices>

The tutorial opens with the rule of signs, which says that
the sum of two negative numbers is negative @monniaux24[slide 8]. Over unbounded integers, the rule is sound, and Sign proves `z < 0` after
`z = x + y` with $x = -5$ and $y = -10$ (claim
#claim-ref("flavors-vanilla-sign")).

A set of states at a loop head is an _inductive_ invariant if it contains the states that first
reach the head, and if one more iteration of the loop from any of its states
stays inside it. In the terms of @sec:lattices, it is a post-fixpoint of the loop's
transfer function that contains the initial states. The abstract value that an
analyzer computes at a loop head describes such an invariant, so a check that
the analyzer proves follows from an inductive invariant that its domain can
express. The converse fails: widening may miss an invariant the domain can
express (@sec:flavors-foiled).

#_flavor("flavors-not-inductive-sign")

In this loop from the tutorial @monniaux24[slide 27], `i` takes the values $4$
and $2$ at the check, so `i > 0` holds. The property
is not inductive, however. If all that is known at the loop head is that `i`
is positive, `i` may be $1$, and the next iteration then yields $-1$. Sign can
express `i > 0` but nothing stronger about `i`, so the loop head reaches every
sign, and the check is #_vv("flavors-not-inductive-sign", "i > 0") (claim
#claim-ref("flavors-not-inductive-sign")). Int, in contrast, can express a stronger
property that is inductive: at the loop head, `i` is nonnegative, at most $4$,
and even. A positive `i` with these bounds is $2$ or $4$, so the next iteration
yields $0$ or $2$ and stays inside the property.

Int finds this invariant through the reduction of its components. Widening
drops Interval's lower bound at the loop head, but Sign keeps $i gt.eq 0$. The guard `i != 0` then
makes the sign positive, and the reduction (@sec:reduced-product) moves the interval to $absval(ivl(1, 4))$ and, since `i`
is even, to $absval(ivl(2, 4))$. From there, `i - 2` returns to
$absval(ivl(0, 2))$, which the head value already covers, and the check is
#_vv("flavors-not-inductive-int", "i > 0"). Without the reduction, the check sees $i in absval(ivl(-infinity, 4))$ and is
#_vv("flavors-not-inductive-int-never", "i > 0") (claims
#claim-ref("flavors-not-inductive-int") and
#claim-ref("flavors-not-inductive-int-never")). Goblint proves the check only with a widening delay of $3$ or with thresholds
at the constants of comparisons (@tab:flavors, #link(repo-blob + "thesis/shared/code/goblint-flavors/results.tsv")[`results.tsv`]).

=== Paths and convexity <sec:flavors-paths>

The tutorial's coffee example computes an absolute value
and checks that it is positive only for a nonzero argument
@monniaux24[slide 38]:

#_flavor("flavors-coffee-int-order")

The check needs $y lt.eq |x|$ after the branch, which holds only as the
disjunction of $y = x$ on one path and $y = -x$ on the other. A non-relational
domain loses both relations. A convex relational domain joins the branches
into their convex hull @cousot78[§4.4], which keeps $y gt.eq |x|$ but loses
$y lt.eq |x|$, so polyhedra fail as well @monniaux24[slides 42--43]. Voblint's
order analysis ends with $x lt.eq y$, which does not exclude $x = 0$, and the
check is #_vv("flavors-coffee-int-order", "x != 0") (claim
#claim-ref("flavors-coffee-int-order")). Proving the check requires keeping
the two branches apart, as trace partitioning and path partitioning do
@rival07[§1.1] @blanchet03[§7.1.5] @mine17[§6.3.4]. In Goblint, neither octagons
nor path sensitivity alone proves the check, but octagons partitioned by the
branches taken do. Voblint has no such
partitioning, which would need its own soundness proof.

=== Widening and narrowing <sec:flavors-widening>

Voblint's Interval proves both widening examples that narrowing repairs: the
bounded loop, which counts `i` to $10$ (claim
#claim-ref("flavors-fudge-interval")), and the reset at bound:

#_flavor("flavors-reset-bound-interval")

Widening sends the upper bound of `i` to $+infinity$, and narrowing through the
test `i >= 10` brings it back to $9$ @monniaux24[slide 59]. Both checks are
#_vv("flavors-reset-bound-interval", "i <= 9") over
#absval(raw(claim-check("flavors-reset-bound-interval", "i >= 0").at(4).split("i=").at(1)))
(claim #claim-ref("flavors-reset-bound-interval")). Goblint's
Interval proves `i <= 9` but loses `i >= 0` because its widening stops at the
largest `int`, where `i + 1` may overflow and `assume_top` gives the sum the
whole range of `int`. With `assume_none`, which assumes that no signed
operation overflows, Goblint proves `i >= 0` as well (#link(repo-blob + "thesis/shared/code/goblint-flavors/results.tsv")[`results.tsv`]).

=== Narrowing foiled <sec:flavors-foiled>

Two variants of the same counter defeat narrowing. In the
skipped increment (left), a nondeterministic branch may skip the increment
@monniaux24[slide 60]. In the reset at equality (right), the counter resets on
`i == 10` instead of `i >= 10` @monniaux24[slide 77]:

#grid(
  columns: (1fr, 1fr),
  column-gutter: 8pt,
  _flavor("flavors-skipped-interval"), _flavor("flavors-reset-eq-interval"),
  align(center, text(size: 8pt)[skipped increment]),
  align(center, text(size: 8pt)[reset at equality]),
)

In the skipped increment, the skipping path carries the loop-head value back
unchanged. Every interval $absval(ivl(0, c))$ with $c gt.eq 9$ is therefore a
fixpoint, the widened value included, and a decreasing iteration cannot descend
below a fixpoint @mine17[§4.7.3, Ex. 4.7] @halbwachs12. In the reset at
equality, the test removes no bound from an interval, so nothing stops the
widened bound at $9$. Both checks are #_vv("flavors-skipped-interval", "i <= 9") in
Voblint, with $i in absval(ivl(0, +infinity))$ (claims
#claim-ref("flavors-skipped-interval") and #claim-ref("flavors-reset-eq-interval")).
Goblint's octagons do not help either, since the loss comes from the
iteration.

The known repairs change how the solver iterates. Goblint proves both checks
when it delays widening by $10$ rounds @blanchet03[§7.1.3], but not by $9$, so
the delay must exceed the loop bound. It also proves them with threshold
widening @blanchet03[§7.1.2], but only when the thresholds include the $9$ of
the check itself. Policy iteration @costan05[§3.2] and guided static analysis
@gopan07 replace the decreasing iteration altogether. In Voblint, each repair
would change the vendored solver and its partial-correctness proof.

The flavors benchmark has eight checks on small programs, so it compares the
mechanisms of the two analyzers and says little about their precision on
larger programs. On these checks, Voblint loses no precision to verification
on the mechanisms both analyzers share. With Int and the order
analysis, it proves five of the eight checks of @tab:flavors, and Goblint's
plain Interval proves three. Across all its settings, Goblint proves all eight,
though no single setting does, using widening delays, thresholds, and path
partitioning. Voblint lacks these techniques, and each would bring its own
proof obligation.

=== Procedures <sec:flavors-procedures>

The second benchmark compares calling contexts and the update rules for
global unknowns on five programs from Goblint's own regression suite, adapted
to VIMP (@tab:flavors-ctx). Goblint runs on C versions whose checks all hold
in a native run
(#link(repo-blob + "thesis/shared/code/goblint-contexts")[`goblint-contexts`]).
Voblint runs Int, and Goblint runs Interval
with its default domain of excluded values, so both refine a guard such as
`i != 0`.

In _three contexts_, a loop steps `i` by `f(i) = i + 1` and then checks
`i == 10`. The _deep call chain_ consists of recursive procedures that call
each other up to $21$ levels deep, and its ten checks ask for their results. In the _chain with guards_, `f` calls `g`, `g` calls `h`, and
`h` counts its argument down to $0$ behind the guards `i == 0` and `0 < i`, and all seven calls, with arguments up to $300$, return $3$. In the
_mutual recursion_, $f(i) = g(i-2) + g(i-3)$ and $g(i) = f(i+1)$, and twelve
checks ask for exact values. The _two-formal countdown_
`f(x, y)` decrements both arguments until `x` reaches $0$ and returns `y`, so its three calls return $0$.

#let _ctx-gob = {
  let rows = (:)
  for line in read("../shared/code/goblint-contexts/results.tsv").split("\n") {
    let cells = line.split("\t")
    if cells.len() == 4 { rows.insert(cells.at(0) + "/" + cells.at(1), cells) }
  }
  rows
}
// Proved checks out of those that hold. A check Goblint reports nothing for
// was found unreachable, which counts as proved, like Voblint's DEAD.
#let _ratio(k, n) = {
  let fill = if k == n { vb.proved } else if k == 0 { vb.unproved } else { vb.neutral }
  text(fill: fill)[#k/#n]
}
#let _ctx-v(key, cfg) = {
  let rows = claim-text("ctxcmp-" + key + "-" + cfg)
    .split("\n")
    .map(l => l.trim().split(regex("\s{2,}")))
    .filter(c => c.len() == 5 and c.at(3) in ("PROVED", "REFUTED", "UNKNOWN", "DEAD"))
    // The circle fixture also pins Goblint's wrong annotation f(13) = 233.
    .filter(c => c.at(2) != "m == 233")
  _ratio(rows.filter(c => c.at(3) in ("PROVED", "DEAD")).len(), rows.len())
}
#let _ctx-g(prog, cfg) = {
  let cells = _ctx-gob.at(prog + "/" + cfg)
  let n = int(cells.at(2))
  let reported = cells.at(3).split(";").filter(c => c != "")
  let ok = reported.filter(c => c.ends-with("will succeed")).len() + n - reported.len()
  _ratio(ok, n)
}

#figure(
  {
    set text(size: 7.5pt)
    set par(first-line-indent: 0pt, justify: false)
    let progs = (
      ([three \ contexts], "ctxs3"),
      ([deep call \ chain], "chain5"),
      ([chain with \ guards], "chain3"),
      ([mutual \ recursion], "circle"),
      ([two-formal \ countdown], "countdown"),
    )
    let voblint = (
      ([none], "none"),
      ([bounded narrowing], "none-bn"),
      ([call string, $k = 1$], "cs1"),
      ([call string, $k = 5$], "cs5"),
      ([entry state], "es"),
    )
    let goblint = (
      ([none], "insensitive"),
      ([narrowing globals], "insensitive+narrow-globs"),
      ([call string, $k = 1$], "callstring1"),
      ([call string, $k = 5$], "callstring5"),
      ([full], "full"),
      ([gas 10], "gas10"),
    )
    let group(name, n) = table.cell(
      rowspan: n,
      align: left + horizon,
      rotate(-90deg, reflow: true, strong(name)),
    )
    table(
      columns: (auto, auto) + (1fr,) * progs.len(),
      align: (left + horizon, left + horizon) + (center + horizon,) * progs.len(),
      stroke: none,
      inset: (x: 3pt, y: 2pt),
      table.hline(stroke: 0.5pt),
      [], [], ..progs.map(((what, _)) => what),
      [], [], ..progs.map(((_, key)) => vimp-button(claim-playground("ctxcmp-" + key + "-es"))),
      table.hline(stroke: 0.4pt),
      ..voblint
        .enumerate()
        .map(((i, (label, cfg))) => (
          ..if i == 0 { (group("Voblint", voblint.len()),) },
          label,
          ..progs.map(((_, key)) => _ctx-v(key, cfg)),
        ))
        .flatten(),
      table.hline(stroke: 0.4pt),
      ..goblint
        .enumerate()
        .map(((i, (label, cfg))) => (
          ..if i == 0 { (group("Goblint", goblint.len()),) },
          label,
          ..progs.map(((_, key)) => _ctx-g(key, cfg)),
        ))
        .flatten(),
      table.hline(stroke: 0.5pt),
    )
  },
  kind: table,
  placement: bottom,
  caption: [Checks proved out of those that hold, on procedure programs adapted
    from Goblint's regression suite (Voblint with Int, Goblint with Interval).
    Voblint: no contexts, also with bounded
    narrowing; call strings of length $k$; entry-state contexts. Goblint
    (#link(repo-blob + "thesis/shared/code/goblint-contexts/results.tsv")[`results.tsv`]):
    context gas $0$, also with narrowing of global unknowns; call strings
    of length $k$; its default full contexts; context gas $10$.],
) <tab:flavors-ctx>

Goblint's context gas $0$, call strings, full contexts, and narrowing of
global unknowns
(#link("https://github.com/goblint/analyzer/blob/6127869c56c61fa184a830a3fcfb7df44de33829/src/config/options.schema.json#L2595")[`solvers.td3.narrow-globs`])
correspond to Voblint's policy without contexts, its call strings,
entry-state contexts, and bounded narrowing (@sec:update-rules). Context gas $10$
(#link("https://github.com/goblint/analyzer/blob/6127869c56c61fa184a830a3fcfb7df44de33829/src/config/options.schema.json#L1061")[`ana.context.gas_value`]),
which keeps full contexts only for the first ten recursive calls, has no
counterpart.

With entry-state contexts, Voblint proves every check of all five programs.
Goblint's full contexts prove every check except the one of the three-contexts
program. After its loop,
an interval only bounds `i` to $absval(ivl(10, 11))$. Voblint's Int also knows
that `i` is even, which leaves $10$, and Goblint's configuration has no parity
or congruence component. With bounded contexts,
Goblint proves more on the deep call chain and Voblint more on the mutual
recursion. The two-formal
countdown recurses up to $300$ levels deep and needs a context per level,
which only entry-state contexts provide.

On this benchmark, Voblint's entry-state contexts prove every check that
Goblint's full contexts prove, and one more. With call strings, each analyzer
proves checks the other loses, and without contexts Voblint proves more. Goblint's widening
then loses the lower bound $0$ of `i` in `h` unless it narrows global unknowns
(#link(repo-blob + "thesis/shared/code/goblint-contexts/results.tsv")[`results.tsv`]), whereas Voblint keeps it and turns `i != 0` into `i > 0`.

== Running time <sec:eval-runtime>

A sound result is of little use if the analyzer takes too long to produce it. Speed,
however, was not a goal of this thesis. Apart from the defect fixed in @sec:codegen, the
generated code runs as Isabelle emits it. The measurements below therefore ask only
whether this unoptimized code runs in acceptable time on the regression corpus.

The #link(site("profiling.html"))[profiling page] reports the measurements in full. They
cover the regression fixtures, the WebAssembly build, generated programs of growing size,
and CPU profiles. This section summarizes them. The profiler selects the
#prof-int("fixtures_selected") fixtures whose header sets no timeout of its own, which
leaves out the fixtures that test divergence. Of these, #prof-int("fixtures_ill_formed")
are programs that the parser or the well-formedness check rejects, so
#prof-int("fixtures") fixtures remain. Each of them runs under all
#prof-int("configurations") combinations of domain and context policy, and each such
pair of a fixture and a configuration is one case.

#if prof-value("timeouts") > 0 [Of the #prof-int("cases") cases, #prof-int("timeouts") pass
  the limit of #prof-int("meta.timeout_s")~s, all of them under
  #prof-list("timeout_contexts") contexts.]
The other #prof-int("cases_solved") cases finish, and each is timed as #prof-runs().
#if prof-value("solve_median_ms") < 5 [Most of them are solved within a few
  milliseconds.] else [Their median solve time is #prof-ms("solve_median_ms").]
The expensive cases include recursive programs under entry-state contexts, where successive
calls can create distinct contexts. A procedure `h` that calls itself $n$ times with
arguments $n, n - 1, dots, 0$ shows the effect. Sign and Parity have only a few abstract
values, so the number of contexts stays bounded and the solve time is
#prof-growth("depth_fits.sign.time"). Congruence, Interval and Int tell the successive
arguments apart and create one context per level. Their solve time grows
#prof-growth("depth_fits.interval.time"), although the number of solver evaluations grows
only #prof-growth("depth_fits.interval.evals").

#if prof-value("scaling.broken").len() == 0 [
  Generated programs that grow other sizes, such as variables or statements, show no such
  gap, so the growth is tied to contexts.
] else if prof-value("scaling.flat").len() == 0 [
  The same gap appears without recursion. The profiling page grows
  #prof-int("scaling.count") sizes of a program independently, from variables and
  statements to call chains. In all of them the number of evaluations grows about linearly,
  while solve time grows as #prof-exp("scaling.time_min") to #prof-exp("scaling.time_max")
  (@fig:runtime-scaling). Each evaluation therefore gets more expensive as the program
  grows, along every size measured.
] else [
  Generated programs that grow one size at a time show the same gap with
  #prof-list("scaling.broken"), while time and evaluations grow alike with
  #prof-list("scaling.flat") (@fig:runtime-scaling).
]
The CPU profiles trace this cost to the data structures of the generated code. Its finite
sets and maps are lists (@sec:codegen), so a membership test scans the list, a union
inserts element by element, and removing duplicates compares every pair. Balanced trees or
hash tables would avoid these scans. The Collections Framework @lammich10collections
refines abstract sets and maps into such structures, and the Light-weight Containers
@lochbihler13containers can replace the list-based default of code generation altogether.
Either route needs only targeted replacements in the code setup and no change to the
soundness proofs.

The generated analyzer therefore handles the regression corpus in acceptable time, while
its data structures limit how far it scales. These measurements cover small programs on
one machine and give no performance guarantee beyond them.

#figure(
  scaling-plot(width: 12.5cm, height: 4.6cm),
  kind: image,
  placement: bottom,
  caption: [Fitted exponents $k$ of $n^k$ for solve time and solver evaluations, each family
    growing one program size $n$ under Interval. The fits describe the measured ranges and
    are no complexity bounds.],
) <fig:runtime-scaling>
