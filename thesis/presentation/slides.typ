// The thesis talk. It opens like the thesis introduction (wrong answers,
// machine-checked proofs, Goblint's architecture), works through one example
// into the formal argument, demonstrates the playground live, and closes like
// the thesis conclusion (relevance to Goblint, limits, outlook).
#import "theme.typ": *
#import "../lib/code.typ": (
  claim-playground-link, decode-isabelle, isabelle-scripts, isabelle-syntax, isaconst, isalocale,
  isathm, isatype, playground-link, site,
)
#import "../lib/claims.typ": claim-check, claim-snapshot, snapshot-verdict
#import "../lib/stats.typ": stat
#import "../lib/theme.typ": metro

#show: deck
// Isabelle sub- and superscripts, as the thesis renders them.
#show raw.where(lang: "isabelle"): isabelle-scripts

#let pg(name) = "/shared/generated/playground/" + name
#let svg(name) = "/shared/generated/svg/" + name + ".svg"

#let code-card(body, w: 520pt, size: 24pt) = block(
  width: w,
  radius: 12pt,
  fill: rgb("#132A33"),
  inset: (x: 26pt, y: 20pt),
  {
    set text(fill: rgb("#E6EEF0"), size: size)
    set par(leading: 0.5em)
    body
  },
)

#let verdict-colour(v) = if v == "PROVED" { green } else if v == "REFUTED" {
  red
} else if v == "DEAD" { grey } else { amber }
#let verdict-tag(v) = box(inset: (x: 10pt, y: 5pt), radius: 6pt, fill: verdict-colour(v), text(
  fill: white,
  size: 20pt,
  weight: "bold",
  v,
))

// A coverage obligation's name, in the thesis's small capitals.
#let ob(name) = text(fill: vb.locale, weight: "bold", smallcaps(name))

// ============================================================ Motivation

#page(fill: night, margin: 0pt)[
  #metadata((
    id: 1,
    title: [Voblint],
    seconds: 20,
    notes: [
      Introduce yourself in one sentence. Voblint is short for verified
      Goblint. The question of the talk: can we trust what a program analyzer
      says?
    ],
  )) <talk-slide>
  #set text(fill: white)
  #block(height: 400pt, clip: true, width: 100%, image("assets/banner.png", width: 100%))
  #align(center)[
    #v(14pt)
    #text(size: 60pt, weight: "bold")[Voblint]
    #v(-16pt)
    #text(size: 28pt)[Verifying a context-sensitive abstract interpreter]
    #v(10pt)
    #text(size: 22pt, fill: grey)[
      Manuel Lerchner · Master's thesis · Technical University of Munich\
      Supervisors: Alexandra Graß and Helmut Seidl
    ]
  ]
]

#talk-slide(
  2,
  [Tests check #b(amber)[some] runs. An analysis covers #b(blue)[all] of them.],
  30,
  section: [Motivation],
  [
    #v(20pt)
    #align(center, image(svg("runs"), width: 1080pt))
  ],
  notes: [
    A static analyzer answers questions about every execution of a program
    at once: can this divisor be zero, is this point reachable, does this
    condition always hold. A passing test suite has seen finitely many runs
    (left). An analysis computes one region containing every run, tried or
    not (right). Developers act on these answers without running the
    program, so the answers have to be right.
  ],
)

#talk-slide(
  3,
  [Goblint: an #b(blue)[abstract interpreter for C]],
  40,
  section: [Motivation],
  [
    #grid(
      columns: (300pt, 1fr),
      column-gutter: 50pt,
      align: horizon,
      image("assets/goblint.svg", width: 280pt),
      [
        #set text(size: 26pt)
        Looks for
        #v(6pt)
        #let tag(body) = box(
          inset: (x: 12pt, y: 7pt),
          radius: 8pt,
          fill: white,
          stroke: 1.5pt + blue,
          text(size: 22pt, body),
        )
        #(
          (
            [user assertions],
            [integer overflows],
            [data races],
            [memory-safety errors],
            [memory leaks],
            [nontermination],
          )
            .map(tag)
            .join(h(8pt))
        )
        #v(26pt)
        One architecture for all of them: #b(blue)[analyses] and the #b(blue)[solver] meet at a
        side-effecting equation system, with #b(blue)[calling contexts].
        #v(20pt)
        #small[No false negative on the SV-COMP benchmarks since its first participation in 2021.]
      ],
    )
  ],
  sources: [Vojdani et al. 2016 · Seidl et al. 2026 · Saan 2026, §3.3],
  notes: [
    The analyzer this work is modelled on. Goblint is an abstract interpreter
    for C, developed for many years at TUM. Besides user-written checks it
    looks for integer overflows, data races, memory-safety errors, leaks and
    nontermination. Despite this range, its architecture is uniform: each
    analysis is defined independently of the solver, and they meet at a
    side-effecting equation system with calling contexts. It is tested well:
    no false negative on the SV-COMP benchmarks since 2021.
  ],
)

#talk-slide(
  4,
  [But analyzers are programs, and they give #b(red)[confident wrong answers]],
  45,
  section: [Motivation],
  [
    #v(10pt)
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      align: horizon,
      [
        #code-card(raw(
          "c = -5;   // or c = -7\n__voblint_check(c % 2 == 1);",
          lang: none,
        ))
        #v(30pt)
        #text(
          size: 26pt,
        )[Goblint, a static analyzer for C: #b(red)[more than a hundred] issues labeled #emph[unsound] since 2021.]
      ],
      grid(
        columns: (auto, 1fr),
        column-gutter: 20pt,
        row-gutter: 30pt,
        align: (right + horizon, left + horizon),
        text(size: 26pt, weight: "bold")[C11],
        [#text(
            size: 40pt,
            weight: "bold",
            fill: green,
          )[−5 % 2 = −1]\ #small[the remainder truncates toward zero]],

        text(size: 26pt, weight: "bold")[Goblint],
        [#text(
            size: 40pt,
            weight: "bold",
            fill: red,
          )[always 1]\ #small[the congruence domain ignored the sign]],
      ),
    )
    #v(30pt)
    #align(center, text(
      size: 28pt,
    )[A wrong answer is worse than no answer: nobody looks for the error.])
  ],
  sources: [Goblint issue 1156, fixed by pull request 1161 · Goblint issue tracker, label "unsound"],
  notes: [
    The analyzer is itself a program, and its errors produce confident
    answers that real runs contradict. Goblint's issue tracker has more than
    a hundred issues labeled unsound since 2021. One example: Goblint claimed
    c % 2 == 1 for c = −5 or −7. In C the remainder truncates toward zero, so
    the answer is −1. The congruence domain ignored the sign of the dividend.
    An imprecise answer leaves the question open; a wrong one gives nobody a
    reason to look.
  ],
)

#talk-slide(
  5,
  [Fixing one bug does not rule out the next: #b(blue)[proofs, checked by machines]],
  40,
  section: [Motivation],
  [
    #v(10pt)
    #align(center, cetz.canvas(length: 1cm, {
      import cetz.draw: *
      let milestone(x, y, year, name, tool, c) = {
        line((x, 0), (x, y), stroke: 1.5pt + c)
        circle((x, 0), radius: 0.12, fill: c, stroke: none)
        content(
          (x, y),
          anchor: if y > 0 { "south" } else { "north" },
          padding: 0.15,
          box(inset: 8pt, radius: 6pt, fill: white, stroke: 1pt + c, align(
            center,
            text(size: 21pt)[#text(weight: "bold", name)\ #text(
                size: 16pt,
                fill: grey,
              )[#year · #tool]],
          )),
        )
      }
      // Milestones sit at even spacing; the year labels carry the time.
      let x(i) = 1.6 + i * 4.6
      line((0, 0), (x(7) + 1.2, 0), stroke: 2.5pt + grey, mark: (end: ">"))
      content((-0.4, 0.5), anchor: "south-east", text(size: 18pt, fill: grey)[maths ↑])
      content((-0.4, -0.5), anchor: "north-east", text(size: 18pt, fill: grey)[software ↓])
      // Neighbouring cards alternate in height so they never overlap.
      milestone(x(0), -1.4, "2009", [seL4 kernel], "Isabelle", green)
      milestone(x(1), -4.4, "2009", [CompCert], "Coq", green)
      milestone(x(2), 1.4, "2015", [Kepler\ conjecture], "HOL Light, Isabelle", blue)
      milestone(x(3), 4.6, "2022", [Liquid\ Tensor], "Lean", blue)
      milestone(x(4), 1.4, "2025", [Busy\ Beaver 5], "Coq", blue)
      milestone(x(5), -1.4, "2026", [AWS Nitro\ hypervisor], "Isabelle", green)
      milestone(x(6), 4.6, "Sep 2026", [Navier–\ Stokes], "Lean", red)
      milestone(x(7), 1.4, "Nov 2026", [Riemann\ Hypothesis], "Lean", red)
    }))
  ],
  sources: [Red: formal proofs produced with AI systems in 2026. Sources: presentation-outline.md.],
  notes: [
    Fixing one bug does not rule out the next. Ruling out all of them needs a
    proof that the answers hold for every run, and an analyzer is too complex
    for a proof checked by reading it. Proof assistants do this at scale: a
    small trusted kernel checks every inference step. They have verified the
    CompCert compiler and the seL4 kernel, settled the Kepler conjecture, and
    in 2026 AI systems produced Lean proofs of a Navier–Stokes blow-up result
    and of the Riemann Hypothesis. Check the status of both the week of the
    talk.
  ],
)

#talk-slide(
  6,
  [The checker checks the proof, #b(red)[not the definitions]],
  50,
  section: [Motivation],
  [
    #v(40pt)
    #checked-chain([What we #b(blue)[mean]], [Formal #b(blue)[statement]\ + definitions], [
      Formal #b(blue)[proof]
    ])
    #v(50pt)
    #align(center, text(size: 24pt, fill: rgb("#444"))[
      Riemann (Nov 2026): a separate tool confirms the theorem #emph[is] Mathlib's statement.\
      Navier–Stokes (Oct 2026): "the formalised Lean proof does not correspond to the NL proof".\
      Voblint: the proof starts at #b(blue)[VIMP's semantics]; its adequacy for C is argued, not proved.
    ])
  ],
  sources: [Lean FRO and Mathlib Initiative, 21 Nov 2026 · Bastounis, Circelli, Hansen, arXiv 2610.08144],
  notes: [
    The kernel checks a proof only against the definitions it is given.
    Whether the statement and definitions say what we mean stays a human
    question. The Riemann certification therefore ran a separate statement
    check; for the Navier–Stokes result, a group argues the Lean proof does
    not match the published argument. For Voblint, the proof starts from the
    semantics of its input language, VIMP. Whether that models the C programs
    Goblint analyzes is argued in the thesis, not proved.
  ],
)

#talk-slide(
  7,
  [Goblint's architecture lets the proof #b(blue)[split along its modules]],
  40,
  section: [Motivation],
  [
    #v(20pt)
    #align(center, cetz.canvas(length: 1.35cm, {
      import cetz.draw: *
      let stage(x, label, c, note) = {
        rect((x - 2.6, -1.1), (x + 2.6, 1.1), radius: 0.25, fill: white, stroke: 2.5pt + c)
        content((x, 0), text(size: 20pt, weight: "bold", label))
        content((x, -1.5), anchor: "north", text(size: 17pt, fill: c, note))
      }
      stage(0, [VIMP\ program], ink, [source runs])
      stage(6, [Graph +\ contexts], blue, [this thesis])
      stage(12, [Equations], blue, [this thesis])
      stage(18, [TD solver], green, [verified before])
      stage(24, [Verdicts], blue, [this thesis])
      for x in (2.7, 8.7, 14.7, 20.7) {
        line((x, 0), (x + 0.6, 0), stroke: 2.5pt + grey, mark: (end: ">", fill: grey))
      }
      content((12, 3.2), text(
        size: 22pt,
      )[each domain, context policy and the solver proves #b(blue)[its own obligation]])
      line((6, 2.6), (6, 1.1), stroke: (paint: grey, dash: "dashed"))
      line((12, 2.6), (12, 1.1), stroke: (paint: grey, dash: "dashed"))
      line((18, 2.6), (18, 1.1), stroke: (paint: grey, dash: "dashed"))
    }))
    #v(30pt)
    #align(center, text(size: 26pt)[
      The solver's theorem says its result satisfies #emph[the equations].\
      Whether the equations describe #b(blue)[the program] is the missing link.
    ])
  ],
  sources: [TD solver: Stade et al. 2024, Tilscher, Graß, Seidl, NFM 2026 · Goblint: Vojdani et al. 2016, Seidl et al. 2026],
  notes: [
    Goblint defines each analysis independently of the solver, and the two
    meet at a side-effecting equation system. That gives a proof its
    modules: a domain proves its operations sound, a context policy proves its
    contexts agree with the real calls, the solver proves its result satisfies
    the equations, and generic theorems combine them. The top-down solver,
    with side effects, was already verified in Isabelle by prior work. Its
    theorem says nothing about whether the equations describe the program.
    That link, through calling contexts, is what this thesis proves.
  ],
)

#talk-slide(
  8,
  [What the user sees: #b(blue)[four verdicts]],
  35,
  section: [Motivation],
  [
    #grid(
      columns: (560pt, 1fr),
      column-gutter: 40pt,
      align: horizon,
      image(pg("clamp.png"), width: 100%),
      [
        #set text(size: 23pt)
        #let row(v, body) = block(below: 18pt, grid(
          columns: (150pt, 1fr),
          align: (left + horizon, left + horizon),
          verdict-tag(v), body,
        ))
        #row("PROVED", [holds whenever a run reaches the check])
        #row("REFUTED", [fails whenever a run reaches it; not a counterexample])
        #row("DEAD", [no run reaches the check])
        #row("UNKNOWN", [the analysis cannot decide])
        #small[Plus a warning at every division whose divisor might be zero.]
      ],
    )
  ],
  sources: [Playground run of the regression test 48-clamp_every_answer (thesis fig:intro-answers)],
  notes: [
    From the user's side, Voblint answers each check with one of four
    verdicts. PROVED and REFUTED say nothing about reachability; only DEAD
    does. A REFUTED check is a real error only if some run reaches it, which
    Voblint does not prove. This is the playground, which we will use live
    later.
  ],
)

// ======================================================= Language, example

#talk-slide(
  9,
  [Our language: VIMP, #b(blue)[a small C]],
  45,
  section: [Example],
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      align: horizon,
      [
        #set text(size: 24pt)
        #text(weight: "bold")[Expressions] #h(8pt) #small[(#isatype("exp"))]
        $
          e ::= & n | x | e + e | e - e | e * e | e \/ e | e % e \
              | & e < e | e <= e | e == e | dots | !e | e        && e | e || e
        $
        #v(12pt)
        #text(weight: "bold")[Commands] #h(8pt) #small[(#isatype("gcom"))]
        $
          c ::= & x := e | "check"(e) | c; c | "if" (e) {c} "else" {c} \
              | & "while" (e) {c} | [x :=] p(e, dots, e) | "return" e
        $
        #v(12pt)
        #text(size: 22pt)[
          #b(green)[Has:] unbounded integers, locals and globals, recursive
          procedures with value parameters, nondeterministic input.\
          #b(red)[Lacks:] pointers and heap, arrays and structs, machine
          integers, threads, floating point, `goto`.
        ]
      ],
      align(center, image(svg("island"), width: 100%)),
    )
  ],
  sources: [Thesis §3.1 (syntax) and §3.7 (comparison with C11)],
  notes: [
    VIMP is a small imperative language modelled on C: integer expressions
    where comparisons yield 0 or 1, and commands with assignment, checks,
    conditionals, loops, calls with an optional result, and return. It has
    unbounded integers, globals, and recursive procedures with value
    parameters. It leaves out what makes C hard: pointers and the heap,
    arrays and structs, machine integers, threads. Every construct needs a
    semantics, a compiler case and a sound transfer function in every
    domain, so the language is kept small. The picture places VIMP inside
    the C that Goblint analyzes.
  ],
)

#talk-slide(
  10,
  [A question about #b(blue)[every run]],
  40,
  section: [Example],
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      align: horizon,
      code-card(raw(read(pg("contexts.vimp")), lang: none)),
      cetz.canvas(length: 1.25cm, {
        import cetz.draw: *
        // The values a and b take, against what three abstractions keep.
        for i in range(0, 10) {
          line((i * 1.3, -0.15), (i * 1.3, 0.15), stroke: 1pt + grey)
          content((i * 1.3, -0.6), text(size: 18pt, fill: grey, str(i)))
        }
        line((-0.3, 0), (12.3, 0), stroke: 1.5pt + grey)
        circle((5 * 1.3, 0), radius: 0.22, fill: ink, stroke: none)
        circle((6 * 1.3, 0), radius: 0.22, fill: ink, stroke: none)
        content((5.5 * 1.3, 0.8), text(size: 20pt, weight: "bold")[runs: 5, 6])
        let band(y, from, to, c, label) = {
          rect(
            (from * 1.3, y - 0.3),
            (to * 1.3, y + 0.3),
            fill: c.transparentize(70%),
            stroke: 2pt + c,
            radius: 0.2,
          )
          content((-0.5, y), anchor: "east", text(size: 20pt, fill: c, weight: "bold", label))
        }
        band(-2.0, 1, 9.3, amber, [sign])
        band(-3.2, 5, 6, blue, [interval])
        band(-4.4, 0, 9.3, vb.called, [parity])
        content((9.6 * 1.3, -2.0), anchor: "west", text(size: 18pt, fill: grey)[positive])
        content((9.6 * 1.3, -3.2), anchor: "west", text(size: 18pt, fill: grey)[[5, 6]])
        content((9.6 * 1.3, -4.4), anchor: "west", text(size: 18pt, fill: grey)[any])
      }),
    )
  ],
  notes: [
    The running example. bump adds one; main calls it twice and asks two
    questions. Running it, both hold. An analyzer must answer for every
    input without running it, so it computes with abstract values: a sign,
    an interval, a parity. Each must contain every value a run produces and
    may contain more. Precision may be lost, a real value never.
  ],
)

#talk-slide(
  11,
  [From the graph to #b(blue)[equations]],
  45,
  section: [Example],
  [
    #grid(
      columns: (440pt, 1fr),
      column-gutter: 40pt,
      align: horizon,
      align(center, cetz.canvas(length: 1.9cm, {
        import cetz.draw: *
        let node(pos, name) = {
          circle(pos, radius: 0.55, fill: white, stroke: 2.5pt + ink)
          content(pos, text(size: 20pt, weight: "bold", name))
        }
        let edge(a, b, label, side, c: grey) = {
          line(a, b, stroke: 2pt + c, mark: (end: ">", fill: c))
          content((a, 50%, b), anchor: side, padding: 0.2, text(
            size: 17pt,
            font: "DejaVu Sans Mono",
            fill: if c == grey { ink } else { c },
            label,
          ))
        }
        node((0, 0), [E])
        node((0, -3), [H])
        node((2.6, -5), [B])
        node((0, -6.5), [X])
        edge((0, -0.6), (0, -2.4), [i := 0], "west")
        edge((0.45, -3.35), (2.15, -4.6), [i < 5], "south-west")
        edge((0, -3.6), (0, -5.9), [i ≥ 5], "east")
        bezier((2.9, -4.5), (0.6, -2.8), (3.6, -2.4), stroke: 2pt + red, mark: (
          end: ">",
          fill: red,
        ))
        content((3.2, -2.5), anchor: "south", text(
          size: 17pt,
          font: "DejaVu Sans Mono",
          fill: red,
        )[i := i + 1])
      })),
      [
        #set text(size: 26pt)
        #let eq(lhs, rhs, note) = block(
          width: 100%,
          inset: 14pt,
          radius: 10pt,
          fill: white,
          below: 12pt,
        )[
          #text(weight: "bold", lhs) $=$ #raw(rhs) \
          #text(size: 18pt, fill: grey, note)
        ]
        #eq([E], "⊤", [the entry: any store])
        #eq([H], "[i := 0] E ⊔ [i := i + 1] B", [two incoming edges, joined])
        #eq([B], "assume(i < 5) H", [the guard keeps only stores where it holds])
        #eq([X], "assume(i ≥ 5) H", [the loop exit])
      ],
    )
  ],
  sources: [The counting loop of thesis ch. 2, as on the project site],
  notes: [
    How does an analyzer compute? It turns the control-flow graph into one
    equation per node. The value at the loop head H is the join of what
    arrives along its two incoming edges: from the entry after i := 0, and
    from the body after i := i + 1. Guards filter. A solver finds values that
    satisfy all equations at once; with intervals, widening makes the loop
    finish. With procedures and contexts, the unknowns become pairs of node
    and context, which is where we go next.
  ],
)

#let ctx-policies = (
  ("ctx-demo-none", [None]),
  ("ctx-demo-entry", [Entry state]),
  ("ctx-demo-k1", [Call string, $k = 1$]),
  ("ctx-demo-k2", [Call string, $k = 2$]),
)
// Call sites of the demo program, named as on the project site.
#let site-names = ("pp18": "s1", "pp19": "s2", "pp4": "s3")
#let ctx-label(ctx) = if ctx == "unit" or ctx == "root context" { "[ ]" } else if ctx.starts-with(
  "call-string=",
) {
  "[" + ctx.slice(12).split(" ").map(x => site-names.at(x, default: x)).join(" ") + "]"
} else { ctx }
#let ctx-grid(claim) = {
  let snap = claim-snapshot(claim)
  let row(proc) = {
    let cs = snap.clusters.filter(c => c.proc == proc)
    grid(
      columns: (120pt, auto),
      column-gutter: 14pt,
      align: (right + horizon, left + horizon),
      text(size: 24pt, font: "DejaVu Sans Mono", proc),
      cs
        .map(c => box(
          inset: (x: 12pt, y: 10pt),
          radius: 8pt,
          fill: red.lighten(85%),
          stroke: 1.5pt + red,
          text(
            size: 20pt,
            font: "DejaVu Sans Mono",
            ctx-label(c.ctx),
          ),
        ))
        .join(h(10pt)),
    )
  }
  let verdict = snapshot-verdict(snap, "a == 2")
  [
    #row("main") #v(14pt) #row("wrap") #v(14pt) #row("scale")
    #v(26pt)
    #text(size: 26pt)[#raw("a == 2") #h(8pt) #verdict-tag(verdict)]
  ]
}

#talk-slide(
  12,
  [How many #b(blue)[copies] of a procedure?],
  60,
  section: [Example],
  steps: 4,
  step => grid(
    columns: (440pt, 1fr),
    column-gutter: 40pt,
    align: (left + horizon, left + horizon),
    [
      #code-card(
        raw(
          "fun scale(v) {\n  return v * 2;\n}\nfun wrap(w) {\n  r = scale(w); // s3\n  return r;\n}\nfun main() {\n  a = wrap(1);  // s1\n  b = wrap(4);  // s2\n  __voblint_check(a == 2);\n}",
          lang: none,
        ),
        w: 440pt,
        size: 21pt,
      )
      #v(14pt)
      #checklist(ctx-policies.map(p => p.at(1)), step)
    ],
    ctx-grid(ctx-policies.at(step - 1).at(0)),
  ),
  sources: [Context sets and verdicts from the analyzer's graph snapshots (claims ctx-demo-none, -entry, -k1, -k2); the listing is an excerpt of the regression program],
  notes: [
    Context sensitivity decides how many copies of a procedure the analysis
    keeps. With none, wrap(1) and wrap(4) share one copy, w is between 1 and
    4, and a == 2 is UNKNOWN. Entry-state contexts key each copy by the
    argument: two copies of wrap and of scale, and the check is PROVED. Call
    strings of length 1 key by the most recent call site: wrap gets two
    copies, but scale has only one call site, s3, so both calls meet there
    again: UNKNOWN. With length 2, scale is keyed by s3 plus s1 or s2, the
    calls stay apart, PROVED. More copies cost work and can buy precision.
  ],
)

// ============================================================ Formal part

// One run of the bump example: activation, node, and the value that matters.
#let act-colours = (ink, blue, vb.called)
#let chip(a, body) = box(
  inset: (x: 7pt, y: 4pt),
  radius: 5pt,
  fill: act-colours.at(a).lighten(85%),
  stroke: 1.2pt + act-colours.at(a),
  text(size: 20pt, font: "DejaVu Sans Mono", body),
)
#let run = (
  (0, [entry_main]),
  (0, [pp2]),
  (1, [entry_bump n=5]),
  (1, [pp0]),
  (1, [exit_bump ↩6]),
  (0, [pp3 a=6]),
  (2, [entry_bump n=4]),
  (2, [pp0]),
  (2, [exit_bump ↩5]),
  (0, [pp4 b=5]),
  (0, [⋯ exit_main]),
)
#let activation(a, name, steps, tag: none) = block(
  width: 100%,
  inset: 12pt,
  radius: 10pt,
  stroke: 2pt + act-colours.at(a),
  fill: white,
  below: 10pt,
)[
  #text(size: 22pt, weight: "bold", fill: act-colours.at(a), name)
  #if tag != none { h(10pt) + tag }
  #h(14pt)
  #steps.map(s => chip(a, s)).join(h(6pt))
]

#let story = (
  [One state per node],
  [Per (node, context)],
  [A flat run],
  [Activation traces],
)
#let small-cfg = cetz.canvas(length: 1.45cm, {
  import cetz.draw: *
  let n(pos, name, note: none) = {
    rect(
      (pos.at(0) - 1.6, pos.at(1) - 0.4),
      (pos.at(0) + 1.6, pos.at(1) + 0.4),
      radius: 0.15,
      fill: white,
      stroke: 1.5pt + ink,
    )
    content(pos, text(size: 15pt, font: "DejaVu Sans Mono", name))
    if note != none {
      content((pos.at(0) + 1.8, pos.at(1)), anchor: "west", text(size: 16pt, fill: blue, note))
    }
  }
  n((0, 0), [entry_main])
  n((0, -1.6), [pp2])
  n((0, -3.2), [pp3])
  n((0, -4.8), [pp4], note: [a ∈ [−∞, 6]])
  n((7, -1.6), [entry_bump], note: [n ∈ [4, 5]])
  n((7, -3.2), [pp0])
  n((7, -4.8), [exit_bump], note: [↩ [5, 6]])
  for (a, b) in (
    ((0, -0.4), (0, -1.2)),
    ((0, -2), (0, -2.8)),
    ((0, -3.6), (0, -4.4)),
    ((7, -2), (7, -2.8)),
    ((7, -3.6), (7, -4.4)),
  ) {
    line(a, b, stroke: 1.5pt + grey, mark: (end: ">", fill: grey))
  }
  line(
    (1.6, -1.6),
    (5.4, -1.6),
    stroke: (paint: vb.called, thickness: 1.5pt, dash: "dashed"),
    mark: (end: ">", fill: vb.called),
  )
  line(
    (1.6, -3.2),
    (5.4, -1.8),
    stroke: (paint: vb.called, thickness: 1.5pt, dash: "dashed"),
    mark: (end: ">", fill: vb.called),
  )
  content((3.5, -1.3), text(size: 14pt, fill: vb.called)[bump(5), bump(4)])
})
#let trace-datatype = [
  #set align(left)
  #set text(size: 26pt)
  $ t ::= "Root"(pi) | "Call"(t, pi) | "Resume"(t, t', pi) $
  #v(4pt)
  #small[π: the (node, store) pairs of one activation]
  #v(14pt)
  #set text(size: 22pt)
  #grid(
    columns: (auto, 1fr),
    column-gutter: 16pt,
    row-gutter: 12pt,
    raw("caller_of t"), [the activation that created $t$],
    raw("sink_node t"), [where $t$ is now],
    raw("sink_store t"), [its current store],
    raw("path_of t"), [its own steps],
  )
  #v(14pt)
  #text(
    size: 22pt,
  )[A return resumes #b(blue)[exactly its creating caller], found by #raw("caller_of"); no frame stack.]
]

#talk-slide(
  13,
  [Why we need a #b(blue)[trace semantics]],
  80,
  section: [Proof],
  steps: 4,
  step => grid(
    columns: (430pt, 1fr),
    rows: 500pt,
    column-gutter: 20pt,
    align: (left + horizon, center + horizon),
    [
      #checklist(story, step)
      #v(20pt)
      #small[#(
        (
          [Classical collecting semantics: the stores reaching each node.],
          [The analysis splits easily. But which concrete stores must state (v, c) cover?],
          [Contexts depend on how an activation was called. A flat run interleaves activations and forgets the caller after a return.],
          [Each activation keeps its caller; contexts can be read off a trace.],
        ).at(step - 1)
      )]
    ],
    if step == 1 { small-cfg } else if step == 2 {
      crop(pg("contexts.png"), 1734, 1286, 862, 80, 842, 1178, height: 480pt)
    } else if step == 3 {
      block(width: 100%)[
        #set align(left)
        #run.map(((a, x)) => chip(0, x)).join(h(5pt))
        #v(20pt)
        #text(
          size: 24pt,
        )[At #raw("exit_bump"): returning #b(red)[to which call?] In #b(red)[which context]?]
        #v(10pt)
        #small[The first prototype spliced callee runs into the caller's run; recursion broke it.]
      ]
    } else { trace-datatype },
  ),
  sources: [#isatype("activation_trace") · after the local traces of Schwarz et al., SAS 2021 · thesis §4.1, §15.1],
  notes: [
    Why do we need a new semantics at all? The natural analysis computes one
    abstract state per node of the graph, justified by the classical
    collecting semantics: the stores that reach each node. Context
    sensitivity splits each node into pairs of node and context, here a copy
    of bump per entry value. For the analysis that is easy. For the proof it
    raises a question: which concrete stores must the state at (exit_bump,
    n = 5) cover? Only those of runs that entered bump with 5. A run as a
    flat list of steps interleaves activations, and after a return it no
    longer says which call it returned to. My first prototype did exactly
    this, splicing callee runs into the caller's run; it handled single calls
    but broke on recursion. Activation traces keep one trace per activation
    and remember the creating caller. Accessors read off where a trace is,
    its store, and its caller, so a return resumes exactly its caller, and
    each trace carries its contexts.
  ],
)

#talk-slide(
  14,
  [Activation traces #b(blue)[on the example]],
  55,
  section: [Proof],
  steps: 3,
  step => [
    #text(size: 24pt, weight: "bold")[A run of the example, step by step]
    #v(6pt)
    #run.map(((a, s)) => chip(a, s)).join(h(5pt))
    #v(24pt)
    #if step >= 2 [
      #text(size: 24pt, weight: "bold")[The same run, grouped by activation]
      #v(6pt)
      #activation(0, [main], (
        [entry_main],
        [pp2],
        [↪ bump(5)],
        [pp3],
        [↪ bump(4)],
        [pp4],
        [⋯],
      ))
      #pad(left: 60pt, activation(
        1,
        [bump(5)],
        ([entry_bump n=5], [pp0], [exit_bump ↩6]),
        tag: if step >= 3 { b(blue)[context n = 5] },
      ))
      #pad(left: 60pt, activation(
        2,
        [bump(4)],
        ([entry_bump n=4], [pp0], [exit_bump ↩5]),
        tag: if step >= 3 { b(vb.called)[context n = 4] },
      ))
    ]
    #if step >= 3 [
      #v(8pt)
      #align(center, text(size: 26pt)[
        Flat: #h(6pt) $cal(C)("exit_bump") = {5, 6}$ #h(40pt)
        Per context: #h(6pt) $cal(A)("exit_bump", 5) = {6}$, #h(6pt) $cal(A)("exit_bump", 4) = {5}$
      ])
    ]
  ],
  sources: [#isatype("activation_trace") · #isaconst("node_collect") · #isaconst("activation_collect") · after the local traces of Schwarz et al., SAS 2021],
  notes: [
    Here is one run of the example as a flat list of steps; three activations
    interleave. Grouped by activation, each call opens a new trace that
    remembers its caller, and each return resumes the caller that made the
    call: one trace per activation, caller kept. A context can now be read
    off a trace, here the value of n on entry. Projecting contexts away gives
    the classical collecting semantics, where results 5 and 6 mix at
    exit_bump. Keeping them gives one set per context. That is what the
    context-sensitive analysis must cover. The construction adapts the local
    traces Schwarz et al. use for threads to procedure activations.
  ],
)

#talk-slide(
  15,
  [The proof contract: #b(blue)[five local obligations]],
  65,
  section: [Proof],
  [
    #grid(
      columns: (1fr, 330pt),
      column-gutter: 20pt,
      align: horizon,
      [
        #set text(size: 21pt)
        #let row(name, body) = block(below: 13pt, grid(
          columns: (110pt, 1fr),
          align: (left + horizon, left + horizon),
          ob(name), body,
        ))
        #row([Init], $s in S ==> s in "cover"(v_0, c_0)$)
        #row(
          [Intra],
          $(u, a, v) in "intra"(g), s in "cover"(u, c), s' in [|a|](s) ==> s' in "cover"(v, c)$,
        )
        #row(
          [Call],
          $s in "cover"(u, c), c' in "adm"_e (c, s) ==> "enter"_e (s) in "cover"("entry" p, c')$,
        )
        #row(
          [Return],
          [$s in "cover"(u, c)$, $c'$ admitted, $r in "cover"("result" p, c') ==> "combine"_e (s, r) in "cover"(k, c)$],
        )
        #row([Total], $s in "cover"(u, c) ==> "adm"_e (c, s) != emptyset$)
        #v(16pt)
        #block(inset: 16pt, radius: 10pt, fill: marker.lighten(40%))[
          #text(size: 24pt)[*Theorem.* The five obligations imply
            $cal(A)(v, c) subset.eq "cover"(v, c)$ for every node $v$ and context $c$.]
        ]
        #v(8pt)
        #small[#ob([Call]) and #ob([Return]) sit where Goblint runs `enter` and `combine`.]
      ],
      cetz.canvas(length: 1cm, {
        import cetz.draw: *
        let box-at(pos, label, c) = {
          rect(
            (pos.at(0) - 1.6, pos.at(1) - 0.55),
            (pos.at(0) + 1.6, pos.at(1) + 0.55),
            radius: 0.2,
            fill: white,
            stroke: 2pt + c,
          )
          content(pos, text(size: 17pt, label))
        }
        box-at((0, 0), [$v_0$, $c_0$], ink)
        box-at((0, -3.2), [$u$, $c$], ink)
        box-at((5, -3.2), [entry $p$, $c'$], vb.called)
        box-at((5, -6.4), [result $p$, $c'$], vb.called)
        box-at((0, -6.4), [$k$, $c$], ink)
        let arr(a, b, label, anchor, c) = {
          line(a, b, stroke: 2pt + c, mark: (end: ">", fill: c))
          content((a, 50%, b), anchor: anchor, padding: 0.2, text(size: 15pt, label))
        }
        arr((0, 1.6), (0, 0.6), ob([Init]), "west", ink)
        arr((0, -0.6), (0, -2.6), ob([Intra]), "west", ink)
        arr((1.65, -3.2), (3.35, -3.2), [#ob([Call])\ #ob([Total])], "south", vb.called)
        arr((5, -3.8), (5, -5.8), ob([Intra]), "west", vb.called)
        arr((3.35, -6.4), (1.65, -6.4), ob([Return]), "north", vb.called)
        line((0, -3.8), (0, -5.8), stroke: (paint: grey, thickness: 1.5pt, dash: "dashed"))
      }),
    )
  ],
  sources: [#isalocale("activation_coverage") · #isathm("activation_collect_sound") · Return shown simplified],
  notes: [
    How do we prove an analysis covers every trace without following every
    trace? Traces grow by four rules, so it is enough that each rule keeps us
    inside the analysis's claimed sets, the cover. One local obligation per
    rule, plus TOTAL: every call that can happen gets at least one context.
    Without TOTAL the theorem fails, and the thesis has a machine-checked
    counterexample. The theorem follows by induction over valid traces. In
    Isabelle this is a locale: any analysis that discharges the five
    obligations inherits the inclusion. CALL and RETURN sit exactly where
    Goblint runs enter and combine.
  ],
)

#let rungs = ([Source runs], [Graph traces], [Per-context sets], [Analyzer result])
#let ring-colours = (ink, vb.voblint, vb.locale, vb.solver)
#let nested(upto) = cetz.canvas(length: 1cm, {
  import cetz.draw: *
  let r(i) = 2.4 + 1.9 * i
  // Reserve the final frame so the figure does not move while it grows.
  rect((0, -r(3) * 0.8), (2 * r(3), r(3) * 0.8), stroke: none)
  for i in range(upto).rev() {
    circle((r(i), 0), radius: (r(i), r(i) * 0.8), fill: white, stroke: 3.5pt + ring-colours.at(i))
  }
  for p in ((1.6, -0.2), (2.6, -0.9), (2.1, -1.4), (3.2, -0.5)) {
    circle(p, radius: 0.13, fill: ink, stroke: none)
  }
})

#talk-slide(
  16,
  [Soundness is a chain of #b(blue)[set inclusions]],
  45,
  section: [Proof],
  steps: 4,
  step => grid(
    columns: (460pt, 1fr),
    rows: 480pt,
    align: (left + horizon, center + horizon),
    [
      #checklist(rungs, step, colours: ring-colours)
      #v(20pt)
      #small[Each step may add states: precision lost.\ None may drop one: soundness kept.]
    ],
    nested(step),
  ),
  notes: [
    Putting the pieces together at one program point. Every source run is a
    run on the compiled graph (a simulation proof). Every graph run is a
    valid trace, grouped by context. The contract puts every context's
    stores into the cover. The solver's result is such a cover, by the
    inherited solver theorem plus our equation soundness. Each inclusion is
    its own theorem; each may lose precision; none may lose a state.
  ],
)

#talk-slide(
  17,
  [The end-to-end theorem, #b(green)[as Isabelle states it]],
  50,
  section: [Proof],
  [
    #grid(
      columns: (1fr, 380pt),
      column-gutter: 30pt,
      align: horizon,
      block(width: 100%, radius: 12pt, fill: rgb("#132A33"), inset: 20pt, {
        set text(fill: rgb("#E6EEF0"), size: 16pt)
        set par(leading: 0.45em)
        raw(
          decode-isabelle(read("/shared/generated/snippets/run_voblint_source_sound.thy")),
          lang: "isabelle",
          block: true,
          syntaxes: isabelle-syntax,
        )
      }),
      [
        #set text(size: 22pt)
        #b(blue)[Assumes]
        - a start store (globals 0)
        - a finite source run to $(r, s, F)$
        - the analyzer returns a report `res`
        #v(14pt)
        #b(green)[Establishes] at every node $v$ the run is at:
        - $s$ is collected at $v$
        - $s$ is described by the report
        - $s$ satisfies every definite verdict
        #v(14pt)
        #b(amber)[Trusted:] parser, code generation, OCaml, browser.
      ],
    )
  ],
  sources: [#isathm("run_voblint_source_sound") · about #isaconst("run_voblint"), the function exported to the CLI and the browser],
  notes: [
    Composing the chain gives one theorem about run_voblint, the function the
    command line and the browser call. Take any start store and any finite
    run of the source program. If the analyzer returned a report, then at
    every node the run is at, its store is collected, described by the
    report, and satisfies every definite verdict. The run may be a prefix of
    a non-terminating one. If the solver does not terminate there is no
    report and nothing is claimed: partial correctness. Outside the proof:
    the parser, Isabelle's code generator and the OCaml and browser stack.
  ],
)

#let c-congr = claim-check("goblint-1161-congruence", "c % 2 == 1")
#let i-one = claim-check("goblint-1161-int", "c % 2 == 1")
#let i-neg = claim-check("goblint-1161-int", "c % 2 == -1")

#let pipe-box(title, sub, c: ink, dashed: false) = box(
  width: 128pt,
  height: 84pt,
  radius: 10pt,
  fill: white,
  stroke: (paint: c, thickness: 2pt, dash: if dashed { "dashed" } else { "solid" }),
  align(center + horizon)[
    #text(size: 19pt, weight: "bold", title)\
    #text(size: 15pt, fill: grey, sub)
  ],
)
#let arrow-r = text(size: 20pt, fill: grey)[→]

#talk-slide(
  18,
  [What is #b(green)[proved], what is #b(amber)[trusted]],
  40,
  section: [Proof],
  [
    #set align(center)
    #box(inset: 12pt, radius: 10pt, stroke: (paint: ink, thickness: 1.5pt, dash: "dashed"))[
      #text(size: 20pt, weight: "bold")[Source semantics: pstep and the operators] \
      #text(size: 16pt, fill: grey)[the one assumption no proof covers]
    ]
    #v(-4pt)
    #text(size: 26pt, fill: grey)[↓]
    #v(-6pt)
    #grid(
      columns: 5,
      column-gutter: 8pt,
      align: horizon,
      box(inset: 12pt, radius: 12pt, stroke: (paint: grey, thickness: 1.5pt, dash: "dashed"))[
        #text(size: 18pt, fill: grey, weight: "bold")[Unverified input] \
        #pipe-box([Source], [.vimp text], c: grey) #arrow-r #pipe-box(
          [Lexer + parser],
          [generated, tested],
          c: grey,
        )
      ],
      arrow-r,
      box(inset: 12pt, radius: 12pt, stroke: 3pt + green, fill: green.lighten(92%))[
        #text(size: 18pt, fill: green, weight: "bold")[Proved in Isabelle/HOL] \
        #pipe-box([Compiler], [AST → CFG], c: green) #arrow-r #pipe-box(
          [Equations],
          [point + context],
          c: green,
        ) #arrow-r #pipe-box([TD solver], [post-solution], c: green) #arrow-r #pipe-box(
          [Result],
          [verdicts],
          c: green,
        ) \
        #text(
          size: 18pt,
          fill: green,
          weight: "bold",
        )[theorem: if the solver finishes, the result covers every real store]
      ],
      arrow-r,
      box(inset: 12pt, radius: 12pt, stroke: (paint: grey, thickness: 1.5pt, dash: "dashed"))[
        #text(size: 18pt, fill: grey, weight: "bold")[Unverified output] \
        #pipe-box([Adapter, editor, graph], [handwritten], c: grey)
      ],
    )
    #v(10pt)
    #box(inset: 12pt, radius: 10pt, fill: vb.called.lighten(92%), stroke: (
      paint: vb.called,
      thickness: 1.5pt,
      dash: "dotted",
    ))[
      #text(size: 20pt, weight: "bold", fill: vb.called)[Trusted foundation] \
      #text(
        size: 17pt,
      )[Isabelle kernel · code generator and its target mappings · OCaml and wasm toolchain · Zarith · your browser]
    ]
  ],
  sources: [Project site, "What is verified"; the thesis's trust-boundary figure (fig:intro-trust)],
  notes: [
    The theorem covers the solid box: compiler, equations, solver and result.
    The lexer and parser lie outside it; they are generated from the grammar
    and tested. The handwritten OCaml that renders badges and graphs lies
    outside as well. Above the box sits the one thing no proof covers: the
    source semantics the theorem starts from. Below it, the trusted
    foundation: Isabelle's kernel, the code generator, the OCaml and
    WebAssembly toolchain, the bignum library, and the browser.
  ],
)

#talk-slide(
  19,
  [The remainder bug, #b(blue)[against a proof obligation]],
  45,
  section: [Proof],
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 50pt,
      [
        #text(size: 30pt, weight: "bold")[Goblint before the fix]
        #v(14pt)
        #card([Remainder operator\ returns 1], grey, w: 520pt, h: 100pt)
        #align(center, text(size: 40pt, fill: grey)[↓])
        #card(
          [#text(fill: red)[Wrong answer ships]\ #text(
              size: 20pt,
              weight: "regular",
            )[found by a user]],
          red,
          w: 520pt,
          h: 100pt,
        )
      ],
      [
        #text(size: 30pt, weight: "bold", fill: blue)[Voblint]
        #v(14pt)
        #card([Every remainder must\ #b(blue)[contain the real one]], blue, w: 520pt, h: 100pt)
        #align(center, text(size: 40pt, fill: red)[✗])
        #card(
          [#text(fill: green)[Isabelle refutes the operator]\ #text(
              size: 20pt,
              weight: "regular",
            )[counterexample: −5]],
          green,
          w: 520pt,
          h: 100pt,
        )
      ],
    )
    #v(4pt)
    #align(center)[
      #set text(size: 22pt)
      Same program, sound domains: #h(10pt) Congruence #verdict-tag(c-congr.at(3)) #h(24pt)
      Int: #raw(i-one.at(2)) #verdict-tag(i-one.at(3)) #h(6pt) #raw(i-neg.at(2)) #verdict-tag(i-neg.at(3))
    ]
  ],
  sources: [#isathm("congruence_mod_sound") · #isathm("prefix_congruence_mod_unsound")],
  notes: [
    Back to the bug from the start. In Voblint every abstract remainder
    carries an obligation: the real remainder of any two concrete values must
    lie in the abstract result. Goblint's pre-fix answer cannot meet it;
    Isabelle proves the opposite, with −5 as the witness. So that operator
    could not have been proved sound. On the same program, the sound
    congruence domain says UNKNOWN, and the combined Int domain refutes the
    wrong check and proves the right one.
  ],
)

#talk-slide(
  20,
  [The parts of the #b(blue)[formalization]],
  25,
  section: [Proof],
  [
    #grid(
      columns: (1fr, 400pt),
      column-gutter: 30pt,
      align: horizon,
      align(center, image("/assets/proof-map-treemap.png", height: 500pt)),
      [
        #set text(size: 22pt)
        #let layer(c, name, what) = block(below: 12pt)[
          #box(width: 18pt, height: 18pt, fill: c, radius: 3pt) #h(6pt) #text(
            weight: "bold",
            fill: c,
            name,
          ) \
          #text(size: 19pt, fill: rgb("#444"), what)
        ]
        #layer(metro.sem, [Semantics], [VIMP, the graph, activation traces])
        #layer(metro.comp, [Compiler], [VIMP to graph, simulation proof])
        #layer(metro.dom, [Domains], [sign, interval, parity, congruence, Int])
        #layer(metro.fw, [Framework], [analysis contract, contexts, coverage])
        #layer(metro.sol, [Solver], [the verified TD solver (inherited)])
        #layer(metro.res, [Result], [run_voblint and its verdicts])
        #v(8pt)
        #small[#stat("isabelle.lines") lines in #stat("isabelle.theories") theory files, without the vendored solver.]
      ],
    )
  ],
  sources: [Treemap of exported Isabelle declarations from the site's proof map; areas count entities, not proof difficulty],
  notes: [
    What the formalization consists of. Each block is an Isabelle session,
    each tile a theory, and the area counts exported declarations, not proof
    effort. Semantics and compiler relate source runs to the graph; domains
    and the framework show that the analyzer's states cover each node and
    context; the inherited solver solves the equations; the result layer
    composes everything into the theorem about run_voblint.
  ],
)

#talk-slide(
  21,
  [What runs, and #b(blue)[what holds it up]],
  30,
  section: [Proof],
  [
    #align(center, cetz.canvas(length: 1cm, {
      import cetz.draw: *
      let ice = rgb("#7A9AA3")
      rect((-17, -9.4), (17, 0), fill: rgb("#C9D8DD"), stroke: none)
      line((-17, 0), (17, 0), stroke: 2pt + ice)
      line(
        (-0.9, 0),
        (-0.4, 4),
        (0, 2.5),
        (0.4, 4.8),
        (0.9, 0),
        close: true,
        fill: white,
        stroke: 2pt + ice,
      )
      line(
        (-0.9, 0),
        (-3, -1.2),
        (-4, -4),
        (-3.3, -7),
        (0, -8.2),
        (2.9, -7),
        (3.9, -3.6),
        (3, -1.1),
        (0.9, 0),
        close: true,
        fill: rgb("#EEF3F4"),
        stroke: 2pt + ice,
      )
      line(
        (7, -5.6),
        (8.8, -5.1),
        (9.8, -6.4),
        (9.3, -8.2),
        (7.5, -8.5),
        (6.5, -7.3),
        close: true,
        fill: rgb("#EEF3F4"),
        stroke: 2pt + ice,
      )
      let label(pos, anchor, body) = content(pos, anchor: anchor, align(
        if anchor.contains("east") { right } else { left },
        body,
      ))
      label((1.6, 3.4), "west")[#text(
          size: 30pt,
          weight: "bold",
        )[#stat("generated_ocaml") lines] \ #text(
          size: 18pt,
        )[generated OCaml: the analyzer that runs]]
      label((4.4, -2.4), "west")[#text(
          size: 30pt,
          weight: "bold",
        )[#stat("isabelle.lines") lines of Isabelle] \ #text(
          size: 18pt,
        )[#stat("isabelle.theories") theories · #stat("isabelle.proofs") lemmas · #stat("isabelle.defs") definitions]]
      label((-4.6, -1.6), "east")[#text(
        size: 18pt,
      )[#stat("handwritten_ocaml") lines of handwritten OCaml \ parser glue, renderers, CLI, browser \ #emph[outside the proof]]]
      label((-4.6, -5.4), "east")[#text(
        size: 18pt,
      )[#stat("corpus.cases") regression programs \ #stat("eval_witnesses") evaluation witnesses \ #emph[tested, not proved]]]
      label((10.2, -6.8), "west")[#text(
          size: 24pt,
          weight: "bold",
        )[#stat("solver.used.lines") lines] \ #text(
          size: 16pt,
        )[of the vendored TD solver \ proof that Voblint imports]]
    }))
  ],
  sources: [Repository figures measured at build time (thesis stats)],
  notes: [
    What runs above the waterline is the generated OCaml, about thirteen
    thousand lines. Below it, about sixty thousand lines of Isabelle hold it
    up, plus the part of the verified solver proof it imports. Beside the
    proof: handwritten OCaml glue outside the proof, and the regression
    programs and evaluation witnesses, which are tested, not proved.
  ],
)

// ================================================================== Demo

#let domain-card(name, fig, line) = box(
  width: 186pt,
  height: 250pt,
  radius: 12pt,
  fill: white,
  stroke: 1.5pt + pale,
  inset: 12pt,
)[
  #align(center, box(height: 120pt, align(horizon, fig)))
  #v(6pt)
  #text(size: 22pt, weight: "bold", name)\
  #text(size: 16pt, fill: rgb("#444"), line)
]
#let lattice(top, mid, bot) = cetz.canvas(length: 0.85cm, {
  import cetz.draw: *
  let dot(pos, label) = {
    circle(pos, radius: 0.55, fill: white, stroke: 1.5pt + ink)
    content(pos, text(size: 11pt, label))
  }
  let w = (mid.len() - 1) * 1.6
  for (i, m) in mid.enumerate() {
    let x = i * 1.6 - w / 2
    line((0, 2.2), (x, 0), stroke: 1pt + grey)
    line((x, 0), (0, -2.2), stroke: 1pt + grey)
  }
  dot((0, 2.2), top)
  for (i, m) in mid.enumerate() { dot((i * 1.6 - w / 2, 0), m) }
  dot((0, -2.2), bot)
})

#talk-slide(
  22,
  [What Voblint #b(blue)[supports], all covered by the theorem],
  40,
  section: [Demo],
  [
    #grid(
      columns: 6,
      column-gutter: 10pt,
      domain-card([Sign], lattice([⊤], ([\<0], [0], [\>0]), [⊥]), [signs and their unions]),
      domain-card(
        [Interval],
        cetz.canvas(length: 1cm, {
          import cetz.draw: *
          line((0, 0), (4.6, 0), stroke: 1.5pt + grey)
          rect((1.2, -0.3), (3.2, 0.3), radius: 0.1, fill: pale, stroke: 1.5pt + ink)
          content((2.2, 0.9), text(size: 15pt, font: "DejaVu Sans Mono")[[−2, 5]])
        }),
        [bounds, with widening],
      ),
      domain-card([Parity], lattice([⊤], ([even], [odd]), [⊥]), [even or odd]),
      domain-card(
        [Congruence],
        cetz.canvas(length: 1cm, {
          import cetz.draw: *
          line((0, 0), (4.6, 0), stroke: 1.5pt + grey)
          for i in range(10) {
            let hit = calc.rem(i, 3) == 2
            circle(
              (0.3 + i * 0.45, 0),
              radius: if hit { 0.16 } else { 0.07 },
              fill: if hit { amber } else { grey },
              stroke: none,
            )
          }
          content((2.3, 0.8), text(size: 15pt, font: "DejaVu Sans Mono")[x ≡ 2 mod 3])
        }),
        [remainders],
      ),
      domain-card(
        [Int],
        block(inset: 4pt, {
          set text(size: 12pt, font: "DejaVu Sans Mono")
          grid(
            columns: 2,
            column-gutter: 8pt,
            row-gutter: 6pt,
            [sign], [\>0],
            [interval], [[1,9]],
            [parity], [odd],
            [congr.], [1 mod 4],
          )
        }),
        [the four, refining each other],
      ),
      domain-card(
        [Order],
        text(size: 22pt)[$x < y$\ $y <= z$],
        [relational facts between variables],
      ),
    )
    #v(24pt)
    #set text(size: 22pt)
    #grid(
      columns: (auto, 1fr),
      column-gutter: 20pt,
      row-gutter: 12pt,
      text(weight: "bold")[Contexts], [none · entry state · call string of length $k$],
      text(weight: "bold")[Global updates],
      [join · join per origin · warrow · warrow per origin · bounded narrowing],

      text(weight: "bold")[Program globals], [flow-sensitive · flow-insensitive],
    )
  ],
  sources: [Thesis ch. 11 (instances) · the end-to-end theorem holds under every configuration run_voblint offers (§10.4)],
  notes: [
    What you can select, before we try it. Four non-relational numeric
    domains: sign, interval, parity, congruence. Int is their reduced
    product, where the components sharpen one another. Order is a relational
    analysis that tracks facts like x < y between variables; it shows the
    framework is not limited to per-variable maps. Analyses can be combined
    and answer each other's queries. Contexts: none, the entry state, or
    call strings of bounded length. Several update rules for shared values,
    and globals kept per point or shared. The end-to-end theorem holds for
    every one of these configurations.
  ],
)

#let try-row(what, links) = block(below: 14pt, grid(
  columns: (420pt, 1fr),
  column-gutter: 20pt,
  align: (left + horizon, left + horizon),
  text(size: 24pt, weight: "bold", what),
  links
    .map(((label, url)) => link(url, box(
      inset: (x: 12pt, y: 7pt),
      radius: 8pt,
      fill: white,
      stroke: 1.5pt + blue,
      text(size: 20pt, fill: blue)[#label ↗],
    )))
    .join(h(10pt)),
))

#talk-slide(
  23,
  [Now: #b(blue)[the playground]],
  130,
  section: [Demo],
  [
    #v(10pt)
    #try-row([Calling contexts], (
      ([none], claim-playground-link("ctx-demo-none")),
      ([call string 1], claim-playground-link("ctx-demo-k1")),
      ([call string 2], claim-playground-link("ctx-demo-k2")),
      ([entry state], claim-playground-link("ctx-demo-entry")),
    ))
    #try-row([Mixed flow sensitivity: globals], (
      ([flow-sensitive], claim-playground-link("mixed-flow-sign")),
      ([flow-insensitive], claim-playground-link("mixed-flow-sign-shared", graph: "analysis")),
    ))
    #try-row([The remainder bug], (
      ([congruence], claim-playground-link("goblint-1161-congruence")),
      ([Int], claim-playground-link("goblint-1161-int")),
    ))
    #try-row([All four verdicts], (([clamp], claim-playground-link("intro-answers")),))
    #try-row([Watch the solver], (
      (
        [replay bump],
        playground-link(read(pg("contexts.vimp")), ctx: "entry-state", trace: "verbose"),
      ),
    ))
    #v(16pt)
    #small[Runs code generated by Isabelle from #raw("run_voblint"), compiled to WebAssembly. Each link opens the program with its settings.]
  ],
  notes: [
    Live demo, about two minutes; click the links. 1. Contexts: the scale/wrap
    program under none, call string 1, call string 2, entry state; watch the
    graph grow a box per context and a == 2 flip to PROVED. 2. Mixed flow
    sensitivity: the same program with globals carried in each point's state,
    then on one shared, flow-insensitive unknown per global; 0 < y is proved
    only in the first. This is the D/G split Goblint uses for threads. 3. The
    remainder bug: congruence says UNKNOWN, Int refutes the wrong check. 4.
    Clamp shows all four verdicts. 5. Turn on the trace and step through the
    solve. Fallback: the backup slides.
  ],
)

// ============================================================ Conclusion

#let alignment = json("/shared/generated/goblint-alignment.json").rows
#let count(status) = alignment.filter(r => r.status == status).len()

#talk-slide(
  24,
  [Relevance to Goblint, and #b(amber)[limits]],
  40,
  section: [Conclusion],
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 50pt,
      [
        #text(
          size: 26pt,
          weight: "bold",
        )[Of #alignment.len() compared aspects of Goblint's framework]
        #v(10pt)
        #let bar(n, c, label) = grid(
          columns: (auto, 1fr),
          column-gutter: 12pt,
          align: horizon,
          box(width: n * 26pt, height: 34pt, fill: c, radius: 4pt),
          text(size: 24pt)[#b(c)[#n] #label],
        )
        #bar(count("modeled"), green, [modeled])
        #v(6pt)
        #bar(count("simplified"), amber, [simplified])
        #v(6pt)
        #bar(count("absent"), red, [absent])
        #v(24pt)
        #text(size: 24pt)[Goblint's architecture #b(blue)[admits a modular soundness proof].]
      ],
      [
        #set text(size: 23pt)
        #b(green)[Useful for Goblint]
        - replay a defect as a counterexample theorem
        - check a proposed domain operation first
        - export verified components as OCaml
        #v(14pt)
        #b(red)[Limits]
        - VIMP is not C: no pointers, heap, threads, machine integers
        - VIMP's adequacy is argued, not proved
        - precision only shown on examples
      ],
    )
  ],
  sources: [Comparison rows of the project site, Goblint revision 5320a6b · thesis §15.2],
  notes: [
    The correspondence with Goblint is architectural: the proofs are about
    Voblint's definitions, so they do not show Goblint correct. They show
    that Goblint's architecture admits a soundness proof that composes along
    its own boundaries. The comparison on the project site counts which
    aspects are modeled, simplified or absent. For Goblint's developers it is
    still largely a proof of concept, but it can replay a defect as a
    counterexample theorem, check a proposed operation against its
    obligation, or supply verified components. The largest gap is VIMP
    versus C.
  ],
)

#talk-slide(
  25,
  [Outlook: towards #b(blue)[C and Goblint]],
  40,
  section: [Conclusion],
  [
    #v(30pt)
    #grid(
      columns: (1fr, 1fr, 1fr),
      column-gutter: 30pt,
      card(
        [#text(fill: green)[Fits the current proof]\ #text(
            size: 21pt,
            weight: "regular",
          )[relational domains (octagons, polyhedra), path-sensitive analyses]],
        green,
        w: 360pt,
        h: 230pt,
      ),
      card(
        [#text(fill: amber)[New step functions]\ #text(
            size: 21pt,
            weight: "regular",
          )[machine integers (PR 357), then a bitfield domain; a heap]],
        amber,
        w: 360pt,
        h: 230pt,
      ),
      card(
        [#text(fill: red)[Revisit the traces]\ #text(
            size: 21pt,
            weight: "regular",
          )[pointers into a caller's frame, threads]],
        red,
        w: 360pt,
        h: 230pt,
      ),
    )
    #v(40pt)
    #align(center, text(size: 26pt)[
      AI tools wrote many of these proofs, and got #b(blue)[consistently better] during the project.
    ])
  ],
  sources: [Thesis §15.3 · Voblint PR 357 · Goblint PR 1623 (bitfield domain)],
  notes: [
    Some extensions fit the current proof, because each soundness proof
    stays within its own obligations: relational domains, path-sensitive
    analyses. Others need new step functions: machine integers, developed
    separately in pull request 357, after which Goblint's bitfield domain is
    a natural next analysis; and a heap, which like a global passes between
    caller and callee. Pointers into a caller's frame and threads break the
    separation the trace semantics relies on, so they require revisiting it.
    AI-assisted tools produced many of the proofs here and improved over the
    project; that may bring such revisions within reach.
  ],
)

#statement-slide(
  26,
  25,
  [Conclusion],
  [
    The soundness of a #b(blue)[Goblint-style analyzer] with calling
    contexts, side effects and a verified solver can be
    #b(green)[machine-checked], from #b(blue)[source executions] to the
    #b(blue)[verdicts] of the analyzer that runs.
  ],
  notes: [
    One sentence summary, from the thesis conclusion. A PROVED verdict now
    rests on a proof, not on the tests the analyzer has passed. Thank you;
    questions.
  ],
)

// ============================================================== Backups

#talk-slide(
  101,
  [Backup: what is inherited, what is new],
  0,
  [
    #v(30pt)
    #grid(
      columns: (1fr, 1fr, 1fr),
      column-gutter: 30pt,
      card(
        [#text(fill: grey)[Goblint]\ #text(
            size: 20pt,
            weight: "regular",
          )[local/global split,\ enter/combine protocol]],
        grey,
        w: 340pt,
        h: 220pt,
      ),
      card(
        [#text(fill: grey)[Prior proofs]\ #text(
            size: 20pt,
            weight: "regular",
          )[local traces (SAS 2021),\ verified solver (NFM 2026)]],
        grey,
        w: 340pt,
        h: 220pt,
      ),
      card(
        [#text(fill: blue)[This thesis]\ #text(
            size: 20pt,
            weight: "regular",
          )[source semantics to verdicts,\ context-indexed coverage,\ executable analyzer]],
        blue,
        w: 340pt,
        h: 220pt,
      ),
    )
  ],
  sources: [Schwarz et al., SAS 2021 · Tilscher, Graß, Seidl, NFM 2026],
  notes: [
    If asked about the contribution: the solver and side-effecting equations
    come from prior work, the D/G architecture from Goblint, the trace idea
    from Schwarz et al. This thesis connects them to source executions
    through context-indexed semantics and ships the executable analyzer.
  ],
)

#talk-slide(
  102,
  [Backup: watching the solver work],
  0,
  [
    #align(center, crop(pg("solve-replay-still.png"), 2088, 1472, 0, 0, 2088, 1472, height: 500pt))
  ],
  notes: [
    Demo fallback. The playground replays the solve step by step: which
    unknown is evaluated, which call is entered, when a callee's entry state
    is published. Here the first call into a context reads its callee's seed.
  ],
)

#talk-slide(
  103,
  [Backup: combining domains #b(blue)[proves more]],
  0,
  [
    #align(center, image(pg("int-refinement.png"), height: 500pt))
  ],
  notes: [
    Demo fallback, one precision example. y + 1 == 3 implies y is 2. Sign,
    interval and parity alone answer UNKNOWN; the reduced product Int proves
    y == 2.
  ],
)
