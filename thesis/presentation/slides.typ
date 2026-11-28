// The thesis talk. It opens like the thesis introduction (wrong answers,
// machine-checked proofs, Goblint's architecture), works through one example
// into the formal argument, demonstrates the playground live, and closes like
// the thesis conclusion (relevance to Goblint, limits, outlook).
#import "theme.typ": *
#import "../lib/code.typ": (
  claim-playground-link, decode-isabelle, isabelle-scripts, isabelle-syntax, isaconst, isalink,
  isalocale, isathm, isatype, listing, playground-link, site,
)
#import "../lib/claims.typ": claim-check, claim-snapshot, snapshot-cluster-of, snapshot-verdict
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
  fill: rgb("#EAEFEF"),
  stroke: 1pt + pale,
  inset: (x: 26pt, y: 20pt),
  {
    set text(size: size)
    set par(leading: 0.5em)
    body
  },
)
// A VIMP listing at slide size, linked to the playground by its tag.
#let vimp(src, size: 24pt, ..args) = {
  set text(size: size)
  listing(src, lang: "c", ..args)
}

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
  35,
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
        #vimp("c = -5;   // or c = -7\n__voblint_check(c % 2 == 1);", claim: "goblint-1161-int")
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

// Call sites of the demo program, named as on the project site.
#let site-names = ("pp18": "s1", "pp19": "s2", "pp4": "s3")
#let ctx-params = ("wrap": "w", "scale": "v")
#let ctx-name(proc, ctx) = if ctx == "unit" or ctx == "root context" {
  "()"
} else if ctx.starts-with(
  "call-string=",
) {
  "[" + ctx.slice(12).split(" ").map(x => site-names.at(x, default: x)).join(" ") + "]"
} else {
  let m = ctx.match(regex("^\\[(-?\\d+),(-?\\d+)\\]$"))
  if m != none and m.captures.at(0) == m.captures.at(1) {
    "(" + ctx-params.at(proc, default: "x") + "=" + m.captures.at(0) + ")"
  } else { "(" + ctx-params.at(proc, default: "x") + "∈" + ctx + ")" }
}
// Node rows per procedure, top to bottom as on the project site.
#let ctx-rows = (("scale", 2), ("wrap", 3), ("main", 4))
// Call edges: (caller, call row, continuation row, callee) by call text.
#let ctx-calls = (
  "wrap(1)": ("main", 1, 2, "wrap"),
  "wrap(4)": ("main", 2, 3, "wrap"),
  "scale(w)": ("wrap", 1, 2, "scale"),
)
#let ctx-figure(claim) = {
  let snap = claim-snapshot(claim)
  let procs = ctx-rows.map(r => r.at(0))
  let cl = snap.clusters.filter(c => c.proc in procs)
  let cols = ()
  for p in ("main", "wrap", "scale") {
    for c in cl.filter(c => c.proc == p) {
      let n = ctx-name(p, c.ctx)
      if n not in cols { cols.push(n) }
    }
  }
  let col-of(c) = cols.position(x => x == ctx-name(c.proc, c.ctx))
  let ys = (:)
  let y = 0
  for (p, k) in ctx-rows {
    ys.insert(p, y)
    y -= k * 0.55 + 0.45
  }
  let pos(p, col, row) = (col * 1.5, ys.at(p) - row * 0.55)
  cetz.canvas(length: 1.2cm, {
    import cetz.draw: *
    for (i, n) in cols.enumerate() {
      content((i * 1.5, 0.65), text(size: 11pt, font: "DejaVu Sans Mono", n))
    }
    for (p, k) in ctx-rows {
      content((-0.8, ys.at(p) - (k - 1) * 0.31), anchor: "east", text(
        size: 13pt,
        font: "DejaVu Sans Mono",
        p,
      ))
      for i in range(cols.len()) {
        let live = cl.any(c => c.proc == p and col-of(c) == i)
        for r in range(k) {
          rect(
            (i * 1.5 - 0.22, ys.at(p) - r * 0.55 - 0.2),
            (i * 1.5 + 0.22, ys.at(p) - r * 0.55 + 0.2),
            radius: 0.08,
            fill: if live { red.lighten(85%) } else { none },
            stroke: if live { 1pt + red } else {
              (paint: grey.lighten(40%), thickness: 0.6pt, dash: "dashed")
            },
          )
        }
      }
    }
    for e in snap.edges {
      for (call, (caller, row, cont, callee)) in ctx-calls {
        let src = snapshot-cluster-of(snap, e.src)
        let dst = snapshot-cluster-of(snap, e.dst)
        if src == none or dst == none { continue }
        if e.label == "enter " + call {
          let a = pos(caller, col-of(src), row)
          let b = pos(callee, col-of(dst), 0)
          bezier(
            (a.at(0) + 0.25, a.at(1)),
            (b.at(0) - 0.25, b.at(1)),
            ((a.at(0) + b.at(0)) / 2, b.at(1) + 0.3),
            stroke: (paint: vb.called, thickness: 1pt, dash: "dashed"),
            mark: (end: ">", fill: vb.called, size: 0.15),
          )
        }
        if e.label.starts-with("combine") and e.label.ends-with(call) {
          let a = pos(callee, col-of(src), (ctx-rows.find(r => r.at(0) == callee)).at(1) - 1)
          let b = pos(caller, col-of(dst), cont)
          bezier(
            (a.at(0) - 0.25, a.at(1)),
            (b.at(0) + 0.25, b.at(1)),
            ((a.at(0) + b.at(0)) / 2, b.at(1) - 0.3),
            stroke: 1pt + ink,
            mark: (end: ">", fill: ink, size: 0.15),
          )
        }
      }
    }
  })
}
#let ctx-a(claim) = {
  let snap = claim-snapshot(claim)
  let n = snap.nodes.values().find(n => "check a == 2" in n.lines)
  let a = n.lines.find(l => l.starts-with("a="))
  (snapshot-verdict(snap, "a == 2"), a)
}

#talk-slide(
  10,
  [Calling contexts decide #b(blue)[precision]],
  70,
  section: [Example],
  [
    #grid(
      columns: (270pt, 1fr),
      column-gutter: 24pt,
      align: (left + top, left + top),
      [
        #vimp(
          "fun scale(v) {\n  return v * 2;\n}\nfun wrap(w) {\n  r = scale(w); // s3\n  return r;\n}\nfun main() {\n  a = wrap(1);  // s1\n  b = wrap(4);  // s2\n  __voblint_check(a == 2);\n}",
          size: 17pt,
          claim: "ctx-demo-entry",
        )
        #v(10pt)
        #small[Excerpt of the regression program. Purple: enter a callee context; black: combine back into the caller.]
      ],
      grid(
        columns: (1fr, 1fr, 1fr),
        column-gutter: 16pt,
        align: center + top,
        ..(
          ("ctx-demo-none", [None], [one copy of each procedure: both calls of wrap meet]),
          (
            "ctx-demo-k1",
            [Call string, $k = 1$],
            [wrap splits by call site, but scale has one site, s3: the calls meet again],
          ),
          ("ctx-demo-entry", [Entry state], [one copy per argument: the calls never meet]),
        ).map(((claim, name, why)) => {
          let (verdict, a) = ctx-a(claim)
          [
            #text(size: 22pt, weight: "bold", name)
            #v(4pt)
            #box(height: 260pt, align(horizon, ctx-figure(claim)))
            #v(4pt)
            #raw("a == 2") #h(4pt) #verdict-tag(verdict) \
            #text(size: 14pt, fill: grey, raw(a)) \
            #v(2pt)
            #text(size: 16pt, fill: rgb("#444"), why)
          ]
        }),
      ),
    )
  ],
  sources: [Contexts, arrows, values and verdicts from the analyzer's graph snapshots (claims ctx-demo-none, ctx-demo-k1, ctx-demo-entry)],
  notes: [
    Context sensitivity decides how many copies of a procedure the analysis
    keeps, and that decides precision. With none, wrap(1) and wrap(4) share
    one copy of wrap and scale; the argument covers both calls, a is not
    determined, and a == 2 is UNKNOWN. A call string of length 1 splits wrap
    by its call sites s1 and s2, but scale is only ever called from s3, so
    both calls meet again in scale: still UNKNOWN. Entry-state contexts key
    each copy by the argument value: wrap and scale get one copy per value,
    a is exactly 2, PROVED. More copies cost work and buy precision.
  ],
)

// ============================================================ Formal part

// The soundness chain at a node, revealed as the talk establishes each link.
#let chain-links = (
  ($s$, none),
  ($in cal(C)(v)$, [graph]),
  ($= union.big_c cal(A)(v, c)$, [traces]),
  ($subset.eq cal(R)_"res" (v)$, [analysis]),
  ($subset.eq cal(V)_"res" (v)$, [verdicts]),
)
#let chain-strip(n) = {
  set text(size: 20pt)
  chain-links
    .enumerate()
    .map(((i, (rel, label))) => {
      let now = i == n and n > 0
      box(
        inset: (x: 5pt, y: 3pt),
        radius: 5pt,
        fill: if now { marker } else { none },
        text(fill: if now { ink } else if i <= n { white } else { grey.darken(20%) }, rel),
      )
    })
    .join(h(3pt))
}

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
  11,
  [Layer 1: #b(blue)[one state per node]],
  40,
  section: chain-strip(1),
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      align: horizon,
      small-cfg,
      [
        #set text(size: 25pt)
        The control-flow graph gives #b(blue)[one equation per node]: a node's state joins what its incoming edges produce.
        #v(16pt)
        The solution must cover the #b(blue)[collecting semantics] $cal(C)(v)$: every store a run has at node $v$.
        #v(16pt)
        Every source run is a run of the graph #small[(simulation proof)].
      ],
    )
  ],
  sources: [#isaconst("node_collect") · #isathm("source_reaches_node_collect")],
  notes: [
    The classical picture. The analyzer works on the control-flow graph and
    computes one abstract state per node, as the solution of one equation
    per node: the state at a node joins what its incoming edges produce. Its
    states must cover the collecting semantics, the set of stores real runs
    have at each node. The first link of the chain: every source run is
    matched by a run of the compiled graph, so its store is in C(v).
  ],
)

#talk-slide(
  12,
  [Layer 2: #b(blue)[one state per (node, context)]],
  40,
  section: chain-strip(1),
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      align: horizon,
      align(center, crop(pg("contexts.png"), 1734, 1286, 862, 80, 842, 1178, height: 470pt)),
      [
        #set text(size: 25pt)
        With entry-state contexts, bump has #b(blue)[one copy per argument].
        #v(16pt)
        The state at (exit_bump, $n = 5$) only has to cover runs that #b(blue)[entered bump with 5].
        #v(16pt)
        $cal(C)("exit_bump") = {5, 6}$ mixes both calls. #b(red)[It cannot say which store belongs to which context.]
      ],
    )
  ],
  notes: [
    Context sensitivity splits every node into pairs of node and context;
    here bump gets one copy per entry value. For the analysis that is easy.
    For the proof it raises a question: which concrete stores must the state
    at exit_bump in context n = 5 cover? Only those of runs that entered bump
    with 5. The collecting semantics cannot express that: at exit_bump it
    holds 5 and 6, and forgets which call produced which.
  ],
)

#talk-slide(
  13,
  [Layer 3: #b(red)[a run as a flat list?]],
  40,
  section: chain-strip(1),
  [
    #v(20pt)
    #run.map(((a, x)) => chip(0, x)).join(h(5pt))
    #v(40pt)
    #set text(size: 25pt)
    A step's context depends on #b(blue)[how its activation was called].
    #v(14pt)
    In a flat run, activations #b(red)[interleave], and after a return nothing says #b(red)[which call returned].
    #v(14pt)
    #small[The first prototype spliced each callee's run into its caller's run. It handled single calls and broke on recursion.]
  ],
  sources: [Thesis §4.1 and §15.1 (design record)],
  notes: [
    The obvious fix is to look at whole runs. Here is one run of the example
    as a flat list of steps. To know the context of exit_bump, we need the
    call that created this activation. In a flat list, the steps of main and
    the two bump activations interleave, and once the frame is popped after
    a return, nothing records which call returned. My first prototype did
    this, splicing callee runs into the caller's run; it handled single calls
    but not recursion.
  ],
)

#talk-slide(
  14,
  [Layer 4: #b(green)[activation traces]],
  45,
  section: chain-strip(2),
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      align: horizon,
      trace-datatype,
      [
        #set text(size: 25pt)
        Each trace #b(blue)[carries its contexts], read off how it was called.
        #v(16pt)
        $cal(A)(v, c)$: the stores of valid traces that end at $v$ and carry $c$.
        #v(16pt)
        Every trace carries a context, so $cal(C)(v) = union.big_c cal(A)(v, c)$.
      ],
    )
  ],
  sources: [#isatype("activation_trace") · #isaconst("activation_collect") · #isathm("node_collect_eq_Union_activation_of_has_context") · after the local traces of Schwarz et al., SAS 2021],
  notes: [
    Activation traces keep one trace per activation and remember the creating
    caller. A call starts a new trace that points to its caller; a return
    resumes exactly that caller. The accessors read off where a trace is,
    its store and its caller. Now a context can be read off a trace, and the
    collecting semantics splits by context: A(v, c) are the stores of traces
    that end at v and carry c. Since every trace carries a context, C(v) is
    the union of the A(v, c). Second link of the chain.
  ],
)

#talk-slide(
  15,
  [Activation traces #b(blue)[on the example]],
  50,
  section: chain-strip(2),
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
  16,
  [The proof contract: #b(blue)[five local obligations]],
  65,
  section: chain-strip(3),
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

#talk-slide(
  17,
  [The end-to-end theorem],
  50,
  section: chain-strip(4),
  [
    #v(30pt)
    #set text(size: 26pt)
    #align(center)[
      $
        underbrace(("main", s_0, []) ->_p^* (r, s, F), "a finite source run")
        quad ==> quad
        underbrace(exists v. med (r, s, F) ⊳ v, "observed at a node")
      $
      #v(10pt)
      $
        and quad forall v. med (r, s, F) ⊳ v ==>
        underbrace(s in cal(C)(v), "collected")
        and underbrace(s in cal(R)_"res" (v), "described by the report")
        and underbrace(s in cal(V)_"res" (v), "satisfies the verdicts")
      $
    ]
    #v(20pt)
    #align(center, text(
      size: 22pt,
    )[whenever #raw("run_voblint") returns a report #raw("res"), for every start store with globals 0])
  ],
  sources: [#isathm("run_voblint_source_sound"); the four links: #isathm("source_reaches_node_collect"), #isathm("node_collect_eq_Union_activation_of_has_context"), #isathm("run_voblint_covers"), #isathm("analysis_report_verdicts_sound")],
  notes: [
    Chaining the links gives the end-to-end theorem about run_voblint, the
    function the command line and the browser call. Take any finite run of
    the source program from a start store. Then the run is observed at some
    node, and at every node it is observed at, its store is collected, is
    described by the report, and satisfies every definite verdict. The run
    may be a prefix of a non-terminating one. If the solver does not finish
    there is no report and nothing is claimed: partial correctness.
  ],
)

#let formal-link(body) = box(
  inset: (x: 12pt, y: 7pt),
  radius: 8pt,
  fill: white,
  stroke: 1.5pt + green,
  text(size: 20pt, body),
)

#talk-slide(
  18,
  [Now: #b(green)[the formalization]],
  90,
  section: [Proof],
  [
    #v(10pt)
    #set text(size: 24pt)
    #grid(
      columns: (330pt, 1fr),
      column-gutter: 20pt,
      row-gutter: 18pt,
      align: (left + horizon, left + horizon),
      text(weight: "bold")[The whole development],
      formal-link(link(site("formalization.pdf"))[formalization.pdf ↗]),

      text(weight: "bold")[Source semantics], formal-link(isaconst("pstep")),
      text(weight: "bold")[Activation traces],
      [#formal-link(isatype("activation_trace")) #formal-link(isaconst("valid_activation_trace"))],

      text(weight: "bold")[The proof contract],
      [#formal-link(isalocale("activation_coverage")) #formal-link(
          isathm("activation_collect_sound"),
        )],

      text(weight: "bold")[A domain obligation],
      [#formal-link(isathm("congruence_mod_sound")) #formal-link(
          isathm("prefix_congruence_mod_unsound"),
        )],

      text(weight: "bold")[The end-to-end theorem], formal-link(isathm("run_voblint_source_sound")),
    )
    #v(20pt)
    #small[Each name opens its definition in the rendered Isabelle theories on the project site.]
  ],
  notes: [
    Switch to the browser and click through. Start with the PDF to show the
    size. Then the source semantics pstep, the activation trace datatype and
    its validity rules, the coverage locale with its five assumptions and
    the soundness theorem, one domain obligation together with the
    counterexample theorem for Goblint's old remainder operator, and finally
    the end-to-end theorem. Keep it to the statements; do not open proofs.
  ],
)

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
  19,
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
  20,
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
  21,
  [What Voblint #b(blue)[supports], all covered by the theorem],
  35,
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
  22,
  [Now: #b(blue)[the playground]],
  110,
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
  23,
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
  24,
  [Outlook: towards #b(blue)[C and Goblint]],
  35,
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
  25,
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
