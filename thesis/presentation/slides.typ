// The thesis talk. It opens like the thesis introduction (wrong answers,
// machine-checked proofs, Goblint's architecture), works through one example
// into the formal argument, demonstrates the playground live, and closes like
// the thesis conclusion (relevance to Goblint, limits, outlook).
#import "theme.typ": *
#import "../lib/code.typ": (
  decode-isabelle, isabelle-scripts, isabelle-syntax, isaconst, isalocale, isathm, isatype, site,
)
#import "../lib/claims.typ": claim-check
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
  #align(center + horizon)[
    #image("assets/voblint.png", height: 220pt)
    #v(8pt)
    #text(size: 72pt, weight: "bold")[Voblint]
    #v(-12pt)
    #text(size: 30pt)[Verifying a context-sensitive abstract interpreter]
    #v(30pt)
    #text(size: 22pt, fill: grey)[
      Manuel Lerchner · Master's thesis · Technical University of Munich\
      Supervisors: Alexandra Graß and Helmut Seidl
    ]
  ]
]

#talk-slide(
  2,
  [Tests check #b(amber)[some] runs. An analysis covers #b(blue)[all] of them.],
  40,
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
  [But analyzers are programs, and they give #b(red)[confident wrong answers]],
  50,
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
  4,
  [Fixing one bug does not rule out the next: #b(blue)[proofs, checked by machines]],
  45,
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
  5,
  [The checker checks the proof, #b(red)[not the definitions]],
  55,
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
  6,
  [Goblint's architecture lets the proof #b(blue)[split along its modules]],
  55,
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
  7,
  [What the user sees: #b(blue)[four verdicts]],
  45,
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
  sources: [Playground run of the regression test 48-clamp_every_answer (thesis Fig. 1.2)],
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
  8,
  [Our language: VIMP, #b(blue)[a small C]],
  50,
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
  9,
  [A question about #b(blue)[every run]],
  45,
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
  10,
  [Merging calls #b(red)[loses] precision; contexts keep them apart],
  50,
  section: [Example],
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      align(center)[
        #text(size: 30pt, weight: "bold")[One state per procedure]\
        #small[both calls of bump merged]
        #v(10pt)
        #crop(pg("contexts.png"), 1734, 1286, 28, 82, 806, 548, width: 540pt)
      ],
      align(center)[
        #text(size: 30pt, weight: "bold", fill: blue)[One state per calling context]\
        #small[a copy of bump per entry state]
        #v(10pt)
        #crop(pg("contexts.png"), 1734, 1286, 28, 710, 794, 548, width: 540pt)
      ],
    )
  ],
  notes: [
    With one state per procedure, bump sees n up to 5 and returns up to 6,
    and both checks come back UNKNOWN (left). Analyzing bump once per calling
    context, here per entry value, gives a = 6 and b = 5 exactly: both
    PROVED (right). Goblint does this. The price is the proof: what does "the
    states of bump in context n = 5" mean for real runs?
  ],
)

#talk-slide(
  11,
  [#b(red)[Infinitely many] contexts, created while solving],
  30,
  section: [Example],
  [
    #v(10pt)
    #grid(
      columns: (1fr, 380pt),
      column-gutter: 30pt,
      align: horizon,
      align(center, image(svg("infinite"), height: 470pt)),
      [
        #text(size: 28pt)[A recursive call can create a #b(blue)[new context] every time.]
        #v(24pt)
        #text(size: 28pt)[The solver explores only the #b(blue)[finitely many] it reaches.]
      ],
    )
  ],
  notes: [
    With recursion there can be infinitely many contexts, so the equation
    system has infinitely many unknowns, and a callee's contexts become known
    only during solving. The solver touches only the ones it needs.
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

#talk-slide(
  12,
  [The trace semantics: #b(blue)[one trace per activation]],
  75,
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
  13,
  [Valid traces: #b(blue)[four rules]],
  50,
  section: [Proof],
  [
    #set text(size: 27pt)
    #let rule(name, premises, conclusion) = block(
      width: 100%,
      inset: (x: 18pt, y: 12pt),
      radius: 10pt,
      fill: white,
      stroke: 1.5pt + pale,
      below: 12pt,
      grid(
        columns: (170pt, 1fr),
        align: (left + horizon, center + horizon),
        text(weight: "bold", fill: blue, name), $ (#premises) / (#conclusion) $,
      ),
    )
    #rule([Root], $s in S$, $"Root"([(v_0, s)]) in cal(T)$)
    #rule(
      [Local step],
      $t in cal(T) quad ("sink"(t), a, v) in "intra"(g) quad s' in [|a|]("store"(t))$,
      $"extend"(t, (v, s')) in cal(T)$,
    )
    #rule(
      [Call],
      $t in cal(T) quad e = ("sink"(t), a, "entry" p, k) in "calls"(g)$,
      $"Call"(t, [("entry" p, "enter"_e ("store"(t)))]) in cal(T)$,
    )
    #rule(
      [Return],
      $t' in cal(T) quad "caller"(t') = "Some"(t) quad "sink"(t') = "result" p quad e = ("sink"(t), a, "entry" p, k) in "calls"(g)$,
      $"Resume"(t, t', "path"(t) dot [(k, "combine"_e ("store"(t), "store"(t')))]) in cal(T)$,
    )
  ],
  sources: [#isaconst("valid_activation_trace"); shortened: sink, store, caller, enter, combine for sink_node, sink_store, caller_of, call_enter, combine_collect],
  notes: [
    Formally, the valid traces are an inductive set with one rule per kind of
    step. A root starts from an initial store at the graph entry. A local
    step follows an edge of the control-flow graph. A call starts a new trace
    at the callee's entry and keeps the caller. A return resumes exactly the
    caller that created the callee, at the continuation of the call edge, and
    combines the caller's saved store with the callee's result. No frame
    stack is needed: the Call term remembers its caller.
  ],
)

#talk-slide(
  14,
  [The proof contract: #b(blue)[five local obligations]],
  70,
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
  15,
  [Soundness is a chain of #b(blue)[set inclusions]],
  50,
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
  16,
  [The end-to-end theorem, #b(green)[as Isabelle states it]],
  55,
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

#talk-slide(
  17,
  [The remainder bug, #b(blue)[against a proof obligation]],
  50,
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
  18,
  [The parts of the #b(blue)[formalization]],
  40,
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

// ================================================================== Demo

#talk-slide(
  19,
  [Live: the proved analyzer #b(blue)[in the browser]],
  120,
  section: [Demo],
  [
    #align(center, image(svg("build"), width: 1100pt))
    #v(10pt)
    #align(center, text(size: 28pt)[
      #link(site("playground.html"))[#b(
        blue,
      )[manuellerchner.github.io/Voblint-Verification-Master-Thesis/playground.html]]
    ])
  ],
  notes: [
    Switch to the browser. 1. Open the bump example, intervals, context none:
    two UNKNOWN. 2. Switch context to entry-state: two PROVED, and the graph
    shows one box per context. 3. Enable solver tracing and step through the
    replay: watch the first call into a context read its callee's seed. 4. If
    time: the clamp example with all four verdicts, or change the remainder
    program from slide 17 and switch between congruence and int. The code
    running here is generated by Isabelle from run_voblint and compiled to
    WebAssembly (the diagram). Fallback if the network fails: the backup
    slides with the replay and the precision example.
  ],
)

// ============================================================ Conclusion

#let alignment = json("/shared/generated/goblint-alignment.json").rows
#let count(status) = alignment.filter(r => r.status == status).len()

#talk-slide(
  20,
  [Relevance to Goblint, and #b(amber)[limits]],
  55,
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
  21,
  [Outlook: towards #b(blue)[C and Goblint]],
  55,
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
  22,
  30,
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
  section: [Backup],
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
  section: [Backup],
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
  section: [Backup],
  [
    #align(center, image(pg("int-refinement.png"), height: 500pt))
  ],
  notes: [
    Demo fallback, one precision example. y + 1 == 3 implies y is 2. Sign,
    interval and parity alone answer UNKNOWN; the reduced product Int proves
    y == 2.
  ],
)
