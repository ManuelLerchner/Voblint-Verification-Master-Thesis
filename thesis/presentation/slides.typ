// The thesis talk. Narrative: why such a tool has to exist, a small example,
// how building an analyzer piles up complexity, the bug that slips through
// anyway, what a machine-checked analyzer changes, and the running tool.
#import "theme.typ": *
#import "../lib/code.typ": isathm
#import "../lib/claims.typ": claim-check

#show: deck

#let pg(name) = "/shared/generated/playground/" + name
#let svg(name) = "/shared/generated/svg/" + name + ".svg"

#let code-card(body, w: 520pt) = block(
  width: w,
  radius: 12pt,
  fill: rgb("#132A33"),
  inset: (x: 26pt, y: 20pt),
  {
    set text(fill: rgb("#E6EEF0"), size: 24pt)
    set par(leading: 0.5em)
    body
  },
)

#let verdict-tag(v) = {
  let c = if v == "PROVED" { green } else if v == "REFUTED" { red } else { amber }
  box(inset: (x: 10pt, y: 5pt), radius: 6pt, fill: c, text(
    fill: white,
    size: 20pt,
    weight: "bold",
    v,
  ))
}

// ======================================================== 1. Why it exists

#page(fill: night, margin: 0pt)[
  #metadata((
    id: 1,
    title: [Voblint],
    seconds: 20,
    notes: [
      Introduce yourself in one sentence. Then go straight to the question
      the talk answers: why should anyone trust what a program analyzer says?
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
  60,
  section: [Why],
  [
    #v(20pt)
    #align(center, image(svg("runs"), width: 1080pt))
  ],
  notes: [
    Start from why such tools exist. Most code is checked by testing. A test
    run that passes tells you about that run. The input nobody tried is never
    checked (left). A static analyzer reads the program and computes one region
    that contains every run, tried or not (right). If that region misses the
    bad states, no run reaches them. That is why people stop looking at a line
    once the analyzer says it is fine. It also means a wrong answer is worse
    than no answer.
  ],
)

#talk-slide(
  3,
  [Machines now check #b(blue)[large proofs]],
  60,
  section: [Why],
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
    The second trend: proof assistants. A proof assistant checks every step
    of a proof against a small trusted kernel. Twenty years ago that meant
    single heroic projects. Today it is routine: the Kepler conjecture, the
    Liquid Tensor Experiment, the fifth Busy Beaver value. On the software
    side, an OS kernel, a C compiler, and since this year AWS's hypervisor.
    And this autumn the scale changed again: AI systems produced Lean proofs
    of a Navier–Stokes blow-up result (OpenAI, September) and of the Riemann
    Hypothesis (released 20 November, certified by the Lean FRO and the
    Mathlib Initiative the next day). Check the status of both the week of
    the talk.
  ],
)

#talk-slide(
  4,
  [The checker checks the proof, #b(red)[not the question]],
  75,
  section: [Why],
  [
    #v(50pt)
    #checked-chain([What we #b(blue)[mean]], [Formal #b(blue)[statement]\ + definitions], [
      Formal #b(blue)[proof]
    ])
    #v(70pt)
    #align(center, text(size: 24pt, fill: rgb("#444"))[
      Riemann (Nov 2026): a separate tool confirms the theorem #emph[is] Mathlib's statement.\
      Navier–Stokes (Oct 2026): "the formalised Lean proof does not correspond to the NL proof".
    ])
  ],
  sources: [Lean FRO and Mathlib Initiative, 21 Nov 2026 · Bastounis, Circelli, Hansen, arXiv 2610.08144],
  notes: [
    What does a machine check actually give you? The kernel checks that the
    proof proves the formal statement. It cannot check that the statement and
    its definitions say what we mean. That step stays with humans. The Riemann
    certification therefore ran a separate statement check. For the Navier–Stokes
    result, a group argues that the Lean proof does not correspond to the
    published argument. Keep this picture in mind; it comes back when we look
    at what Voblint trusts.
  ],
)

// ===================================================== 2. A small example

#talk-slide(
  5,
  [A question about #b(blue)[every run]],
  60,
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
    Here is the example for the rest of the talk. bump adds one. main calls it
    twice and asks two questions. If you run it, both checks hold. An analyzer
    must answer without running the program, for every input, so it computes
    with abstract values: descriptions of sets of numbers. A sign says
    "positive", an interval says "between 5 and 6", parity says "even or odd".
    Every abstract value must contain every value a run can produce. It may
    contain more. That is the deal: precision may be lost, a real value never.
  ],
)

#talk-slide(
  6,
  [How hard could it be? Merging calls #b(red)[loses] precision],
  70,
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
    The descent starts. The simple analyzer keeps one state per procedure. bump
    is called with 5 and with 4, so it sees n in an interval up to 5, returns
    up to 6, and both checks come back UNKNOWN (left). The fix: analyze bump
    separately per calling context, here per entry value. Now a is exactly 6
    and b exactly 5, and both checks are PROVED (right). Real analyzers such
    as Goblint, a static analyzer for C developed at TUM, do this.
  ],
)

#talk-slide(
  7,
  [More precision, more machinery: #b(red)[infinitely many] contexts],
  45,
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
        #v(24pt)
        #small[Contexts, widening, globals, a demand-driven solver: each piece is another place for a bug.]
      ],
    )
  ],
  notes: [
    Contexts bring their own trouble. With recursion there can be infinitely
    many of them, so the equations have infinitely many unknowns. The solver
    only touches the ones it needs. Add widening for loops, shared globals,
    and the solver itself, and you have the kind of machinery real analyzers
    are built from. Every one of those pieces can be wrong.
  ],
)

#talk-slide(
  8,
  [We added all the machinery. Is it correct now? #b(red)[No.]],
  60,
  section: [Example],
  [
    #v(10pt)
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 40pt,
      align: horizon,
      code-card(raw(
        "c = -5;   // or c = -7\n__voblint_check(c % 2 == 1);",
        lang: none,
      )),
      [
        #grid(
          columns: (auto, 1fr),
          column-gutter: 20pt,
          row-gutter: 30pt,
          align: (right + horizon, left + horizon),
          text(size: 26pt, weight: "bold")[C11],
          [#text(
              size: 40pt,
              weight: "bold",
              fill: green,
            )[−5 % 2 = −1]\ #small[remainder truncates toward zero]],

          text(size: 26pt, weight: "bold")[Goblint],
          [#text(
              size: 40pt,
              weight: "bold",
              fill: red,
            )[always 1]\ #small[congruence domain ignored the sign]],
        )
      ],
    )
    #v(40pt)
    #align(center, text(
      size: 28pt,
    )[A #b(red)[confident wrong answer] in a mature analyzer, fixed after a user report.])
  ],
  sources: [Goblint issue 1156, fixed by pull request 1161],
  notes: [
    So we have all the machinery. Are we done? Here is a real bug from
    Goblint. In C, the remainder truncates toward zero, so minus five modulo
    two is minus one. Goblint's congruence domain ignored the sign of the
    dividend and claimed the remainder is always one. A user found it, and
    pull request 1161 fixed it. Fixing one bug does not rule out the next.
  ],
)

// =============================================== 3. What a proof changes

#let c-congr = claim-check("goblint-1161-congruence", "c % 2 == 1")
#let i-one = claim-check("goblint-1161-int", "c % 2 == 1")
#let i-neg = claim-check("goblint-1161-int", "c % 2 == -1")

#talk-slide(
  9,
  [The same bug, #b(blue)[with a proof obligation]],
  75,
  section: [Proof],
  [
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 50pt,
      [
        #text(size: 30pt, weight: "bold")[Unverified analyzer]
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
    This is the comparison that matters. In an unverified analyzer the
    operator is code; nothing forces it to agree with C. In Voblint every
    abstract remainder carries an obligation: whatever the concrete values,
    their real remainder must lie in the abstract result. Goblint's pre-fix
    answer cannot meet it. Isabelle proves the opposite, with minus five as
    the witness. The bug could not have been proved sound, so it could not
    ship. On the same program, the sound congruence domain says UNKNOWN, and
    the combined Int domain refutes the wrong check and proves the right one.
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
  10,
  [Soundness is a chain of #b(blue)[set inclusions]],
  90,
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
    How do we prove it for the whole analyzer, not just one operator? We follow
    one program point and the states real runs have there (the dots).
    Step one: the source program compiles to a graph, and every source run is
    a run on the graph. Step two: the runs on the graph are grouped by calling
    context. Step three: the solver's answer contains each group. Each step is
    its own theorem. Each may add states, which costs precision. None may drop
    a state. Chained together: everything a real run can do is in the answer.
  ],
)

#talk-slide(
  11,
  [What you see, and what #b(blue)[holds it up]],
  60,
  section: [Proof],
  [
    #grid(
      columns: (440pt, 1fr),
      column-gutter: 30pt,
      align: horizon,
      [
        #text(size: 24pt, weight: "bold")[Above the line: the verdicts]
        #v(6pt)
        #crop(pg("clamp.png"), 1328, 1090, 0, 0, 1328, 1090, width: 420pt)
      ],
      [
        #text(size: 24pt, weight: "bold")[Below the line: one theorem per link]
        #v(6pt)
        #image(svg("metro"), width: 100%)
      ],
    )
  ],
  notes: [
    A user sees verdicts: PROVED, REFUTED, DEAD, a warning (left). Below the line
    is the proof that makes those words mean something: each line on the right
    is one component, semantics, compiler, domains, framework, solver, and each
    interchange is a place where one theorem uses another. PROVED means the
    check holds whenever a run reaches the point. It does not say the point is
    reachable. DEAD says it is not.
  ],
)

#talk-slide(
  12,
  [What is #b(amber)[trusted], not proved],
  70,
  section: [Proof],
  [
    #v(10pt)
    #checked-chain(
      [C-like programs\ #text(size: 20pt, weight: "regular")[what we mean]],
      [VIMP semantics\ #text(size: 20pt, weight: "regular")[the definition]],
      [Soundness\ theorem],
    )
    #v(20pt)
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 30pt,
      align: horizon,
      image(svg("island"), width: 100%),
      [
        #text(
          size: 26pt,
        )[#b(amber)[Trusted:] parser, code generation, OCaml and the browser runtime.]
        #v(16pt)
        #text(
          size: 26pt,
        )[#b(blue)[Scope:] unbounded integers, no pointers, heap or threads. Partial correctness.]
      ],
    )
  ],
  notes: [
    Back to the picture from the start. Isabelle checks the proof against the
    VIMP semantics. Whether VIMP models the programs we care about is an
    argument, not a theorem. VIMP is a fragment of C (left): integers,
    globals, recursive procedures; no pointers, heap or threads, and integers
    do not overflow. The parser and the generated-code toolchain sit outside
    the proof. The guarantee is partial correctness: it covers every run when
    the solver finishes.
  ],
)

// ================================================================ 4. Demo

#talk-slide(
  13,
  [The proved analyzer #b(blue)[runs in your browser]],
  150,
  section: [Demo],
  [
    #align(center, image(svg("build"), width: 1100pt))
    #v(10pt)
    #align(center, text(
      size: 26pt,
    )[Isabelle generates the analyzer's code from #b(blue)[the same definition] the theorem is about.])
  ],
  notes: [
    Live demo, about two minutes. Open the playground. Run the bump example
    with contexts off: both checks UNKNOWN. Switch to entry-state contexts: both
    PROVED, and the graph gets a box per context. Then open the overview
    example: PROVED, REFUTED and DEAD checks, an arithmetic warning. The code
    running here is generated by Isabelle from the function the theorem is
    about, compiled to WebAssembly. If the network fails, show this slide.
  ],
)

#talk-slide(
  14,
  [Watching the solver work],
  50,
  section: [Demo],
  [
    #align(center, crop(pg("solve-replay-still.png"), 2088, 1472, 0, 0, 2088, 1472, height: 500pt))
  ],
  notes: [
    The playground can replay the solve step by step: which unknown is being
    evaluated, which call is being entered, and when a callee's entry state is
    published. Here the first call into a context reads its callee's seed.
    This is how we debugged the analyzer during development.
  ],
)

#talk-slide(
  15,
  [Combining domains #b(blue)[proves more]],
  45,
  section: [Demo],
  [
    #align(center, image(pg("int-refinement.png"), height: 500pt))
  ],
  notes: [
    One precision example, not a general claim. y + 1 == 3 tells us y is 2.
    Sign, interval and parity alone each answer UNKNOWN at the check. The
    reduced product Int combines them and proves y == 2.
  ],
)

// =========================================================== 5. Wrap-up

#talk-slide(
  16,
  [What it took],
  50,
  section: [Wrap-up],
  [
    #grid(
      columns: (1fr, 380pt),
      column-gutter: 30pt,
      align: horizon,
      image(svg("strata"), width: 100%),
      [
        #text(size: 28pt)[One layer per Isabelle session, sized by its proof.]
        #v(24pt)
        #text(size: 28pt)[Built with #b(blue)[heavy AI assistance].]
        #v(12pt)
        #small[The same question as slide 4 applies: definitions and theorem statements were reviewed by hand.]
      ],
    )
  ],
  notes: [
    The formalization in cross-section: each layer is an Isabelle session,
    sized by its proof. AI tools wrote much of the proof text, which is the
    same trend as the 2026 results from the start. And the same caution
    applies: a checked proof of the wrong statement is worthless, so the
    definitions and the theorem statements were reviewed by hand.
  ],
)

#statement-slide(
  17,
  40,
  [So what is Voblint?],
  [
    A static analyzer whose #b(blue)[every answer] is backed by a
    #b(green)[machine-checked proof], from the #b(blue)[source program] to
    the #b(blue)[verdict], with its #b(amber)[trusted parts] named.
  ],
  notes: [
    Summary in one sentence. Then take questions. Leave this slide up.
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
    If asked about the contribution: the solver and the side-effecting
    equations come from prior work, the D/G architecture from Goblint. This
    thesis connects them to source executions through context-indexed
    semantics, and ships the result as an executable analyzer.
  ],
)
