{
  /*
   * Transcribed from refine_round = [refine_interval, refine_congruence], iterated by
   * refine_fix, on the state each domain computes alone for x at the two checks.
   */
  const REDUCE_TESTS = {
    "⊤": () => true,
    "> 0": (x) => x > 0,
    "[-2, 10]": (x) => x >= -2 && x <= 10,
    "[1, 9]": (x) => x >= 1 && x <= 9,
    odd: (x) => mod(x, 2) === 1,
    "1 (mod 4)": (x) => mod(x, 4) === 1,
  };

  /* Three states, not five: the tuple as it arrives, and each of the two rounds it takes
     to reach the fixpoint. A third round changes nothing for any starting tuple. */
  const REDUCE_STEPS = [
    {
      sign: "⊤",
      interval: "[-2, 10]",
      parity: "odd",
      congruence: "1 (mod 4)",
      changed: [],
      proved: false,
      text: "Four descriptions of the same `x`, and one of them is `⊤`: the guards left `x` straddling zero, so sign knows nothing at all. The other three are true and too loose, and none rules out `-2` or `10`, so the check is not decided. Together they already allow only `1`, `5` and `9`. Each is true, and none is tight.",
    },
    {
      sign: "⊤",
      interval: "[1, 9]",
      parity: "odd",
      congruence: "1 (mod 4)",
      changed: ["interval"],
      proved: true,
      text: "Round one, and the congruence trims the interval. A bound is only useful if some value of the right residue class sits on it: `-2` is not `1 (mod 4)`, so the lower bound walks up to `1`, and `10` is not either, so the upper walks down to `9`. The dots did not move. The same three integers, described more tightly, and that alone decides the check.",
    },
    {
      sign: "> 0",
      interval: "[1, 9]",
      parity: "odd",
      congruence: "1 (mod 4)",
      changed: ["sign"],
      proved: true,
      text: "Round two, and the trimmed interval sharpens the sign, which is where the component that knew nothing gets something: `[1, 9]` lies entirely above zero, so `⊤` becomes `> 0`. The traffic went congruence to interval to sign, one hop per round. Nothing can move after this, and a third round changes nothing.",
    },
  ];

  for (const figure of document.querySelectorAll(".scene-reduce")) {
    const rows = [...figure.querySelectorAll(".reduce-row")];
    const caption = figure.querySelector(".reduce-caption");
    const checks = figure.querySelectorAll(".reduce-checks li");
    const line = { low: -2, high: 12, x0: 12, dx: 21.8, y: 12 };

    const axis = figure.querySelector(".reduce-axis svg");

    for (const n of [0, 4, 8, 12]) {
      const label = document.createElementNS(SVG_NS, "text");
      label.setAttribute("x", String(line.x0 + (n - line.low) * line.dx));
      label.setAttribute("y", "16");
      label.textContent = String(n);
      axis.append(label);
    }

    const render = (i) => {
      const state = REDUCE_STEPS[i];
      const together = (x) =>
        ["sign", "interval", "parity", "congruence"].every((c) => REDUCE_TESTS[state[c]](x));

      for (const row of rows) {
        const comp = row.dataset.comp;
        const svg = row.querySelector("svg");

        if (comp === "together") {
          drawDots(svg, { ...line, classOf: (x) => (together(x) ? "in" : "out") });
          continue;
        }

        row.querySelector(".reduce-val").textContent = state[comp];
        row.classList.toggle("changed", state.changed.includes(comp));
        drawDots(svg, {
          ...line,
          classOf: (x) => (REDUCE_TESTS[state[comp]](x) ? "in" : "out"),
        });
      }

      caption.innerHTML = withCode(state.text);

      for (const check of checks) {
        const verdict = check.querySelector(".verdict");
        verdict.textContent = state.proved ? "PROVED" : "UNKNOWN";
        verdict.className = `verdict ${state.proved ? "proved" : "unknown"}`;
      }
    };

    makeStepper(figure, {
      count: REDUCE_STEPS.length,
      render,
      controls: figure.querySelector(".reduce-controls"),
      chipsBox: figure.querySelector(".reduce-steps"),
      interval: 4600,
      autoplay: false,
    });
  }
}
