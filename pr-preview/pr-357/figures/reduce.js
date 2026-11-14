{
  /*
   * Transcribed from it_refine (congruence from interval, then interval rounded to the
   * class), iterated by it_refine_mode, on the state each domain computes alone for x.
   */
  const REDUCE_TESTS = {
    "[-2, 10]": (x) => x >= -2 && x <= 10,
    "[1, 9]": (x) => x >= 1 && x <= 9,
    "1 (mod 4)": (x) => mod(x, 4) === 1,
  };

  /* Two states: the tuple as it arrives, and after the one round it takes to reach the
     fixpoint. A second round changes nothing. */
  const REDUCE_STEPS = [
    {
      interval: "[-2, 10]",
      congruence: "1 (mod 4)",
      changed: [],
      proved: false,
      text: "Two descriptions of the same `x`. The interval still admits `-2` and `10`, so the check is not decided, although the congruence excludes both. Together they already allow only `1`, `5` and `9`. Each is true, and neither is tight.",
    },
    {
      interval: "[1, 9]",
      congruence: "1 (mod 4)",
      changed: ["interval"],
      proved: true,
      text: "One round, and the congruence trims the interval. A bound is only useful if some value of the right residue class sits on it: `-2` is not `1 (mod 4)`, so the lower bound walks up to `1`, and `10` is not either, so the upper walks down to `9`. The dots did not move. The same three integers, described more tightly, and that alone decides the check.",
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
      const together = (x) => ["interval", "congruence"].every((c) => REDUCE_TESTS[state[c]](x));

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
