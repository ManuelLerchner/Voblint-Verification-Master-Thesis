{
  /*
   * Transcribed from refine_round = [refine_interval, refine_congruence], iterated by
   * refine_fix, on the state each domain computes alone for x at the two checks.
   */
  const REDUCE_TESTS = {
    "≥ 0": (x) => x >= 0,
    "> 0": (x) => x > 0,
    "[0, 10]": (x) => x >= 0 && x <= 10,
    "[1, 9]": (x) => x >= 1 && x <= 9,
    odd: (x) => mod(x, 2) === 1,
    "1 (mod 4)": (x) => mod(x, 4) === 1,
  };

  const REDUCE_STEPS = [
    {
      sign: "≥ 0",
      interval: "[0, 10]",
      parity: "odd",
      congruence: "1 (mod 4)",
      changed: [],
      proved: false,
      text: "What each domain finds on its own. No component rules out `0` or `10`, so neither check is decided, although together they allow only `1`, `5` and `9`.",
    },
    {
      sign: "≥ 0",
      interval: "[0, 10]",
      parity: "odd",
      congruence: "1 (mod 4)",
      changed: [],
      proved: false,
      text: "`refine_interval` intersects sign and interval. `≥ 0` and `[0, 10]` agree, and `[0, 10]` is not a single value that would fix the parity. Nothing changes.",
    },
    {
      sign: "≥ 0",
      interval: "[1, 9]",
      parity: "odd",
      congruence: "1 (mod 4)",
      changed: ["interval"],
      proved: true,
      text: "`refine_congruence` intersects parity and congruence, which gives `1 (mod 4)`, and moves the interval's bounds onto that residue class: `0` becomes `1` and `10` becomes `9`. Both checks are now decided.",
    },
    {
      sign: "> 0",
      interval: "[1, 9]",
      parity: "odd",
      congruence: "1 (mod 4)",
      changed: ["sign"],
      proved: true,
      text: "The round repeats. `refine_interval` sees `[1, 9]`, which excludes `0`, so the sign sharpens to `> 0`.",
    },
    {
      sign: "> 0",
      interval: "[1, 9]",
      parity: "odd",
      congruence: "1 (mod 4)",
      changed: [],
      proved: true,
      text: "Another round changes nothing, so this is the fixpoint. The set is still `{1, 5, 9}`, with a smaller description.",
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
          classOf: (x) => (REDUCE_TESTS[state[comp]](x) ? (together(x) ? "in" : "extra") : "out"),
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
    });
  }
}
