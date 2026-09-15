{
  /*
   * Each value is its concretization as a predicate on integers. Joins list both sides
   * and the join Voblint computes, so the drawing can show which integers the join adds.
   * The results follow the domains' own join definitions.
   */

  const GAMMA_PRESETS = [
    { label: "[−2, 5]", kind: "interval", test: (x) => x >= -2 && x <= 5 },
    {
      label: "[3, +∞]",
      kind: "interval",
      test: (x) => x >= 3,
      tail: "right",
      note: "The set continues past 12 forever.",
    },
    { label: "≥ 0", kind: "sign", test: (x) => x >= 0, tail: "right" },
    { label: "< 0", kind: "sign", test: (x) => x < 0, tail: "left" },
    { label: "even", kind: "parity", test: (x) => mod(x, 2) === 0, tail: "both" },
    { label: "1 (mod 3)", kind: "congruence", test: (x) => mod(x, 3) === 1, tail: "both" },
    {
      label: "4 (mod 0)",
      kind: "congruence",
      test: (x) => x === 4,
      note: "Modulus 0 pins the value: exactly 4.",
    },
    {
      label: "≥0 · [0,9] · odd · 1 (mod 3)",
      kind: "Int product",
      test: (x) => x >= 0 && x <= 9 && mod(x, 2) === 1 && mod(x, 3) === 1,
      note: "A product stands for the integers every component allows: here only `1` and `7`.",
    },
    {
      label: "⊤",
      kind: "any domain",
      test: () => true,
      tail: "both",
      note: "Top: nothing is known.",
    },
    {
      label: "⊥",
      kind: "any domain",
      test: () => false,
      note: "Bottom: no value at all. The analysis uses it for unreachable points.",
    },
  ];

  const JOIN_PRESETS = [
    {
      kind: "interval",
      a: "[−3, −1]",
      b: "[4, 6]",
      join: "[−3, 6]",
      left: (x) => x >= -3 && x <= -1,
      right: (x) => x >= 4 && x <= 6,
      test: (x) => x >= -3 && x <= 6,
      note: "An interval has no holes, so the join takes in `0` to `3` as well.",
    },
    {
      kind: "interval",
      a: "[2, 2]",
      b: "[8, 8]",
      join: "[2, 8]",
      left: (x) => x === 2,
      right: (x) => x === 8,
      test: (x) => x >= 2 && x <= 8,
      note: "Two exact values become five extra candidates: the merged context you will meet with procedures.",
    },
    {
      kind: "sign",
      a: "< 0",
      b: "0",
      join: "≤ 0",
      left: (x) => x < 0,
      right: (x) => x === 0,
      test: (x) => x <= 0,
      tail: "left",
      note: "This join is exact: `≤ 0` is precisely the two sets together.",
    },
    {
      kind: "sign",
      a: "< 0",
      b: "> 0",
      join: "⊤",
      left: (x) => x < 0,
      right: (x) => x > 0,
      test: () => true,
      tail: "both",
      note: "Sign has no value for “not zero”, so the join must admit `0`.",
    },
    {
      kind: "parity",
      a: "even",
      b: "odd",
      join: "⊤",
      left: (x) => mod(x, 2) === 0,
      right: (x) => mod(x, 2) === 1,
      test: () => true,
      tail: "both",
      note: "Exact, but useless: even and odd together are every integer.",
    },
    {
      kind: "congruence",
      a: "1 (mod 6)",
      b: "4 (mod 6)",
      join: "1 (mod 3)",
      left: (x) => mod(x, 6) === 1,
      right: (x) => mod(x, 6) === 4,
      test: (x) => mod(x, 3) === 1,
      tail: "both",
      note: "`gcd(6, 6, 1 − 4) = 3`, and the join is exact.",
    },
    {
      kind: "congruence",
      a: "1 (mod 3)",
      b: "2 (mod 3)",
      join: "⊤",
      left: (x) => mod(x, 3) === 1,
      right: (x) => mod(x, 3) === 2,
      test: () => true,
      tail: "both",
      note: "`gcd(3, 3, 1 − 2) = 1`: modulo 1 everything agrees, so the multiples of 3 come in too.",
    },
  ];

  for (const figure of document.querySelectorAll(".scene-gamma")) {
    const presets = figure.querySelector(".gamma-presets");
    const formula = figure.querySelector(".gamma-formula");
    const note = figure.querySelector(".gamma-note");
    const svg = figure.querySelector(".gamma-line");
    const modes = figure.querySelectorAll(".gamma-modes [data-mode]");
    const low = -12;
    const high = 12;
    const xOf = (n) => 40 + ((n - low) * 820) / (high - low);

    const axis = document.createElementNS(SVG_NS, "line");
    axis.setAttribute("class", "axis");
    axis.setAttribute("x1", "20");
    axis.setAttribute("x2", "880");
    axis.setAttribute("y1", "50");
    axis.setAttribute("y2", "50");
    svg.append(axis);

    const dots = [];

    for (let n = low; n <= high; n++) {
      const circle = document.createElementNS(SVG_NS, "circle");
      circle.setAttribute("cx", String(xOf(n)));
      circle.setAttribute("cy", "50");
      circle.setAttribute("r", "9");
      svg.append(circle);

      if (n % 2 === 0) {
        const label = document.createElementNS(SVG_NS, "text");
        label.setAttribute("x", String(xOf(n)));
        label.setAttribute("y", "86");
        label.textContent = String(n);
        svg.append(label);
      }

      dots.push({ n, circle });
    }

    const tails = ["left", "right"].map((side) => {
      const text = document.createElementNS(SVG_NS, "text");
      text.setAttribute("class", "tail");
      text.setAttribute("x", side === "left" ? "14" : "886");
      text.setAttribute("y", "56");
      text.textContent = "…";
      svg.append(text);
      return { side, text };
    });

    const draw = (inSet, extra, tail) => {
      for (const { n, circle } of dots) {
        const kind = inSet(n) ? "in" : extra(n) ? "extra" : "out";
        circle.setAttribute("class", `dot-${kind}`);
        circle.setAttribute("r", kind === "out" ? "6" : "9");
      }

      for (const { side, text } of tails) {
        text.style.visibility = tail === side || tail === "both" ? "visible" : "hidden";
      }
    };

    const showGamma = (preset) => {
      formula.innerHTML = `γ(<span>${preset.label}</span>) <span class="eq">in</span> ${preset.kind}`;
      note.innerHTML = withCode(preset.note ?? "");
      draw(preset.test, () => false, preset.tail);
    };

    const showJoin = (preset) => {
      formula.innerHTML = `${preset.a} ⊔ ${preset.b} <span class="eq">=</span> ${preset.join}`;
      note.innerHTML = withCode(preset.note);
      draw(
        (n) => preset.left(n) || preset.right(n),
        (n) => preset.test(n),
        preset.tail,
      );
    };

    const render = (mode, index) => {
      const list = mode === "join" ? JOIN_PRESETS : GAMMA_PRESETS;
      const chosen = Math.min(index, list.length - 1);

      figure.dataset.mode = mode;

      for (const button of modes) {
        button.setAttribute("aria-selected", String(button.dataset.mode === mode));
      }

      presets.replaceChildren(
        ...list.map((preset, i) => {
          const button = document.createElement("button");
          button.type = "button";
          button.setAttribute("aria-pressed", String(i === chosen));
          button.innerHTML =
            mode === "join"
              ? `${preset.a} ⊔ ${preset.b} <small>${preset.kind}</small>`
              : `${preset.label} <small>${preset.kind}</small>`;
          button.addEventListener("click", () => render(mode, i));
          return button;
        }),
      );

      (mode === "join" ? showJoin : showGamma)(list[chosen]);
    };

    for (const button of modes) {
      button.addEventListener("click", () => render(button.dataset.mode, 0));
    }

    render("gamma", 0);
  }
}
