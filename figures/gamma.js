{
  /*
   * Each value is its concretization: a predicate saying which integers it stands for.
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

  for (const figure of document.querySelectorAll(".scene-gamma")) {
    const presets = figure.querySelector(".gamma-presets");
    const formula = figure.querySelector(".gamma-formula");
    const note = figure.querySelector(".gamma-note");
    const svg = figure.querySelector(".gamma-line");
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

    const draw = (inSet, tail) => {
      for (const { n, circle } of dots) {
        const kind = inSet(n) ? "in" : "out";
        circle.setAttribute("class", `dot-${kind}`);
        circle.setAttribute("r", kind === "out" ? "6" : "9");
      }

      for (const { side, text } of tails) {
        text.style.visibility = tail === side || tail === "both" ? "visible" : "hidden";
      }
    };

    const render = (index) => {
      const preset = GAMMA_PRESETS[index];

      presets.replaceChildren(
        ...GAMMA_PRESETS.map((item, i) => {
          const button = document.createElement("button");
          button.type = "button";
          button.setAttribute("aria-pressed", String(i === index));
          button.innerHTML = `${item.label} <small>${item.kind}</small>`;
          button.addEventListener("click", () => render(i));
          return button;
        }),
      );

      formula.innerHTML = `γ(<span>${preset.label}</span>) <span class="eq">in</span> ${preset.kind}`;
      note.innerHTML = withCode(preset.note ?? "");
      draw(preset.test, preset.tail);
    };

    render(0);
  }
}
