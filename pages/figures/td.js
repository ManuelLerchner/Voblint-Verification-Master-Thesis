{
  /*
   * One entry per solver event, transcribed from query/iterate in the vendored solver
   * for the counting loop. "c" is the set of unknowns being computed, in call order.
   */
  const TD_STEPS = [
    {
      eq: "X",
      c: ["X"],
      stable: ["X"],
      point: [],
      sigma: { E: "⊥", H: "⊥", B: "⊥", X: "⊥" },
      text: "Solve `X`. `X` goes onto the set of unknowns being computed, and its equation needs `H`.",
    },
    {
      eq: "H",
      c: ["X", "H"],
      stable: ["X", "H"],
      point: [],
      sigma: { E: "⊥", H: "⊥", B: "⊥", X: "⊥" },
      text: "`H` is not being computed yet, so the solver starts computing it. `H` needs `E`, then `B`.",
    },
    {
      eq: "E",
      c: ["X", "H"],
      stable: ["X", "H", "E"],
      point: [],
      sigma: { E: "⊤", H: "⊥", B: "⊥", X: "⊥" },
      text: "`E` depends on nothing: it is `⊤`, any store, and immediately stable.",
    },
    {
      eq: "B",
      c: ["X", "H", "B"],
      stable: ["X", "H", "E", "B"],
      point: ["H"],
      sigma: { E: "⊤", H: "⊥", B: "⊥", X: "⊥" },
      text: "`B` needs `H`, but `H` is still being computed: a cycle. The solver answers with `H`'s current value, `⊥`, and marks `H` as a loop point.",
    },
    {
      eq: "B",
      c: ["X", "H"],
      stable: ["X", "H", "E", "B"],
      point: ["H"],
      sigma: { E: "⊤", H: "⊥", B: "⊥", X: "⊥" },
      text: "`B` evaluates to `⊥`, which is already its value, so `B` is done for now.",
    },
    {
      eq: "H",
      c: ["X", "H"],
      stable: ["X", "E"],
      point: ["H"],
      sigma: { E: "⊤", H: "[0,0]", B: "⊥", X: "⊥" },
      text: "`H` evaluates to `[0,0]`. This round started before `H` was known to be a loop point, so it updates without widening. `H` changed, so `B`, which read `H`, is no longer stable.",
    },
    {
      eq: "B",
      c: ["X", "H"],
      stable: ["X", "E", "H", "B"],
      point: ["H"],
      sigma: { E: "⊤", H: "[0,0]", B: "[0,0]", X: "⊥" },
      text: "`H` is evaluated again. `B` is recomputed from the new `H`: `[0,0]`.",
    },
    {
      eq: "H",
      c: ["X", "H"],
      stable: ["X", "E"],
      point: ["H"],
      sigma: { E: "⊤", H: "[0,+∞]", B: "[0,0]", X: "⊥" },
      text: "`H`'s equation now gives `[0,1]`. `H` is a loop point and its value grew, so warrowing widens: `[0,+∞]`.",
    },
    {
      eq: "B",
      c: ["X", "H"],
      stable: ["X", "E", "H", "B"],
      point: ["H"],
      sigma: { E: "⊤", H: "[0,+∞]", B: "[0,4]", X: "⊥" },
      text: "`B` recomputes: `assume(i < 5)` on `[0,+∞]` gives `[0,4]`.",
    },
    {
      eq: "H",
      c: ["X", "H"],
      stable: ["X", "E"],
      point: ["H"],
      sigma: { E: "⊤", H: "[0,5]", B: "[0,4]", X: "⊥" },
      text: "`H`'s equation gives `[0,5]`, below the widened value, so warrowing narrows: `[0,5]`.",
    },
    {
      eq: "H",
      c: ["X"],
      stable: ["X", "E", "H", "B"],
      point: [],
      sigma: { E: "⊤", H: "[0,5]", B: "[0,4]", X: "⊥" },
      text: "One more round changes nothing. `H` is stable, stops being computed, and is no longer a loop point.",
    },
    {
      eq: "X",
      c: [],
      stable: ["X", "E", "H", "B"],
      point: [],
      sigma: { E: "⊤", H: "[0,5]", B: "[0,4]", X: "[5,5]" },
      text: "Back in `X`: `assume(i ≥ 5)` on `[0,5]` gives `[5,5]`. Everything is stable, and the check `i == 5` holds.",
    },
  ];

  for (const figure of document.querySelectorAll(".scene-td")) {
    const caption = figure.querySelector(".td-caption");
    const equations = figure.querySelectorAll(".td-eq");
    const rows = figure.querySelectorAll(".td-sigma tr");
    const sets = figure.querySelectorAll(".td-chips");
    const chipsBox = figure.querySelector(".td-steps");
    const toggle = figure.querySelector(".loop-play");
    const icon = toggle.querySelector("i");
    let step = 0;
    let previous = null;
    let timer = null;

    const chips = TD_STEPS.map((_, i) => {
      const chip = document.createElement("button");
      chip.type = "button";
      chip.textContent = String(i + 1);
      chip.addEventListener("click", () => {
        setPlaying(false);
        show(i);
      });
      chipsBox.append(chip);
      return chip;
    });

    const show = (next) => {
      step = (next + TD_STEPS.length) % TD_STEPS.length;
      const state = TD_STEPS[step];
      figure.dataset.step = String(step);
      caption.innerHTML = withCode(state.text);

      for (const node of figure.querySelectorAll(".td-node")) {
        node.classList.toggle("is-current", node.dataset.var === state.eq);
        node.querySelector("[data-val]").textContent = state.sigma[node.dataset.var];
      }

      for (const eq of equations) {
        eq.classList.toggle("is-current", eq.dataset.var === state.eq);
      }

      for (const row of rows) {
        const name = row.dataset.var;
        const cell = row.querySelector("td");
        const changed = previous !== null && previous.sigma[name] !== state.sigma[name];
        cell.textContent = state.sigma[name];
        row.classList.remove("changed");

        if (changed) {
          void row.offsetWidth;
          row.classList.add("changed");
        }
      }

      for (const box of sets) {
        const members = state[box.dataset.set];
        box.replaceChildren(
          ...(members.length
            ? members.map((name) =>
                Object.assign(document.createElement("span"), { textContent: name }),
              )
            : [
                Object.assign(document.createElement("span"), {
                  className: "empty",
                  textContent: "empty",
                }),
              ]),
        );
      }

      chips.forEach((chip, i) => {
        chip.setAttribute("aria-pressed", String(i === step));
      });
      previous = state;
    };

    const setPlaying = (playing) => {
      clearInterval(timer);
      timer = playing
        ? setInterval(() => {
            if (!figure.classList.contains("is-offscreen")) {
              show(step + 1);
            }
          }, 3200)
        : null;
      icon.className = playing ? "fa-solid fa-pause" : "fa-solid fa-play";
      toggle.setAttribute("aria-label", playing ? "Pause" : "Play");
    };

    toggle.addEventListener("click", () => setPlaying(timer === null));
    figure.querySelector(".td-controls").hidden = false;
    show(0);
    setPlaying(!reducedMotion);
  }
}
