{
  /*
   * The procedure walk. The markup ships every equation shown and no step
   * highlighted, so without script the figure is the finished system; with it,
   * the walk builds one equation at a time and seals the callee until the call.
   */
  for (const figure of document.querySelectorAll(".scene-walk")) {
    const steps = Number(figure.dataset.steps);
    const callStep = Number(figure.dataset.callStep);
    const chips = figure.querySelectorAll("[data-goto]");
    const toggle = figure.querySelector(".loop-play");
    const icon = toggle.querySelector("i");
    const eqs = figure.querySelectorAll(".walk-eq");
    const notes = figure.querySelectorAll(".walk-note");
    const nodes = figure.querySelectorAll(".walk-node");
    const lines = figure.querySelectorAll(".walk-code .wl");
    let step = 0;
    let timer = null;

    const show = (next) => {
      step = (next + steps) % steps;
      figure.dataset.step = String(step);
      figure.classList.toggle("is-call", step === callStep);

      for (const [i, eq] of eqs.entries()) {
        eq.classList.toggle("is-shown", i <= step);
        eq.classList.toggle("is-current", i === step);
      }
      for (const note of notes) {
        note.classList.toggle("is-shown", Number(note.dataset.for) === step);
      }
      for (const [i, node] of nodes.entries()) {
        node.classList.toggle("is-current", i === step);
        node.classList.toggle("is-done", i < step);
      }
      for (const line of lines) {
        line.classList.toggle("is-current", line.dataset.step.split(" ").includes(String(step)));
      }
      for (const chip of chips) {
        chip.setAttribute("aria-pressed", String(Number(chip.dataset.goto) === step));
      }
    };

    const setPlaying = (playing) => {
      clearInterval(timer);
      timer = playing
        ? setInterval(() => {
            if (!figure.classList.contains("is-offscreen")) {
              show(step + 1);
            }
          }, 3000)
        : null;

      icon.className = playing ? "fa-solid fa-pause" : "fa-solid fa-play";
      toggle.setAttribute("aria-label", playing ? "Pause" : "Play");
    };

    for (const chip of chips) {
      chip.addEventListener("click", () => {
        setPlaying(false);
        show(Number(chip.dataset.goto));
      });
    }

    toggle.addEventListener("click", () => setPlaying(timer === null));

    figure.classList.add("is-stepping");
    figure.querySelector(".loop-controls").hidden = false;
    show(0);
    setPlaying(!reducedMotion);
  }
}
