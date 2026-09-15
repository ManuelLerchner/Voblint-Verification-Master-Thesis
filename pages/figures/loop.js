{
  /*
   * The loop stepper. The markup ships the final step, so without script the figure
   * still shows the proved check; with it, the steps play and the chips jump.
   */
  for (const figure of document.querySelectorAll(".scene-loop")) {
    const steps = Number(figure.dataset.steps);
    const chips = figure.querySelectorAll("[data-goto]");
    const toggle = figure.querySelector(".loop-play");
    const icon = toggle.querySelector("i");
    let step = 0;
    let timer = null;

    const show = (next) => {
      step = (next + steps) % steps;
      figure.dataset.step = String(step);

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
          }, 2200)
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

    figure.querySelector(".loop-controls").hidden = false;
    show(0);
    setPlaying(!reducedMotion);
  }
}
