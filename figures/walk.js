{
  /*
   * One equation per node. Generation has no order: each node's equation is built
   * from its own incoming edges, independently of the others. So the figure shows
   * every equation at once and plays nothing; selecting a node, its source line or
   * its chip highlights that node's equation and note. The last note is the
   * overview, shown while nothing is selected.
   */
  for (const figure of document.querySelectorAll(".scene-walk")) {
    const overview = Number(figure.dataset.steps) - 1;
    const callStep = Number(figure.dataset.callStep);
    const chips = figure.querySelectorAll("[data-goto]");
    const eqs = figure.querySelectorAll(".walk-eq");
    const notes = figure.querySelectorAll(".walk-note");
    const nodes = figure.querySelectorAll(".walk-node");
    const lines = figure.querySelectorAll(".walk-code .wl");

    const show = (step) => {
      figure.dataset.step = String(step);
      figure.classList.toggle("is-call", step === callStep);

      for (const [i, eq] of eqs.entries()) {
        eq.classList.add("is-shown");
        eq.classList.toggle("is-current", i === step);
      }
      for (const note of notes) {
        note.classList.toggle("is-shown", Number(note.dataset.for) === step);
      }
      for (const [i, node] of nodes.entries()) {
        node.classList.toggle("is-current", i === step);
      }
      for (const line of lines) {
        line.classList.toggle("is-current", line.dataset.step.split(" ").includes(String(step)));
      }
      for (const chip of chips) {
        chip.setAttribute("aria-pressed", String(Number(chip.dataset.goto) === step));
      }
    };

    const select = (step) => () => show(step);

    for (const chip of chips) {
      chip.addEventListener("click", select(Number(chip.dataset.goto)));
    }
    for (const [i, node] of nodes.entries()) {
      node.style.cursor = "pointer";
      node.addEventListener("click", select(i));
    }
    for (const line of lines) {
      line.style.cursor = "pointer";
      line.addEventListener("click", select(Number(line.dataset.step.split(" ").at(-1))));
    }

    figure.classList.add("is-stepping");
    figure.querySelector(".loop-controls").hidden = false;
    show(overview);
  }
}
