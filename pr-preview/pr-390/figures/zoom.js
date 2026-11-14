{
  for (const figure of document.querySelectorAll(".scene-zoom")) {
    const levels = [...figure.querySelectorAll(".zoom-level")];
    const gauge = figure.querySelectorAll(".zoom-gauge [data-goto]");
    const range = figure.querySelector(".zoom-range");
    let level = 0;

    const show = (next) => {
      level = Math.max(0, Math.min(levels.length - 1, next));
      figure.dataset.level = String(level);
      range.value = String(level);

      levels.forEach((card, i) => {
        card.classList.toggle("is-current", i === level);
        card.classList.toggle("is-above", i === level - 1);
        card.classList.toggle("is-past", i < level - 1);
        card.classList.toggle("is-below", i > level);
        card.setAttribute("aria-hidden", String(i !== level));
      });

      gauge.forEach((button) => {
        const i = Number(button.dataset.goto);
        button.setAttribute("aria-pressed", String(i === level));
        button.classList.toggle("is-passed", i < level);
      });
    };

    gauge.forEach((button) => {
      button.addEventListener("click", () => show(Number(button.dataset.goto)));
    });
    figure.querySelector(".zoom-in").addEventListener("click", () => show(level + 1));
    figure.querySelector(".zoom-out").addEventListener("click", () => show(level - 1));
    range.addEventListener("input", () => show(Number(range.value)));
    figure.querySelector(".zoom-controls").hidden = false;
    figure.classList.add("is-interactive");
    show(0);
  }
}
