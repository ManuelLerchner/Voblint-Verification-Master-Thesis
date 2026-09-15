{
  const strataLabel = (name) => (name === "TD" ? "TD" : name.replace("Voblint_Analysis_", "").replace("Voblint_", ""));

  for (const figure of document.querySelectorAll(".scene-strata")) {
    const svg = figure.querySelector(".strata-svg");
    const parts = figure.querySelectorAll(".stratum-part");
    const name = figure.querySelector(".strata-info-name");
    const meta = figure.querySelector(".strata-info-meta");
    const rests = figure.querySelector(".strata-info-rests");
    const text = figure.querySelector(".strata-info-text");

    const show = (part) => {
      const supports = new Set(part.dataset.rests.split(" ").filter(Boolean));

      for (const other of parts) {
        other.classList.toggle("is-current", other === part);
        other.classList.toggle("is-support", supports.has(other.dataset.name));
        other.closest(".stratum").classList.toggle("is-current", other.closest(".stratum") === part.closest(".stratum"));
      }

      svg.classList.add("has-current");
      name.innerHTML = `<code>${escapeText(part.dataset.name)}</code>`;
      meta.textContent = part.dataset.meta;
      rests.innerHTML = supports.size
        ? `Rests on ${[...supports].map((s) => `<code>${escapeText(strataLabel(s))}</code>`).join(", ")}`
        : "Rests on the logic alone.";
      text.textContent = part.dataset.info;
    };

    for (const part of parts) {
      part.addEventListener("pointerenter", () => show(part));
      part.addEventListener("focus", () => show(part));
    }

    show(figure.querySelector('.stratum-part[data-name="Voblint_Framework"]'));
  }
}
