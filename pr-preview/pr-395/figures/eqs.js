{
  for (const figure of document.querySelectorAll(".scene-eqs")) {
    const parts = figure.querySelectorAll("[data-edge]");

    const highlight = (edge) => {
      for (const part of parts) {
        part.classList.toggle("is-hl", edge !== null && part.dataset.edge === edge);
      }
    };

    for (const part of parts) {
      part.addEventListener("pointerenter", () => highlight(part.dataset.edge));
      part.addEventListener("focus", () => highlight(part.dataset.edge));
      part.addEventListener("pointerleave", () => highlight(null));
      part.addEventListener("blur", () => highlight(null));
    }
  }
}
