{
  for (const figure of document.querySelectorAll(".scene-island")) {
    const note = figure.querySelector(".island-note");
    const idle = note.textContent;

    for (const region of figure.querySelectorAll("[data-note]")) {
      const show = () => {
        note.innerHTML = withCode(region.dataset.note);
      };
      region.addEventListener("pointerenter", show);
      region.addEventListener("focus", show);
      region.addEventListener("pointerleave", () => {
        note.textContent = idle;
      });
      region.addEventListener("blur", () => {
        note.textContent = idle;
      });
    }
  }
}
