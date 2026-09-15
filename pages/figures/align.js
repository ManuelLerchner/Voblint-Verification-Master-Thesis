{
  for (const figure of document.querySelectorAll(".scene-align")) {
    const buttons = figure.querySelectorAll("[data-filter]");

    for (const button of buttons) {
      button.addEventListener("click", () => {
        figure.dataset.filter = button.dataset.filter;

        for (const other of buttons) {
          other.setAttribute("aria-pressed", String(other === button));
        }
      });
    }
  }
}
