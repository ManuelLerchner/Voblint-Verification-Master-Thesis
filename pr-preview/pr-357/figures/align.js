{
  for (const figure of document.querySelectorAll(".scene-align")) {
    const buttons = figure.querySelectorAll("[data-filter]");
    const more = figure.querySelector(".align-more");
    if (!more) {
      continue;
    }
    const total = figure.querySelectorAll(".align-row").length;
    const label = (collapsed) => (collapsed ? `Show all ${total} rows` : "Show fewer");

    figure.classList.add("is-collapsed");
    more.textContent = label(true);
    more.hidden = false;
    more.addEventListener("click", () => {
      const collapsed = figure.classList.toggle("is-collapsed");
      more.setAttribute("aria-expanded", String(!collapsed));
      more.textContent = label(collapsed);
    });

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
