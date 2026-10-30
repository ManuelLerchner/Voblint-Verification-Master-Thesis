{
  for (const figure of document.querySelectorAll(".scene-metro")) {
    const name = figure.querySelector(".metro-info-name");
    const text = figure.querySelector(".metro-info-text");
    const stations = figure.querySelectorAll(".metro-station");

    const show = (station) => {
      for (const other of stations) {
        other.classList.toggle("is-current", other === station);
      }

      name.innerHTML = `<code>${escapeText(station.dataset.name)}</code> <span>${escapeText(station.dataset.theory)}</span>`;
      text.textContent = station.dataset.info;
    };

    for (const station of stations) {
      station.addEventListener("pointerenter", () => show(station));
      station.addEventListener("focus", () => show(station));
    }

    show(figure.querySelector(".metro-core"));
  }
}
