{
  /*
   * Two analyses, one question. The markup shows the combined run of the first
   * program; the tabs pick the program and the selection of analyses, and each
   * pair has its own pre-rendered view.
   */
  for (const figure of document.querySelectorAll(".scene-coop")) {
    const progTabs = figure.querySelectorAll("[data-prog][role='tab']");
    const selTabs = figure.querySelectorAll("[data-sel][role='tab']");

    const render = () => {
      const { prog, sel } = figure.dataset;

      for (const tab of progTabs) {
        tab.setAttribute("aria-selected", String(tab.dataset.prog === prog));
      }
      for (const tab of selTabs) {
        tab.setAttribute("aria-selected", String(tab.dataset.sel === sel));
      }
      for (const code of figure.querySelectorAll(".coop-prog")) {
        code.hidden = code.dataset.prog !== prog;
      }
      for (const view of figure.querySelectorAll(".coop-view")) {
        view.hidden = view.dataset.view !== `${prog}-${sel}`;
      }
    };

    for (const tab of progTabs) {
      tab.addEventListener("click", () => {
        figure.dataset.prog = tab.dataset.prog;
        render();
      });
    }
    for (const tab of selTabs) {
      tab.addEventListener("click", () => {
        figure.dataset.sel = tab.dataset.sel;
        render();
      });
    }

    for (const group of figure.querySelectorAll(".coop-progs, .coop-sels")) {
      group.hidden = false;
    }
    render();
  }
}
