{
  /*
   * Pick a node, see its equation built. The markup ships every node's
   * derivation and the figure reveals one, so without script the panel still
   * has content and the page still says how an equation is made.
   */
  for (const figure of document.querySelectorAll(".scene-gen")) {
    const nodes = figure.querySelectorAll("[data-node]");
    const edges = figure.querySelectorAll("[data-edge]");
    const builds = figure.querySelectorAll(".gen-build");

    /* All derivations occupy one grid cell so the panel keeps the height of the
       tallest, and hovering cannot resize the figure under the cursor. Done
       here rather than in the markup: without script they stay in flow. */
    const panel = builds[0].parentElement;

    panel.classList.add("gen-stack");

    for (const build of builds) {
      build.hidden = false;
    }

    const show = (name) => {
      figure.dataset.node = name;

      for (const node of nodes) {
        node.classList.toggle("is-hl", node.dataset.node === name);
      }

      /* An edge is highlighted when it is one this node reads from. Which
         those are is on the node itself, so a second graph needs no script. */
      const reads = (figure.querySelector(`[data-node="${name}"]`)?.dataset.edges ?? "")
        .split(/\s+/)
        .filter(Boolean);

      for (const edge of edges) {
        edge.classList.toggle("is-hl", reads.includes(edge.dataset.edge));
      }

      for (const build of builds) {
        const on = build.dataset.for === name;

        build.classList.toggle("is-shown", on);
        build.setAttribute("aria-hidden", String(!on));
      }
    };

    for (const node of nodes) {
      const pick = () => show(node.dataset.node);

      node.addEventListener("pointerenter", pick);
      node.addEventListener("click", pick);
      node.addEventListener("focus", pick);
    }

    show(figure.dataset.node);
  }
}
