{
  /* What each theorem rules out, told as the failure an analysis without it could show. */
  const BRIDGE_FAILURES = {
    1: "Without compiler simulation, a compiler could drop the edge for the `else` branch of `if (n < 2)`. Runs with `n ≥ 2` would exist in the source but not in the graph, and the analysis could report `return n * r` as DEAD.",
    2: "Without sound transfers, a single wrong lemma suffices: Goblint's congruence subtraction computed `3ℤ − 2 = 3ℤ` and turned a live branch DEAD, the bug replayed earlier on this page.",
    3: "Without context coverage, a policy could file a call under a key that no call site seeds. That copy of the callee starts from `⊥`, its body looks unreachable, and its checks read DEAD.",
    4: "Without a post-solution, stop the solver after its first pass over the counting loop: `H = [0, 1]`, so `X = assume(i ≥ 5) [0, 1] = ⊥`, and the check after the loop reads DEAD although every run reaches it. The solver promises a post-solution only when it terminates.",
    5: "Without honest verdicts, a classifier could say PROVED for `i == 5` whenever `5` lies in the interval, so `[0, 5]` would prove it too. `classify_proved` demands that every store in `γ` satisfies the check.",
  };

  const BRIDGE_X = { 1: 267, 2: 383, 3: 500, 4: 617, 5: 733 };

  for (const figure of document.querySelectorAll(".scene-bridge")) {
    const toggles = figure.querySelectorAll(".bridge-toggles button");
    const pillars = figure.querySelectorAll(".bridge-pillars [data-pillar]");
    const segments = figure.querySelectorAll(".bridge-deck [data-seg]");
    const run = figure.querySelector(".bridge-run");
    const caption = figure.querySelector(".bridge-caption");
    const idle = caption.innerHTML;
    const removed = new Set();
    let t = 0;
    let last = 0;

    const place = (x, y) =>
      run.setAttribute("transform", `translate(${x.toFixed(1)} ${y.toFixed(1)})`);

    const render = () => {
      const order = [...removed].sort();
      figure.dataset.broken = order.join(" ");

      for (const pillar of pillars) {
        pillar.classList.toggle("is-removed", removed.has(Number(pillar.dataset.pillar)));
      }

      for (const button of toggles) {
        button.setAttribute("aria-pressed", String(!removed.has(Number(button.dataset.pillar))));
      }

      /* Segment k spans pillars k and k + 1; it sags toward whichever supporting end is gone. */
      segments.forEach((segment, k) => {
        const leftGone = removed.has(k);
        const rightGone = removed.has(k + 1);
        const left = Number(segment.getAttribute("x"));
        const right = left + Number(segment.getAttribute("width"));
        segment.style.transformOrigin = `${leftGone ? right : left}px 143px`;
        segment.style.transform =
          leftGone && rightGone
            ? "translateY(150px)"
            : rightGone
              ? "rotate(24deg)"
              : leftGone
                ? "rotate(-24deg)"
                : "none";
        segment.classList.toggle("is-broken", leftGone || rightGone);
      });

      caption.innerHTML = order.length
        ? order.map((k) => `<span>${withCode(BRIDGE_FAILURES[k])}</span>`).join("")
        : idle;
      t = 0;
    };

    /* The run walks the deck; at the first missing pillar it drops into the valley. */
    const frame = (now) => {
      const dt = last ? Math.min(50, now - last) : 16;
      last = now;

      if (!figure.classList.contains("is-offscreen")) {
        t += dt / 1000;
        const first = [...removed].sort()[0];
        const stop = first ? BRIDGE_X[first] : 850;
        const x = Math.min(40 + t * 150, stop);
        const falling = first && x >= stop ? t - (stop - 40) / 150 : 0;
        const y = 124 + falling * falling * 260;
        place(first ? x : Math.min(x, 926), Math.min(y, 330));
        run.classList.toggle("is-lost", Boolean(first) && falling > 0);
        run.classList.toggle("is-home", !first && x >= 850);

        if (t > 6) {
          t = 0;
        }
      }

      requestAnimationFrame(frame);
    };

    for (const button of toggles) {
      button.addEventListener("click", () => {
        const k = Number(button.dataset.pillar);
        removed.has(k) ? removed.delete(k) : removed.add(k);
        render();
      });
    }

    for (const pillar of pillars) {
      pillar.addEventListener("click", () =>
        figure.querySelector(`.bridge-toggles [data-pillar="${pillar.dataset.pillar}"]`).click(),
      );
    }

    render();

    if (reducedMotion) {
      place(926, 124);
    } else {
      requestAnimationFrame(frame);
    }
  }
}
