{
  /*
   * What each observer of `ltr` reads, shown against one activation of the run above.
   * `t` is whichever box the reader picks; the table says what the six answers are for
   * each of them, since the shapes differ: `main` is a `Root` with no caller, a callee
   * that has returned nothing yet is a `Call`, and one that has is a `Resume`.
   */
  const LTR = "Voblint/Voblint_CFG/LTR_Def.html#LTR_Def.";

  const ACTS = {
    0: {
      name: "main",
      ctor: "Root",
      steps: 5,
      entry: "{x = ?}",
      sink: "exit_main",
      store: "{x = 3}",
    },
    1: {
      name: "sum(2)",
      ctor: "Resume",
      steps: 6,
      entry: "{n = 2, m = 0, r = 0}",
      sink: "exit_sum",
      store: "{n = 2, m = 1, r = 1}",
      caller: 0,
      callee: 3,
    },
    2: {
      name: "dec(2)",
      ctor: "Call",
      steps: 3,
      entry: "{x = 2}",
      sink: "exit_dec",
      store: "{x = 2}",
      caller: 1,
    },
    3: {
      name: "sum(1)",
      ctor: "Resume",
      steps: 6,
      entry: "{n = 1, m = 0, r = 0}",
      sink: "exit_sum",
      store: "{n = 1, m = 0, r = 0}",
      caller: 1,
      callee: 5,
    },
    4: {
      name: "dec(1)",
      ctor: "Call",
      steps: 3,
      entry: "{x = 1}",
      sink: "exit_dec",
      store: "{x = 1}",
      caller: 3,
    },
    5: {
      name: "sum(0)",
      ctor: "Call",
      steps: 4,
      entry: "{n = 0, m = 0, r = 0}",
      sink: "exit_sum",
      store: "{n = 0, m = 0, r = 0}",
      caller: 3,
    },
  };

  const DEFS = {
    path: "path (Root p) = p | path (Call _ p) = p | path (Resume _ _ p) = p",
    entry: "entry_store t = snd (hd (path t))",
    sinknode: "sink_node t = fst (last (path t))",
    sinkstore: "sink_store t = snd (last (path t))",
    caller:
      "caller_of (Root _) = None | caller_of (Call c _) = Some c | caller_of (Resume cur _ _) = caller_of cur",
    callee: "Resume (ltr_current: ltr) (ltr_callee: ltr) trace",
  };

  const LINKS = {
    path: "path%7Cconst",
    entry: "entry_store%7Cconst",
    sinknode: "sink_node%7Cconst",
    sinkstore: "sink_store%7Cconst",
    caller: "caller_of%7Cconst",
    callee: "ltr%7Ctype",
  };

  const answer = (key, id) => {
    const a = ACTS[id];
    if (key === "path") {
      return `\`path t\` is whichever \`trace\` the constructor carries, here ${a.steps} \`(node, store)\` pairs. Only this activation's own steps are on it.`;
    }
    if (key === "entry") {
      return `\`entry_store t\` is \`${a.entry}\`, the store at the head of the trace, as \`${a.name}\` was entered.`;
    }
    if (key === "sinknode") {
      return `\`sink_node t\` is \`${a.sink}\`, the node of the last pair. Every question of the form “which runs are at node \`v\`” is a question about this.`;
    }
    if (key === "sinkstore") {
      return `\`sink_store t\` is \`${a.store}\`, the store of that same last pair. This is the value \`ltr_collect\` keeps when it buckets traces by node.`;
    }
    if (key === "caller") {
      if (a.caller === undefined) {
        return `\`caller_of t\` is \`None\`. \`${a.name}\` is the \`Root\`: nobody called it, so there is no caller field to read.`;
      }
      const via =
        a.ctor === "Resume"
          ? "descends `ltr_current` rather than stopping at the callee"
          : "reads the `Call`'s own caller field";
      return `\`caller_of t\` is the whole \`${ACTS[a.caller].name}\` trace. \`${a.name}\` is a \`${a.ctor}\`, so this ${via}.`;
    }
    if (a.callee === undefined) {
      return `\`${a.name}\` is a \`${a.ctor}\`, not a \`Resume\`, so there is no finished callee to read. Nothing it called has returned into it yet.`;
    }
    return `\`ltr_callee t\` is the whole \`${ACTS[a.callee].name}\` trace, the call \`${a.name}\` has just finished. It is a selector of the constructor, not a search.`;
  };

  for (const figure of document.querySelectorAll(".scene-obs")) {
    const layout = figure.querySelector(".obs-layout");
    const answerBox = figure.querySelector(".obs-answer");
    const title = figure.querySelector(".obs-subject");
    const buttons = [...figure.querySelectorAll("[data-obs]")];
    const chips = [...figure.querySelectorAll("[data-key]")];
    const boxes = [...figure.querySelectorAll("[data-box]")];

    let subject = 3;
    let pinned = null;

    const chipsOf = (id) => chips.filter((c) => Number(c.dataset.key.split(":")[0]) === id);

    const lit = (key) => {
      const a = ACTS[subject];
      if (key === "path") return { chips: chipsOf(subject) };
      if (key === "entry") return { chips: chipsOf(subject).slice(0, 1) };
      if (key === "sinknode" || key === "sinkstore") return { chips: chipsOf(subject).slice(-1) };
      if (key === "caller") return { boxes: a.caller === undefined ? [] : [a.caller] };
      return { boxes: a.callee === undefined ? [] : [a.callee] };
    };

    /* Hover previews, click keeps: the answer carries a link into the theory, so it has to
       survive the pointer leaving the button. */
    const paint = (button) => {
      layout.classList.toggle("is-lighting", Boolean(button));
      for (const other of buttons) {
        other.classList.toggle("is-on", other === button);
      }
      for (const node of [...chips, ...boxes]) {
        node.classList.remove("is-lit");
      }

      if (!button) {
        answerBox.innerHTML = withCode(
          `Hover an observer to see what it reads, click to keep it. Click an activation on the right to make it \`t\`.`,
        );
        return;
      }

      const key = button.dataset.obs;
      const on = lit(key);
      for (const chip of on.chips ?? []) chip.classList.add("is-lit");
      for (const id of on.boxes ?? []) {
        const box = boxes.find((b) => Number(b.dataset.box) === id);
        if (box) box.classList.add("is-lit");
      }
      const where = `<a href="${LTR}${LINKS[key]}"><code>${DEFS[key]}</code></a>`;
      answerBox.innerHTML = `${withCode(answer(key, subject))} <span class="obs-def">${where}</span>`;
    };

    const choose = (id) => {
      subject = id;
      for (const box of boxes) {
        box.classList.toggle("is-subject", Number(box.dataset.box) === id);
      }
      title.innerHTML = withCode(`\`t = ${ACTS[id].name}\`, a \`${ACTS[id].ctor}\``);
      paint(pinned);
    };

    for (const button of buttons) {
      button.addEventListener("pointerenter", () => paint(button));
      button.addEventListener("focus", () => paint(button));
      button.addEventListener("pointerleave", () => paint(pinned));
      button.addEventListener("blur", () => paint(pinned));
      button.addEventListener("click", () => {
        pinned = pinned === button ? null : button;
        paint(pinned);
      });
    }

    for (const box of boxes) {
      box.addEventListener("click", (event) => {
        event.stopPropagation();
        choose(Number(box.dataset.box));
      });
    }

    choose(3);
    pinned = buttons[0];
    paint(pinned);
  }
}
