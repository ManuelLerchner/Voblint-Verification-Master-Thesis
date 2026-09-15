{
  /*
   * One entry per source step of the factorial run, with the graph steps csim_step matches
   * it to and the trace constructors valid_ltr applies. Residuals flatten the nested Seq;
   * trees list each activation's path, its live callee and whether it has returned.
   */
  const FRAME_MAIN = "Frame {a = ?} a";
  const FRAME_F2 = "Frame {n = 2, r = 0} r";
  const RET_MAIN = "(pp6, a, {a = ?})";
  const RET_F2 = "(pp3, r, {n = 2, r = 0})";
  const CHECK = "check(a == 2)";

  const act = (name, ctor, path, child = null, done = false) => ({ name, ctor, path, child, done });

  const RUN_STEPS = [
    {
      line: "calla",
      edges: ["body_main"],
      node: "pp5",
      store: "a = ?",
      residual: ["a = f(2)", CHECK],
      frames: [],
      rets: [],
      callers: [],
      rules: {
        source: "start (main body, s₀, [])",
        graph: "Intra body(main)",
        trace: "Root, intra",
      },
      tree: act("main", "Root", ["entry_main", "pp5"]),
      text: "The run starts in `main` with no frames. The source is about to run `a = f(2)`. The matching graph configuration already sits at `pp5`: its trace starts with `Root` at `entry_main` and has taken `main`'s body edge.",
    },
    {
      line: "if",
      edges: ["call_main", "body_f"],
      node: "pp0",
      store: "n = 2, r = 0",
      residual: ["if (n < 2) …", "Restore", CHECK],
      frames: [FRAME_MAIN],
      rets: [RET_MAIN],
      callers: ["main"],
      rules: { source: "Call", graph: "Call, Intra body(f)", trace: "call, intra" },
      tree: act("main", "Root", ["entry_main", "pp5"], act("f(2)", "Call", ["entry_f", "pp0"])),
      text: "The source `Call` evaluates `2`, binds it to `n` in a fresh store, pushes a frame that remembers the caller's store and the destination `a`, and runs `f`'s body followed by `Restore`. The graph takes the call edge, pushes the return point `pp6` and follows `f`'s body edge. The trace opens a new activation, `Call main …`.",
    },
    {
      line: "call",
      edges: ["ge"],
      node: "pp2",
      store: "n = 2, r = 0",
      residual: ["r = f(n - 1)", "return n * r", "Restore", CHECK],
      frames: [FRAME_MAIN],
      rets: [RET_MAIN],
      callers: ["main"],
      rules: { source: "IfFalse", graph: "Intra ¬ n < 2", trace: "intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp5"],
        act("f(2)", "Call", ["entry_f", "pp0", "pp2"]),
      ),
      text: "`n < 2` is false. Both sides take the else branch, and the trace extends its path.",
    },
    {
      line: "if",
      edges: ["call_f", "body_f"],
      node: "pp0",
      store: "n = 1, r = 0",
      residual: ["if (n < 2) …", "Restore", "return n * r", "Restore", CHECK],
      frames: [FRAME_F2, FRAME_MAIN],
      rets: [RET_F2, RET_MAIN],
      callers: ["f(2)", "main"],
      rules: { source: "Call", graph: "Call, Intra body(f)", trace: "call, intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp5"],
        act("f(2)", "Call", ["entry_f", "pp0", "pp2"], act("f(1)", "Call", ["entry_f", "pp0"])),
      ),
      text: "The recursive call. Each side grows its stack by one entry, a frame, a return point `pp3`, a trace nested one level deeper: `Call (Call (Root …) …) …`. The graph reuses the same node `entry_f`.",
    },
    {
      line: "ret1",
      edges: ["lt"],
      node: "pp1",
      store: "n = 1, r = 0",
      residual: ["return 1", "Restore", "return n * r", "Restore", CHECK],
      frames: [FRAME_F2, FRAME_MAIN],
      rets: [RET_F2, RET_MAIN],
      callers: ["f(2)", "main"],
      rules: { source: "IfTrue", graph: "Intra n < 2", trace: "intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp5"],
        act(
          "f(2)",
          "Call",
          ["entry_f", "pp0", "pp2"],
          act("f(1)", "Call", ["entry_f", "pp0", "pp1"]),
        ),
      ),
      text: "Now `n = 1`, so `n < 2` holds.",
    },
    {
      line: "ret1",
      edges: ["ret1"],
      node: "exit_f",
      store: "n = 1, r = 0, #ret = 1",
      residual: ["Unwind", "Restore", "return n * r", "Restore", CHECK],
      frames: [FRAME_F2, FRAME_MAIN],
      rets: [RET_F2, RET_MAIN],
      callers: ["f(2)", "main"],
      rules: { source: "ReturnSome", graph: "Intra return 1", trace: "intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp5"],
        act(
          "f(2)",
          "Call",
          ["entry_f", "pp0", "pp2"],
          act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"]),
        ),
      ),
      text: "`return 1` writes the return variable `#ret` and turns the rest of the body into `Unwind`. The graph reaches `exit_f`, the one result node that every activation of `f` shares.",
    },
    {
      line: "call",
      edges: ["resume_f"],
      node: "pp3",
      store: "n = 2, r = 1",
      residual: ["SKIP", "return n * r", "Restore", CHECK],
      frames: [FRAME_MAIN],
      rets: [RET_MAIN],
      callers: ["main"],
      rules: { source: "UnwindAct", graph: "Return", trace: "ret: Resume" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp5"],
        act(
          "f(2)",
          "Resume",
          ["entry_f", "pp0", "pp2", "pp3"],
          act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true),
        ),
      ),
      text: "The source pops its frame: the caller's locals come back and `r := #ret`. The graph pops its return point, jumps to `pp3` without following an edge, and applies `combine_collect`. The trace builds `Resume`: the caller's path continues at `pp3`, and the finished callee stays inside it.",
    },
    {
      line: "retn",
      edges: [],
      node: "pp3",
      store: "n = 2, r = 1",
      residual: ["return n * r", "Restore", CHECK],
      frames: [FRAME_MAIN],
      rets: [RET_MAIN],
      callers: ["main"],
      rules: { source: "Seq1", graph: "no step", trace: "no step" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp5"],
        act(
          "f(2)",
          "Resume",
          ["entry_f", "pp0", "pp2", "pp3"],
          act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true),
        ),
      ),
      text: "`Seq SKIP c` steps to `c`, and the graph does not move. The simulation allows zero graph steps: `csim` relates both source configurations to `pp3`.",
    },
    {
      line: "retn",
      edges: ["retn"],
      node: "exit_f",
      store: "n = 2, r = 1, #ret = 2",
      residual: ["Unwind", "Restore", CHECK],
      frames: [FRAME_MAIN],
      rets: [RET_MAIN],
      callers: ["main"],
      rules: { source: "ReturnSome", graph: "Intra return n * r", trace: "intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp5"],
        act(
          "f(2)",
          "Resume",
          ["entry_f", "pp0", "pp2", "pp3", "exit_f"],
          act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true),
        ),
      ),
      text: "`return n * r` writes `#ret = 2`. The graph reaches `exit_f` again, this time for the outer activation.",
    },
    {
      line: "calla",
      edges: ["resume_main"],
      node: "pp6",
      store: "a = 2",
      residual: ["SKIP", CHECK],
      frames: [],
      rets: [],
      callers: [],
      rules: { source: "UnwindAct", graph: "Return", trace: "ret: Resume" },
      tree: act(
        "main",
        "Resume",
        ["entry_main", "pp5", "pp6"],
        act(
          "f(2)",
          "Resume",
          ["entry_f", "pp0", "pp2", "pp3", "exit_f"],
          act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true),
          true,
        ),
      ),
      text: "The second `Resume` returns to `main` with `a = 2`. All three stacks are empty again, and `main`'s trace holds both calls, one inside the other.",
    },
    {
      line: "check",
      edges: [],
      node: "pp6",
      store: "a = 2",
      residual: [CHECK],
      frames: [],
      rets: [],
      callers: [],
      rules: { source: "Seq1", graph: "no step", trace: "no step" },
      tree: act(
        "main",
        "Resume",
        ["entry_main", "pp5", "pp6"],
        act(
          "f(2)",
          "Resume",
          ["entry_f", "pp0", "pp2", "pp3", "exit_f"],
          act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true),
          true,
        ),
      ),
      text: "Another source step with no graph counterpart.",
    },
    {
      line: "check",
      edges: ["check"],
      node: "pp7",
      store: "a = 2",
      residual: ["SKIP"],
      frames: [],
      rets: [],
      callers: [],
      rules: { source: "Check", graph: "Intra check(a == 2)", trace: "intra" },
      tree: act(
        "main",
        "Resume",
        ["entry_main", "pp5", "pp6", "pp7"],
        act(
          "f(2)",
          "Resume",
          ["entry_f", "pp0", "pp2", "pp3", "exit_f"],
          act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true),
          true,
        ),
      ),
      text: "The check runs in the store `a = 2`. That store is one element of `ltr_collect pp6`, the set the analysis result at `pp6` has to contain.",
    },
    {
      line: null,
      edges: ["ret_main"],
      node: "exit_main",
      store: "a = 2",
      residual: ["SKIP"],
      frames: [],
      rets: [],
      callers: [],
      rules: { source: "done (SKIP, s, [])", graph: "Intra return", trace: "intra" },
      tree: act(
        "main",
        "Resume",
        ["entry_main", "pp5", "pp6", "pp7", "exit_main"],
        act(
          "f(2)",
          "Resume",
          ["entry_f", "pp0", "pp2", "pp3", "exit_f"],
          act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true),
          true,
        ),
      ),
      text: "The source has finished. The graph still takes `main`'s implicit return edge to `exit_main`, and `source_completes_ltr_collect_exit` puts the final store into the collecting semantics there.",
    },
  ];

  function renderActivation(a, sink) {
    const box = document.createElement("div");
    box.className = "run-act";
    box.classList.toggle("is-done", a.done);
    box.classList.toggle("is-sink", a === sink);

    const head = document.createElement("p");
    head.className = "run-act-head";
    head.innerHTML = `<code>${escapeText(a.ctor)}</code> <span>${escapeText(a.name)}</span>${a.done ? " <small>returned, kept inside Resume</small>" : ""}`;

    const path = document.createElement("div");
    path.className = "run-path";
    a.path.forEach((node, i) => {
      const chip = document.createElement("span");
      chip.textContent = node;
      chip.classList.toggle("is-last", a === sink && i === a.path.length - 1);
      path.append(chip);
    });

    box.append(head, path);

    if (a.child) {
      box.append(renderActivation(a.child, sink));
    }

    return box;
  }

  function sinkOf(a) {
    return a.child && !a.child.done ? sinkOf(a.child) : a;
  }

  function fillStack(list, items, empty) {
    list.replaceChildren(
      ...(items.length ? items : [empty]).map((text) => {
        const item = document.createElement("li");
        item.innerHTML = withCode(`\`${text}\``);
        item.classList.toggle("empty", !items.length);
        return item;
      }),
    );
  }

  for (const figure of document.querySelectorAll(".scene-run")) {
    const lines = figure.querySelectorAll(".run-code [data-nodes]");
    const nodes = figure.querySelectorAll(".run-nodes [data-node]");
    const edges = figure.querySelectorAll(".run-edges [data-edge]");
    const residual = figure.querySelector(".run-residual");
    const tree = figure.querySelector(".run-tree");
    const caption = figure.querySelector(".run-caption");
    let state = RUN_STEPS[0];

    const light = (names) => {
      for (const node of nodes) {
        node.classList.toggle("is-hover", names.includes(node.dataset.node));
      }
    };

    const render = (i) => {
      state = RUN_STEPS[i];

      for (const line of lines) {
        line.classList.toggle("is-current", line.dataset.line === state.line);
      }

      for (const node of nodes) {
        node.classList.toggle("is-current", node.dataset.node === state.node);
      }

      for (const edge of edges) {
        edge.classList.toggle("is-taken", state.edges.includes(edge.dataset.edge));
      }

      residual.replaceChildren(
        ...state.residual.map((part, j) => {
          const chip = document.createElement("code");
          chip.textContent = part;
          chip.className = /^(Restore|Unwind|SKIP)$/.test(part) ? "runtime" : "";
          chip.classList.toggle("is-next", j === 0);
          return chip;
        }),
      );

      fillStack(figure.querySelector(".run-frames"), state.frames, "[]");
      fillStack(figure.querySelector(".run-cframes"), state.rets, "[]");
      fillStack(figure.querySelector(".run-callers"), state.callers, "None");

      tree.replaceChildren(renderActivation(state.tree, sinkOf(state.tree)));

      for (const [kind, text] of Object.entries(state.rules)) {
        const rule = figure.querySelector(`[data-rule="${kind}"]`);
        rule.textContent = text;
        rule.classList.toggle("none", text === "no step");
      }

      figure.querySelector(".run-store").textContent = `{${state.store}}`;
      caption.innerHTML = withCode(state.text);
    };

    for (const line of lines) {
      line.addEventListener("pointerenter", () =>
        light(line.dataset.nodes.split(" ").filter(Boolean)),
      );
      line.addEventListener("pointerleave", () => light([]));
    }

    makeStepper(figure, {
      count: RUN_STEPS.length,
      render,
      controls: figure.querySelector(".run-controls"),
      chipsBox: figure.querySelector(".run-steps"),
      interval: 4200,
      autoplay: false,
    });
  }
}
