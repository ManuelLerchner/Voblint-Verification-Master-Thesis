/*
 * Solve replay: steps through a run's solve on its control-flow graph.
 *
 * The replay reads the JSON Lines trace of the shown run, the events the exported
 * solver reports through its traced code equations. From the events alone it
 * rebuilds what the solver holds after each step: every local unknown's value, the
 * unknowns being solved (the solver's call stack), the stable ones, and the ones an
 * update destabilized. Destabilization follows the solver's own rule: an update clears
 * the influence set of the updated unknown and removes each reader from the stable set,
 * continuing through the readers' influence sets except for readers still being solved.
 *
 * Nothing here feeds back into the result on the page.
 */

/* Replay states kept for jumps: stepping back or dragging the slider replays at most this many events. */
const SNAPSHOT_EVERY = 256;
/* Characters of a value shown inside a node; the node itself sizes for this many. */
const VALUE_CHARS = 30;
/* Trace lines kept around the current step in the text pane. */
const TRACE_WINDOW = 60;

const UNREACHED = "not reached";

function query(selector) {
  const element = document.querySelector(selector);

  if (!element) {
    throw new Error(`Missing page element ${selector}`);
  }

  return element;
}

/* The name the result gives a context, as cli/result/result_text.ml's context_label writes it. */
function contextLabel(context) {
  switch (context?.kind) {
    case "unit":
      return "unit";
    case "entry_state":
      return context.values.length > 0 ? context.values.join(", ") : "root context";
    case "call_string":
      return context.sites.length > 0 ? `call-string=${context.sites.join(" ")}` : "root context";
    default:
      return "?";
  }
}

function localKey(unknown) {
  return `L:${unknown.node}|${contextLabel(unknown.context)}`;
}

function globalKey(unknown) {
  return unknown.kind === "activation_seed"
    ? `G:${unknown.procedure}|${contextLabel(unknown.context)}`
    : "G:Global";
}

/* A global unknown as the page's seed list names it. */
function globalName(key) {
  if (key === "G:Global") {
    return "Global";
  }

  const [procedure, context] = key.slice(2).split("|");

  return `enter ${procedure} @ ${context}`;
}

/* One analysis's value loses its "interval: " prefix; a product keeps every label. */
function shortValue(value) {
  const bare = value.includes("; ") ? value : value.replace(/^[^:;=]+: /, "");

  return bare.length > VALUE_CHARS ? `${bare.slice(0, VALUE_CHARS - 1)}…` : bare;
}

/* ------------------------------------------------------------- solver state */

function emptyState() {
  return {
    values: new Map(),
    seen: new Set(),
    stable: new Set(),
    destabilized: new Set(),
    stack: [],
    infl: new Map(),
    globals: new Map(),
  };
}

function copyState(state) {
  return {
    values: new Map(state.values),
    seen: new Set(state.seen),
    stable: new Set(state.stable),
    destabilized: new Set(state.destabilized),
    stack: [...state.stack],
    infl: new Map([...state.infl].map(([key, readers]) => [key, [...readers]])),
    globals: new Map(state.globals),
  };
}

/* The frames above [key] have returned: an event of [key] happens in its own frame. */
function returnTo(state, key) {
  const at = state.stack.lastIndexOf(key);

  if (at !== -1) {
    state.stack.length = at + 1;
  }
}

function addReader(state, key, reader) {
  const readers = state.infl.get(key);

  if (!readers) {
    state.infl.set(key, [reader]);
  } else if (!readers.includes(reader)) {
    readers.push(reader);
  }
}

function destabilize(state, key) {
  const work = [key];

  while (work.length > 0) {
    const next = work.pop();
    const readers = state.infl.get(next);

    if (!readers) {
      continue;
    }

    state.infl.delete(next);

    for (const reader of readers) {
      if (state.stable.delete(reader)) {
        state.destabilized.add(reader);
      }

      if (!state.stack.includes(reader)) {
        work.push(reader);
      }
    }
  }
}

function apply(state, event) {
  const current = event.current ? localKey(event.current) : null;

  if (current) {
    returnTo(state, current);
  }

  switch (event.event) {
    case "solve":
    case "resolve": {
      const key = localKey(event.unknown);

      state.seen.add(key);
      state.stable.add(key);
      state.destabilized.delete(key);

      if (state.stack.at(-1) !== key) {
        state.stack.push(key);
      }

      break;
    }
    case "query_local":
      state.seen.add(localKey(event.target));
      break;
    case "value_local":
      addReader(state, localKey(event.target), current);
      break;
    case "query_global": {
      const key = globalKey(event.target);

      addReader(state, key, current);
      state.globals.set(key, event.value);
      break;
    }
    case "side": {
      const key = globalKey(event.target);

      if (!state.globals.has(key)) {
        state.globals.set(key, "⊥");
      }

      break;
    }
    case "update_global": {
      const key = globalKey(event.unknown);

      state.globals.set(key, event.new);
      destabilize(state, key);
      break;
    }
    case "update_local": {
      const key = localKey(event.unknown);

      returnTo(state, key);
      state.values.set(key, event.new);
      destabilize(state, key);
      break;
    }
    default:
      break;
  }
}

/* ---------------------------------------------------------------- the trace */

function parseEvents(jsonl) {
  return jsonl
    .split("\n")
    .filter((line) => line.trim() !== "")
    .map((line) => JSON.parse(line))
    .filter((record) => Number.isInteger(record.step));
}

/* Names as the CLI's trace writes them (cli/render/solver_trace.ml). */
function traceContext(context) {
  switch (context?.kind) {
    case "unit":
      return "unit";
    case "entry_state":
      return context.values.length > 0 ? `[${context.values.join(", ")}]` : "root";
    case "call_string":
      return context.sites.length > 0 ? `[${context.sites.join(" ")}]` : "root";
    default:
      return "?";
  }
}

function traceLocal(unknown) {
  return `(${unknown.node}, ${traceContext(unknown.context)})`;
}

function traceGlobal(unknown) {
  return unknown.kind === "activation_seed"
    ? `Seed(${unknown.procedure}, ${traceContext(unknown.context)})`
    : "Global";
}

/* One step's label, subject and detail lines. */
function stepText(event) {
  switch (event.event) {
    case "solve":
    case "resolve":
      return [event.event.toUpperCase(), traceLocal(event.unknown), []];
    case "query_local":
      return ["QUERY-L", `${traceLocal(event.current)} -> ${traceLocal(event.target)}`, []];
    case "value_local":
      return [
        "VALUE-L",
        `${traceLocal(event.target)} to ${traceLocal(event.current)}`,
        [["value", event.value]],
      ];
    case "query_global":
      return [
        "QUERY-G",
        `${traceLocal(event.current)} -> ${traceGlobal(event.target)}`,
        [["value", event.value]],
      ];
    case "side":
      return [
        "SIDE",
        `${traceLocal(event.current)} -> ${traceGlobal(event.target)}`,
        [["value", event.value]],
      ];
    case "update_global":
      return [
        "UPDATE-G",
        `${traceGlobal(event.unknown)} (readers destabilized)`,
        [
          ["old", event.old],
          ["new", event.new],
        ],
      ];
    case "update_local":
      return [
        "UPDATE-L",
        `${traceLocal(event.unknown)} (readers destabilized)`,
        [
          ["old", event.old],
          ["new", event.new],
        ],
      ];
    case "answer":
      return ["ANSWER", traceLocal(event.current), [["value", event.value]]];
    case "route":
      return [
        "ROUTE",
        `call at ${traceLocal(event.call)} -> context ${traceContext(event.context)}`,
        [["entry", event.entry]],
      ];
    default:
      return [event.event, "", []];
  }
}

/* One block per step, indented by the solver's call depth after it. */
function stepBlock(event, index, depth) {
  const indent = "  ".repeat(depth);
  const [label, subject, details] = stepText(event);
  const head = `[${String(index + 1).padStart(3, "0")}] ${indent}${label.padEnd(9)} ${subject}`;

  return [head, ...details.map(([key, value]) => `      ${indent}${key} = ${value}`)].join("\n");
}

/* --------------------------------------------------------------------- view */

export function createSolveReplay(deps) {
  const panel = query("#solve-replay");
  const count = query("#solve-replay-count");
  const message = query("#solve-replay-message");
  const retry = query("#solve-replay-load");
  const body = query("#solve-replay-body");
  const graph = query("#solve-replay-graph");
  const globalsList = query("#solve-replay-globals");
  const tracePane = query("#solve-replay-trace");
  const detail = query("#solve-replay-detail");
  const slider = query("#solve-replay-slider");
  const stepLabel = query("#solve-replay-step");
  const speed = query("#solve-replay-speed");
  const buttons = {
    start: query("#solve-replay-start"),
    back: query("#solve-replay-back"),
    play: query("#solve-replay-play"),
    forward: query("#solve-replay-forward"),
    end: query("#solve-replay-end"),
  };

  /* The run offered for replay, and what was loaded from it. */
  let offered = null;
  let loading = null;
  let replay = null;
  let cy = null;
  let playing = 0;
  let selected = null;
  /* What each drawn node shows, so a step touches only nodes that changed. */
  let drawn = new Map();

  function setMessage(text, { canRetry = false, kind = "" } = {}) {
    message.textContent = text;
    message.className = kind ? `solver-globals-note ${kind}` : "solver-globals-note";
    message.hidden = text === "";
    retry.hidden = !canRetry;
  }

  function stop() {
    cancelAnimationFrame(playing);
    playing = 0;
    buttons.play.querySelector("i").className = "fa-solid fa-play";
    buttons.play.setAttribute("aria-label", "Play");
    buttons.play.title = "Play (space)";
  }

  function clear() {
    stop();
    offered = null;
    loading = null;
    replay = null;
    selected = null;
    drawn = new Map();
    cy?.destroy();
    cy = null;
    graph.replaceChildren();
    globalsList.replaceChildren();
    tracePane.replaceChildren();
    detail.textContent = "";
    body.hidden = true;
    panel.open = false;
    panel.hidden = true;
    count.textContent = "";
    setMessage("");
  }

  /* A finished run can be replayed; the traces are computed only when the panel opens. */
  function offer(run) {
    clear();
    offered = run;
    panel.hidden = false;
    count.textContent = "open to load";
  }

  async function load() {
    const run = offered;

    if (!run || loading || replay) {
      return;
    }

    setMessage("Solving the run again with its traces...");
    count.textContent = "loading";

    loading = (async () => {
      const answer = JSON.parse(
        await deps.solve({ ...run.configuration, trace: "jsonl" }, run.source),
      );

      if (typeof answer.trace !== "string" || answer.status !== "ok") {
        throw new Error(answer.message ?? "the analyzer returned no trace");
      }

      return { answer, events: parseEvents(answer.trace) };
    })();

    try {
      const { answer, events } = await loading;

      if (offered !== run) {
        return;
      }

      await build(answer, events);
      setMessage("");
      count.textContent = `${events.length} steps`;
    } catch (error) {
      if (offered === run) {
        const detailText = error instanceof Error ? error.message : String(error);

        setMessage(`The replay could not be loaded: ${detailText}`, {
          canRetry: true,
          kind: "error",
        });
        count.textContent = "";
      }
    } finally {
      if (offered === run) {
        loading = null;
      }
    }
  }

  async function build(answer, events) {
    const nodeOf = new Map();
    const keyOf = new Map();
    const pointOf = new Map();

    for (const node of answer.nodes ?? []) {
      const context = node.context.slice(node.context.indexOf(" / ") + 3);
      const key = `L:${node.point}|${context}`;

      nodeOf.set(key, node.id);
      keyOf.set(node.id, key);
      pointOf.set(node.id, node.point);
    }

    /* A seed is the entry of its procedure in its context; the analysis global has no node. */
    const entryOf = (key) => {
      const [procedure, context] = key.slice(2).split("|");

      return nodeOf.get(`L:entry_${procedure}|${context}`);
    };

    const snapshots = [];
    const blocks = [];
    const state = emptyState();

    events.forEach((event, index) => {
      if (index % SNAPSHOT_EVERY === 0) {
        snapshots.push(copyState(state));
      }

      apply(state, event);
      blocks.push(stepBlock(event, index, Math.max(0, state.stack.length - 1)));
    });

    const { cytoscape, elk } = await deps.getGraphLibraries();
    const elements = deps.graphElements(answer).map((element) => {
      if (element.group !== "nodes" || !pointOf.has(element.data.id)) {
        return element;
      }

      const point = pointOf.get(element.data.id);
      const box = deps.nodeBox([point, "x".repeat(VALUE_CHARS)]);

      return {
        ...element,
        data: { ...element.data, label: `${point}\n${UNREACHED}`, ...box },
        classes: "point r-unseen",
      };
    });
    const layout = await deps.layoutGraph(elk, elements);

    graph.replaceChildren();
    body.hidden = false;

    cy = cytoscape({
      container: graph,
      elements,
      style: [...deps.graphStyle(), ...replayStyle(deps.cssToken)],
      layout: { name: "preset" },
      minZoom: 0.1,
      maxZoom: 4,
      boxSelectionEnabled: false,
      autounselectify: true,
    });

    deps.applyGraphLayout(cy, layout);
    cy.fit(undefined, 24);

    /* A graph too large to read when fitted starts at the solve's root unknown instead. */
    const root = events[0]?.unknown && nodeOf.get(localKey(events[0].unknown));

    if (cy.zoom() < 0.5 && root) {
      cy.zoom(0.8);
      cy.center(cy.getElementById(root));
    }

    cy.on("dbltap", (event) => {
      if (event.target === cy) {
        cy.animate({ fit: { padding: 24 } }, { duration: 260 });
      }
    });
    cy.on("tap", "node.point", (event) => {
      selected = event.target.id();
      render();
    });

    const edgesBetween = new Map();

    cy.edges().forEach((edge) => {
      const key = `${edge.source().id()}>${edge.target().id()}`;

      edgesBetween.set(key, [...(edgesBetween.get(key) ?? []), edge]);
    });

    replay = {
      events,
      blocks,
      snapshots,
      nodeOf,
      keyOf,
      pointOf,
      entryOf,
      edgesBetween,
      step: 0,
      state: copyState(snapshots[0] ?? emptyState()),
      stateStep: 0,
    };

    slider.max = String(events.length);
    render();
  }

  /* The solver state after [step] events, from the nearest snapshot at or before it. */
  function stateAt(step) {
    if (step < replay.stateStep || step - replay.stateStep > SNAPSHOT_EVERY) {
      const base = Math.floor(step / SNAPSHOT_EVERY);

      replay.state = copyState(replay.snapshots[Math.min(base, replay.snapshots.length - 1)]);
      replay.stateStep = Math.min(base, replay.snapshots.length - 1) * SNAPSHOT_EVERY;
    }

    while (replay.stateStep < step) {
      apply(replay.state, replay.events[replay.stateStep]);
      replay.stateStep++;
    }

    return replay.state;
  }

  function status(state, key, finished) {
    if (!finished && state.stack.at(-1) === key) {
      return "r-current";
    }

    if (!finished && state.stack.includes(key)) {
      return "r-solving";
    }

    if (state.stable.has(key)) {
      return "r-stable";
    }

    return state.seen.has(key) ? "r-seen" : "r-unseen";
  }

  /* The graph elements an event touches: edges a value flows along, and its target node. */
  function touched(event) {
    const edges = [];
    const nodes = [];
    const along = (from, to) => {
      const source = replay.nodeOf.get(from);
      const target = replay.nodeOf.get(to);

      edges.push(...(replay.edgesBetween.get(`${source}>${target}`) ?? []));
    };

    switch (event?.event) {
      case "query_local":
      case "value_local":
        along(localKey(event.target), localKey(event.current));
        nodes.push(replay.nodeOf.get(localKey(event.target)));
        break;
      case "route": {
        const call = replay.nodeOf.get(localKey(event.call));
        const context = contextLabel(event.context);

        cy.getElementById(call)
          .outgoers("edge.enter")
          .forEach((edge) => {
            if (replay.keyOf.get(edge.target().id())?.endsWith(`|${context}`)) {
              edges.push(edge);
            }
          });
        break;
      }
      case "query_global":
      case "side":
        nodes.push(replay.entryOf(globalKey(event.target)));
        break;
      case "update_global":
        nodes.push(replay.entryOf(globalKey(event.unknown)));
        break;
      default:
        break;
    }

    return { edges, nodes: nodes.filter(Boolean) };
  }

  function eventGlobal(event) {
    const unknown = event?.event === "update_global" ? event.unknown : event?.target;

    return unknown && unknown.kind !== "local" ? globalKey(unknown) : null;
  }

  function renderGraph(state, event, finished) {
    const changed = event?.event === "update_local" ? localKey(event.unknown) : null;
    const { edges, nodes } = touched(event);

    cy.batch(() => {
      cy.nodes(".point").forEach((node) => {
        const key = replay.keyOf.get(node.id());
        const seen = state.seen.has(key);
        const value = seen ? shortValue(state.values.get(key) ?? "⊥") : UNREACHED;
        const classes = [
          "point",
          status(state, key, finished),
          seen && state.destabilized.has(key) && !state.stable.has(key) ? "r-destabilized" : "",
          key === changed ? "r-changed" : "",
          nodes.includes(node.id()) ? "r-target" : "",
          node.id() === selected ? "graph-node-selected" : "",
        ]
          .filter(Boolean)
          .join(" ");
        const label = `${replay.pointOf.get(node.id())}\n${value}`;
        const last = drawn.get(node.id());

        if (!last || last.classes !== classes || last.label !== label) {
          node.classes(classes);
          node.data("label", label);
          drawn.set(node.id(), { classes, label });
        }
      });

      cy.edges(".r-active").removeClass("r-active");

      for (const edge of edges) {
        edge.addClass("r-active");
      }
    });

    const current = finished ? null : replay.nodeOf.get(state.stack.at(-1));

    /* The view follows the unknown being solved once it leaves the view. */
    if (current) {
      const node = cy.getElementById(current);
      const view = cy.extent();
      const { x, y } = node.position();

      if (x < view.x1 || x > view.x2 || y < view.y1 || y > view.y2) {
        cy.stop(true, true);
        cy.animate({ center: { eles: node } }, { duration: playing ? 0 : 200 });
      }
    }
  }

  function renderGlobals(state, event) {
    const active = eventGlobal(event);
    const rows = [...state.globals].map(([key, value]) => {
      const row = document.createElement("li");
      const name = document.createElement("code");
      const text = document.createElement("span");

      row.className =
        key === active ? "solver-global replay-global is-active" : "solver-global replay-global";
      name.className = "solver-global-key";
      name.textContent = globalName(key);
      text.textContent = value;
      row.append(name, text);

      return row;
    });

    if (rows.length === 0) {
      const empty = document.createElement("li");

      empty.className = "solver-globals-note";
      empty.textContent = "No global unknown reached yet.";
      rows.push(empty);
    }

    globalsList.replaceChildren(...rows);
  }

  function renderTrace(step) {
    const { events, blocks } = replay;
    const from = Math.max(0, step - 1 - TRACE_WINDOW);
    const to = Math.min(events.length, step + TRACE_WINDOW);
    const lines = [];
    let current = null;

    for (let index = from; index < to; index++) {
      const line = document.createElement("button");

      line.type = "button";
      line.className = "replay-line";
      line.dataset.step = String(index + 1);
      line.textContent = blocks[index];

      if (index === step - 1) {
        line.classList.add("is-current");
        line.setAttribute("aria-current", "step");
        current = line;
      }

      lines.push(line);
    }

    tracePane.replaceChildren(...lines);

    if (current) {
      tracePane.scrollTop =
        current.offsetTop - tracePane.clientHeight / 2 + current.clientHeight / 2;
    } else {
      tracePane.scrollTop = 0;
    }
  }

  function renderDetail(state) {
    if (!selected) {
      detail.textContent = "Click a node to read its whole value.";
      return;
    }

    const key = replay.keyOf.get(selected);
    const [point, context] = key.slice(2).split("|");
    const value = state.seen.has(key) ? (state.values.get(key) ?? "⊥") : UNREACHED;

    detail.textContent = `(${point}, ${context}) = ${value}`;
  }

  function render() {
    if (!replay) {
      return;
    }

    const { step, events } = replay;
    const finished = step === events.length;
    const state = stateAt(step);
    const event = step > 0 ? events[step - 1] : null;

    renderGraph(state, event, finished);
    renderGlobals(state, event);
    renderTrace(step);
    renderDetail(state);

    slider.value = String(step);
    stepLabel.textContent = `Step ${step} of ${events.length}${finished ? " · solved" : ""}`;
    buttons.start.disabled = buttons.back.disabled = step === 0;
    buttons.end.disabled = buttons.forward.disabled = finished;
  }

  function go(step) {
    if (!replay) {
      return;
    }

    replay.step = Math.max(0, Math.min(replay.events.length, step));
    render();
  }

  function play() {
    if (!replay) {
      return;
    }

    if (playing) {
      stop();
      return;
    }

    if (replay.step === replay.events.length) {
      go(0);
    }

    let last = performance.now();
    let owed = 0;

    buttons.play.querySelector("i").className = "fa-solid fa-pause";
    buttons.play.setAttribute("aria-label", "Pause");
    buttons.play.title = "Pause (space)";

    const tick = (time) => {
      owed += ((time - last) / 1000) * Number(speed.value);
      last = time;

      const steps = Math.floor(owed);

      if (steps > 0) {
        owed -= steps;
        go(replay.step + steps);
      }

      if (replay.step >= replay.events.length) {
        stop();
        return;
      }

      playing = requestAnimationFrame(tick);
    };

    playing = requestAnimationFrame(tick);
  }

  panel.addEventListener("toggle", () => {
    if (panel.open) {
      load();
      cy?.resize();
    } else {
      stop();
    }
  });

  retry.addEventListener("click", load);
  buttons.start.addEventListener("click", () => go(0));
  buttons.back.addEventListener("click", () => go(replay.step - 1));
  buttons.forward.addEventListener("click", () => go(replay.step + 1));
  buttons.end.addEventListener("click", () => go(replay.events.length));
  buttons.play.addEventListener("click", play);
  slider.addEventListener("input", () => go(Number(slider.value)));

  tracePane.addEventListener("click", (event) => {
    const line = event.target.closest(".replay-line");

    if (line) {
      stop();
      go(Number(line.dataset.step));
    }
  });

  /* Arrow keys step, space plays, Home and End jump, anywhere in the panel but the slider. */
  body.addEventListener("keydown", (event) => {
    if (!replay || event.target === slider || event.target === speed) {
      return;
    }

    const keys = {
      ArrowLeft: () => go(replay.step - 1),
      ArrowRight: () => go(replay.step + 1),
      Home: () => go(0),
      End: () => go(replay.events.length),
      " ": play,
    };

    if (keys[event.key]) {
      event.preventDefault();
      keys[event.key]();
    }
  });

  return { offer, clear };
}

/* The four states, the current unknown and the step's edges, on top of the CFG's own style. */
function replayStyle(cssToken) {
  return [
    /* A step replaces the previous step's marks at once; a fade would blend the two. */
    { selector: "node.point", style: { "transition-duration": 0 } },
    {
      selector: "node.point.r-unseen",
      style: {
        "border-style": "dashed",
        "border-width": 1,
        "border-color": cssToken("--text-faint"),
        "background-color": cssToken("--surface-muted"),
        color: cssToken("--text-faint"),
      },
    },
    {
      selector: "node.point.r-seen",
      style: {
        "border-width": 1,
        "border-color": cssToken("--border-strong"),
        "background-color": cssToken("--surface"),
      },
    },
    {
      selector: "node.point.r-stable",
      style: {
        "border-width": 2,
        "border-color": cssToken("--primary"),
        "background-color": cssToken("--primary-soft"),
      },
    },
    {
      selector: "node.point.r-solving",
      style: {
        "border-width": 2,
        "border-color": cssToken("--accent"),
        "background-color": cssToken("--accent-soft"),
      },
    },
    {
      selector: "node.point.r-current",
      style: {
        "border-width": 4,
        "border-color": cssToken("--accent"),
        "background-color": cssToken("--accent-soft"),
        "underlay-opacity": 0.25,
      },
    },
    {
      selector: "node.point.r-destabilized",
      style: { "border-style": "dotted", "border-width": 2 },
    },
    {
      selector: "node.point.r-target",
      style: { "outline-color": cssToken("--primary"), "outline-width": 3, "outline-offset": 3 },
    },
    {
      selector: "node.point.r-changed",
      style: { "underlay-color": cssToken("--success"), "underlay-opacity": 0.35 },
    },
    {
      selector: "edge.r-active",
      style: {
        width: 4,
        "line-style": "solid",
        "line-color": cssToken("--accent"),
        "target-arrow-color": cssToken("--accent"),
        "z-index": 10,
      },
    },
  ];
}
