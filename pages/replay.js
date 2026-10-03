/*
 * Solve replay: steps through a run's solve on its control-flow graph.
 *
 * The replay reads the JSON Lines trace (schema 2) of the shown run: the events the
 * exported solver reports through its traced code equations. Every state it shows comes
 * from pages/replay_state.js's reducer, folded over those events: values, the stack of
 * open queries, the stable set, widening points, influence edges, destabilization
 * cascades, globals with their contributions, routes and counters. Nothing here
 * reconstructs history on its own.
 *
 * The trace is an unverified observation of the verified computation, and this replay
 * an unverified visualization of the trace. Nothing here feeds back into the result on
 * the page.
 */

import { contextLabel, createCache, globalKey, localKey, parseEvents } from "./replay_state.js";
import { replayStyle } from "./replay-style.js";
import { createTraceView } from "./trace-view.js";

/* Replay states kept for jumps: stepping back or dragging the slider replays at most this many events. */
const SNAPSHOT_EVERY = 256;
/* Characters of a value shown inside a node; the node itself sizes for this many. */
const VALUE_CHARS = 30;

const UNREACHED = "not reached";

function query(selector) {
  const element = document.querySelector(selector);

  if (!element) {
    throw new Error(`Missing page element ${selector}`);
  }

  return element;
}

/* A global unknown as the page's seed list names it. */
function globalName(key) {
  if (key === "G:Global") {
    return "Global";
  }

  const [procedure, context] = key.slice(2).split("|");

  return `enter ${procedure} @ ${context}`;
}

/* A node's value in one line: what it says beyond ⊤, cut to the node's width. */
function shortValue(value) {
  const said = compactValue(value);

  return said.length > VALUE_CHARS ? `${said.slice(0, VALUE_CHARS - 1)}…` : said;
}

/*
 * A value in one line without its ⊤ components or analysis names: only what it says.
 * A value that says nothing beyond ⊤ is ⊤.
 */
/* A product domain's binding alone can be as wide as a box; the tooltip has it all. */
const SEED_LABEL_MAX = 40;

/* A seed's bindings in one line of at most SEED_LABEL_MAX characters, cut at a binding where one fits. */
export function seedLabelOf(bindings) {
  let label = "";

  for (const binding of bindings) {
    const longer = label ? `${label}, ${binding}` : binding;

    if (longer.length > SEED_LABEL_MAX) {
      return label ? `${label}, \u2026` : `${binding.slice(0, SEED_LABEL_MAX - 1)}\u2026`;
    }

    label = longer;
  }

  return label || "\u22a4";
}

function compactValue(value) {
  if (value === "⊥") {
    return "⊥";
  }

  const said = value
    .split("; ")
    .flatMap((section) => section.replace(/^[^:=]+: /, "").split(", "))
    .filter((part) => part !== "⊤" && !part.endsWith("=⊤"));

  return said.length > 0 ? said.join(", ") : "⊤";
}

/* --------------------------------------------------------------------- view */

export function createSolveReplay(deps) {
  const panel = query("#solve-replay");
  const count = query("#solve-replay-count");
  const message = query("#solve-replay-message");
  const retry = query("#solve-replay-load");
  const body = query("#solve-replay-body");
  const graph = query("#solve-replay-graph");
  /* Clicking a line goes to the step whose block it belongs to. */
  const trace = createTraceView(query("#solve-replay-trace"), {
    label: "Trace of the solve. Click a line to go to its step.",
    onLine: (line) => {
      if (replay) {
        stop();
        go(stepOfLine(line));
      }
    },
  });
  /* The full state of the hovered node, kept current while the replay plays. */
  const tooltip = document.createElement("div");

  tooltip.className = "graph-tooltip";
  tooltip.hidden = true;
  document.body.append(tooltip);
  const stackList = query("#solve-replay-stack");
  const routesList = query("#solve-replay-routes");
  const countersBody = query("#solve-replay-counters");
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
  let hovered = null;
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
    hovered = null;
    tooltip.hidden = true;
    drawn = new Map();
    cy?.destroy();
    cy = null;
    graph.replaceChildren();
    trace.setText("");
    body.hidden = true;
    panel.open = false;
    panel.hidden = true;
    count.textContent = "";
    setMessage("");
  }

  /* A finished run is replayed from the traces it recorded; it is laid out when the panel opens. */
  function offer(run) {
    clear();
    offered = run;
    panel.hidden = false;

    const steps = run.answer.trace_jsonl?.match(/^\{"step":/gm)?.length ?? 0;

    count.textContent = `${steps.toLocaleString("en")} steps`;
  }

  async function load() {
    const run = offered;

    if (!run || loading || replay) {
      return;
    }

    const { answer } = run;

    if (typeof answer.trace_jsonl !== "string" || typeof answer.trace !== "string") {
      setMessage("The run returned no trace to replay.", { kind: "error" });
      return;
    }

    setMessage("Laying out the replay...");
    loading = true;

    try {
      const events = parseEvents(answer.trace_jsonl).filter((record) =>
        Number.isInteger(record.step),
      );

      /* The verbose text the steps' lines point into: the trace panel's full form. */
      await build(answer, events, answer.trace);

      if (offered !== run) {
        return;
      }

      setMessage(
        answer.trace.includes("\nTrace truncated:")
          ? "The run's trace was cut short, so the replay stops where the recording did."
          : "",
      );
    } catch (error) {
      if (offered === run) {
        const detailText = error instanceof Error ? error.message : String(error);

        setMessage(`The replay could not be loaded: ${detailText}`, {
          canRetry: true,
          kind: "error",
        });
      }
    } finally {
      if (offered === run) {
        loading = null;
      }
    }
  }

  async function build(answer, events, text) {
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

    /* A seed's node stands beside its procedure's entry in its context. */
    const entryOf = (key) => {
      if (key === "G:Global") {
        return keyOf.has(deps.globalId) ? deps.globalId : undefined;
      }

      const [procedure, context] = key.slice(2).split("|");
      const entry = nodeOf.get(`L:entry_${procedure}|${context}`);

      return entry && deps.seedId(entry);
    };

    for (const node of answer.nodes ?? []) {
      if (node.point.startsWith("entry_")) {
        const context = node.context.slice(node.context.indexOf(" / ") + 3);

        keyOf.set(deps.seedId(node.id), `G:${node.point.slice(6)}|${context}`);
      }
    }

    if ((answer.shared?.globals ?? []).length > 0) {
      keyOf.set(deps.globalId, "G:Global");
    }

    const cache = createCache(events, SNAPSHOT_EVERY);

    const { cytoscape, elk } = await deps.getGraphLibraries();
    const elements = deps.graphElements(answer).map((element) => {
      if (element.classes?.startsWith("seed ") || element.classes === "seed") {
        return { ...element, data: { ...element.data, label: "" }, classes: "seed r-unseen" };
      }

      if (element.classes?.startsWith("global ") || element.classes === "global") {
        return {
          ...element,
          data: { ...element.data, label: "Global" },
          classes: "global r-unseen",
        };
      }

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

    /*
     * Cytoscape draws node labels from textures it caches by text and style and
     * reuses without checking their size. Here labels change at every step, the cache
     * buys nothing, and a reused texture drew labels squashed; labels are drawn
     * directly instead. This reaches into the renderer's private state.
     */
    const labelCache = cy.renderer()?.data?.lblTxrCache;

    if (labelCache) {
      labelCache.getElement = () => null;
    }

    deps.applyGraphLayout(cy, layout);
    deps.followRoutesOnDrag(cy);
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
    cy.on("mouseover", "node.point, node.seed, node.global", (event) => {
      hovered = event.target.id();
      renderTooltip(replay.cache.stateAt(replay.step));
      placeTooltip(event.originalEvent);
    });
    cy.on("mousemove", "node.point, node.seed, node.global", (event) =>
      placeTooltip(event.originalEvent),
    );
    cy.on("mouseout", "node.point, node.seed, node.global", hideTooltip);

    const edgesBetween = new Map();

    cy.edges().forEach((edge) => {
      const key = `${edge.source().id()}>${edge.target().id()}`;

      edgesBetween.set(key, [...(edgesBetween.get(key) ?? []), edge]);
    });

    replay = {
      events,
      lines: events.map((event) => event.line),
      cache,
      nodeOf,
      keyOf,
      pointOf,
      entryOf,
      edgesBetween,
      step: 0,
    };

    trace.setText(text);

    slider.max = String(events.length);
    render();
  }

  /* The four states: unseen, evaluated, solving (on the stack), stable; stable marking is a toggle. */
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

    return state.evaluated.has(key) ? "r-seen" : "r-unseen";
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

  function renderGraph(state, event, finished) {
    const changed = event?.event === "update_local" ? localKey(event.unknown) : null;
    const cascade = state.cascade;
    const { edges, nodes } = touched(event);

    cy.batch(() => {
      cy.nodes(".point").forEach((node) => {
        const key = replay.keyOf.get(node.id());
        const seen = state.reached.has(key);
        const value = seen ? shortValue(state.values.get(key) ?? "⊥") : UNREACHED;
        const classes = [
          "point",
          status(state, key, finished),
          cascade.has(key) ? "r-destabilized" : "",
          state.wpoints.has(key) ? "r-wpoint" : "",
          state.widened === key ? "r-widened" : "",
          key === changed ? "r-changed" : "",
          nodes.includes(node.id()) ? "r-target" : "",
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

      cy.nodes(".seed, .global").forEach((node) => {
        const key = replay.keyOf.get(node.id());
        const g = state.globals.get(key);
        const shape = node.hasClass("global") ? "global" : "seed";
        const classes = [
          shape,
          !g ? "r-unseen" : g.value === "⊥" ? "r-seen" : "r-seed-set",
          event?.event === "update_global" && globalKey(event.unknown) === key ? "r-changed" : "",
          nodes.includes(node.id()) ? "r-target" : "",
        ]
          .filter(Boolean)
          .join(" ");

        const value = !g
          ? ""
          : g.value === "⊥"
            ? "⊥"
            : seedLabelOf(compactValue(g.value).split(", "));
        const label = shape === "global" ? `Global  ${value}`.trim() : value;
        const last = drawn.get(node.id());

        if (last?.classes !== classes || last?.label !== label) {
          node.classes(classes);
          node.data("label", label);
          drawn.set(node.id(), { classes, label });
        }
      });

      cy.edges(".r-active").removeClass("r-active");

      for (const edge of edges) {
        edge.addClass("r-active");
      }

      drawInfluence(state);
      drawEventEdges(state);
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

  /* Influence edges, reader to read unknown, as an overlay of their own; rebuilt per step. */
  function drawInfluence(state) {
    cy.remove("edge.r-infl");

    const edges = [];

    for (const [read, readers] of state.infl) {
      const target = read.startsWith("L:") ? replay.nodeOf.get(read) : replay.entryOf(read);

      for (const reader of readers) {
        const source = replay.nodeOf.get(reader);

        if (source && target) {
          edges.push({
            group: "edges",
            data: { id: `infl:${reader}>${read}`, source, target },
            classes: "r-infl",
          });
        }
      }
    }

    cy.add(edges);
  }

  /* Transient arrows only for the event being replayed, never from final values or CFG guesses. */
  function drawEventEdges(state) {
    cy.remove("edge.r-event");
    const nodeFor = (key) => (key.startsWith("L:") ? replay.nodeOf.get(key) : replay.entryOf(key));
    const edges = [];

    for (const [index, { from, to, kind }] of state.eventEdges.entries()) {
      const source = nodeFor(from);
      const target = nodeFor(to);

      if (source && target) {
        edges.push({
          group: "edges",
          data: { id: `event:${index}`, source, target, label: kind },
          classes: "r-event r-active",
        });
      }
    }

    cy.add(edges);
  }

  /* The stack of open queries, innermost first; always shown. */
  function renderStack(state, finished) {
    const rows = (finished ? [] : [...state.stack].reverse()).map((key, index) => {
      const row = document.createElement("li");
      const [point, context] = key.slice(2).split("|");

      row.className = index === 0 ? "replay-stack-entry is-active" : "replay-stack-entry";
      row.textContent = `(${point}, ${context})`;

      return row;
    });

    stackList.replaceChildren(...rows);
  }

  function counterRows(state) {
    const keys = new Set([
      ...state.counters.evaluations.keys(),
      ...state.counters.updates.keys(),
      ...state.counters.destabilizations.keys(),
    ]);
    const { evaluations, updates } = state.counters;
    const naturally = new Intl.Collator(undefined, { numeric: true });

    /* The busiest unknowns first: most evaluations, then most updates, then by name. */
    const busiest = [...keys].sort(
      (a, b) =>
        (evaluations.get(b) ?? 0) - (evaluations.get(a) ?? 0) ||
        (updates.get(b) ?? 0) - (updates.get(a) ?? 0) ||
        naturally.compare(a, b),
    );
    const rows = busiest.map((key) => {
      const row = document.createElement("tr");
      const cells = [
        key.startsWith("L:") ? `(${key.slice(2).replace("|", ", ")})` : globalName(key),
        state.counters.evaluations.get(key) ?? 0,
        state.counters.updates.get(key) ?? 0,
        state.counters.destabilizations.get(key) ?? 0,
      ];

      row.replaceChildren(
        ...cells.map((value, index) => {
          const cell = document.createElement("td");

          cell.textContent = String(value);

          if (index === 0) {
            cell.title = String(value);
          }

          return cell;
        }),
      );

      return row;
    });

    countersBody.replaceChildren(...rows);
  }

  function renderRoutes(state) {
    routesList.replaceChildren(
      ...state.routes.map(({ call, context, entry }) => {
        const row = document.createElement("li");
        const head = document.createElement("span");
        const detailText = document.createElement("span");
        const [point, callContext] = call.slice(2).split("|");

        head.className = "replay-route";
        head.textContent = `${point} (${callContext}) → context ${context}`;
        detailText.className = "replay-global-detail";
        detailText.textContent = `entry ${compactValue(entry)}`;
        row.append(head, detailText);
        return row;
      }),
    );
  }

  /* The verbose text is set once per load; a step only moves the current line. */
  function renderTrace(step) {
    trace.show(step === 0 ? null : replay.lines[step - 1]);
  }

  /* The first step printed on the last event line at or before [line]; 0 above them. */
  function stepOfLine(line) {
    const { lines } = replay;
    let low = 0;
    let high = lines.length;

    while (low < high) {
      const middle = (low + high) >> 1;

      if (lines[middle] <= line) {
        low = middle + 1;
      } else {
        high = middle;
      }
    }

    if (low === 0) {
      return 0;
    }

    const at = lines[low - 1];
    let first = low - 1;

    while (first > 0 && lines[first - 1] === at) {
      first--;
    }

    return first + 1;
  }

  function hideTooltip() {
    hovered = null;
    tooltip.hidden = true;
  }

  function renderTooltip(state) {
    if (!hovered) {
      return;
    }

    const key = replay.keyOf.get(hovered);

    if (key.startsWith("G:")) {
      renderSeedTooltip(state, key);
      return;
    }

    const [point, context] = key.slice(2).split("|");
    const readers = [...(state.infl.get(key) ?? [])].map((reader) =>
      reader.slice(2).replace("|", " @ "),
    );
    const title = document.createElement("strong");
    const body = document.createElement("pre");

    title.textContent = `(${point}, ${context})`;
    body.textContent = [
      state.reached.has(key) ? (state.values.get(key) ?? "⊥") : UNREACHED,
      "",
      state.stable.has(key) ? "stable" : "not stable",
      ...(state.wpoints.has(key) ? ["widening point"] : []),
      `${state.counters.evaluations.get(key) ?? 0} evaluation(s)`,
      `read by ${readers.join(", ") || "nothing"}`,
    ].join("\n");
    tooltip.replaceChildren(title, body);
    tooltip.hidden = false;
  }

  /* A seed's value, its last change, and the side effects joined into it so far. */
  function renderSeedTooltip(state, key) {
    const g = state.globals.get(key);
    const title = document.createElement("strong");
    const body = document.createElement("pre");
    const from = (contribution) => contribution.from.slice(2).replace("|", " @ ");

    title.textContent = globalName(key);
    body.textContent = !g
      ? "not reached"
      : [
          g.value,
          "",
          g.last ? `last change ${g.last.old} → ${g.last.new}` : "unchanged",
          `${g.contributions.length} side effect(s)`,
          ...g.contributions.map((c) => `  from ${from(c)}: ${c.value}`),
        ].join("\n");
    tooltip.replaceChildren(title, body);
    tooltip.hidden = false;
  }

  function placeTooltip(event) {
    const margin = 14;
    const { width, height } = tooltip.getBoundingClientRect();
    const left =
      event.clientX + margin + width > window.innerWidth
        ? event.clientX - margin - width
        : event.clientX + margin;
    const top =
      event.clientY + margin + height > window.innerHeight
        ? event.clientY - margin - height
        : event.clientY + margin;

    tooltip.style.left = `${Math.max(4, left)}px`;
    tooltip.style.top = `${Math.max(4, top)}px`;
  }

  function render() {
    if (!replay) {
      return;
    }

    const { step, events } = replay;
    const finished = step === events.length;
    const state = replay.cache.stateAt(step);
    const event = step > 0 ? events[step - 1] : null;

    renderGraph(state, event, finished);
    renderStack(state, finished);
    renderRoutes(state);
    counterRows(state);

    renderTrace(step);
    renderTooltip(state);

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
  /* Cytoscape reports no mouseout when the pointer leaves the graph from a node. */
  graph.addEventListener("mouseleave", hideTooltip);

  buttons.start.addEventListener("click", () => go(0));
  buttons.back.addEventListener("click", () => go(replay.step - 1));
  buttons.forward.addEventListener("click", () => go(replay.step + 1));
  buttons.end.addEventListener("click", () => go(replay.events.length));
  buttons.play.addEventListener("click", play);
  slider.addEventListener("input", () => go(Number(slider.value)));

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
