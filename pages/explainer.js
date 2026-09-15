/*
 * Scenes animate by default and pause only once known to be offscreen, so a failed
 * or missing script leaves the page moving rather than frozen on a first frame.
 */
"use strict";

/* Renders prose whose code fragments are marked with backticks. */
function withCode(text) {
  const escape = (part) => part.replace(/[&<>]/g, (ch) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" })[ch]);

  return text
    .split("`")
    .map((part, i) => (i % 2 === 1 ? `<code>${escape(part)}</code>` : escape(part)))
    .join("");
}

/* The home page used to hold the analyzer and these sections; old links still land. */
const movedAnchors = {
  "#analyzer": "playground.html",
  "#soundness": "#theorems",
  "#reports": "#reading",
};

if (movedAnchors[location.hash]) {
  const target = movedAnchors[location.hash];

  if (target.startsWith("#")) {
    history.replaceState(null, "", target);
    document.querySelector(target)?.scrollIntoView();
  } else {
    location.replace(target);
  }
}

const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;

if ("IntersectionObserver" in window) {
  const observer = new IntersectionObserver((entries) => {
    for (const entry of entries) {
      entry.target.classList.toggle("is-offscreen", !entry.isIntersecting);
    }
  });

  for (const scene of document.querySelectorAll(".scene")) {
    observer.observe(scene);
  }
}

/*
 * The loop stepper. The markup ships the final step, so without script the figure
 * still shows the proved check; with it, the steps play and the chips jump.
 */
for (const figure of document.querySelectorAll(".scene-loop")) {
  const steps = Number(figure.dataset.steps);
  const chips = figure.querySelectorAll("[data-goto]");
  const toggle = figure.querySelector(".loop-play");
  const icon = toggle.querySelector("i");
  let step = 0;
  let timer = null;

  const show = (next) => {
    step = (next + steps) % steps;
    figure.dataset.step = String(step);

    for (const chip of chips) {
      chip.setAttribute("aria-pressed", String(Number(chip.dataset.goto) === step));
    }
  };

  const setPlaying = (playing) => {
    clearInterval(timer);
    timer = playing
      ? setInterval(() => {
          if (!figure.classList.contains("is-offscreen")) {
            show(step + 1);
          }
        }, 2200)
      : null;

    icon.className = playing ? "fa-solid fa-pause" : "fa-solid fa-play";
    toggle.setAttribute("aria-label", playing ? "Pause" : "Play");
  };

  for (const chip of chips) {
    chip.addEventListener("click", () => {
      setPlaying(false);
      show(Number(chip.dataset.goto));
    });
  }

  toggle.addEventListener("click", () => setPlaying(timer === null));

  figure.querySelector(".loop-controls").hidden = false;
  show(0);
  setPlaying(!reducedMotion);
}

/*
 * The theorem explorer. A tab picks the theorem; hovering or focusing one of its
 * premises or conclusions lights the graph elements whose data-refs name it.
 */
for (const figure of document.querySelectorAll(".scene-theorems")) {
  const svg = figure.querySelector(".cfg-svg");

  const highlight = (ref) => {
    for (const element of svg.querySelectorAll(".is-hl")) {
      element.classList.remove("is-hl");
    }

    svg.classList.toggle("has-hl", ref !== null);

    if (ref !== null) {
      for (const element of svg.querySelectorAll(`[data-refs~="${ref}"]`)) {
        element.classList.add("is-hl");
      }
    }
  };

  for (const item of figure.querySelectorAll(".rule-item[data-ref]")) {
    const panel = item.closest(".thm-panel");
    const explain = () => renderRuleExplanation(panel, item.dataset.ref);

    item.addEventListener("pointerenter", () => { highlight(item.dataset.ref); explain(); });
    item.addEventListener("focus", () => { highlight(item.dataset.ref); explain(); });
    item.addEventListener("pointerleave", () => highlight(null));
    item.addEventListener("blur", () => highlight(null));
  }
}


/*
 * What each premise and conclusion says, with the formal clause and the definition it
 * rests on. The panel keeps the last item shown, so its link stays reachable.
 */
const ISA = "Voblint";
const isaConst = (session, theory, name) => `${ISA}/${session}/${theory}.html#${theory}.${name}%7Cconst`;

const RULE_EXPLANATIONS = {
  run: {
    clause: "s0 ∈ cinit_stores (declared_global p)  ∧  star (pstep …) (main_body …, s0, []) (residual, s, frs)",
    text: "Start from an initial store (declared globals are `0`, locals arbitrary) with an empty call stack, and let the source semantics take any number of steps. It arrives at the rest of the program `residual`, the store `s` and the call frames `frs`. The run may stop anywhere, even inside a call.",
    link: isaConst("Voblint_VIMP", "VIMP_Proc", "pstep"), linkText: "pstep",
  },
  term: {
    clause: "config_terminates D rule ctx p",
    text: "The verified solver, instantiated for this domain `D`, globals rule and context policy, terminates on this program. HOL functions are total, so without this premise the answer could be an unspecified value that no execution computes. It is checked by running the analysis, never proved in general.",
    link: isaConst("Voblint_CLI", "Analysis_Certified", "config_terminates"), linkText: "config_terminates",
  },
  ans: {
    clause: "run_voblint D rule ctx p = Analysed res",
    text: "The exported analyzer, the function the playground calls, accepted the program as well-formed and returned the result `res`. Its checks and diagnostics are exactly what the page draws.",
    link: isaConst("Voblint_CLI", "Analysis_Run", "run_voblint"), linkText: "run_voblint",
  },
  v: {
    clause: "∃v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)",
    text: "The compiler's simulation relation matches the source state to a node `v` of the compiled graph, with the same store `s` and a matching stack `stk`. This is the forward simulation proved for the compiler.",
    link: isaConst("Voblint_Compile", "Simulation_Relation", "csim"), linkText: "csim",
  },
  coll: {
    clause: "s ∈ ltr_collect (declared_global p) (prog_cfg p) (cinit_stores …) v",
    text: "The graph's collecting semantics reaches node `v` with store `s`: some valid activation-local trace from an initial store ends there. Every analysis result is judged against this set.",
    link: isaConst("Voblint_CFG", "LTR_Collect", "ltr_collect"), linkText: "ltr_collect",
  },
  coll2: {
    clause: "s ∈ ltr_collect (declared_global p) (prog_cfg p) (cinit_stores …) v",
    text: "The graph's collecting semantics reaches node `v` with store `s`. Here it is a premise: the theorem speaks about every store the program can really have at `v`.",
    link: isaConst("Voblint_CFG", "LTR_Collect", "ltr_collect"), linkText: "ltr_collect",
  },
  cover: {
    clause: "analysis_result_covers D rule ctx p v s",
    text: "In the table this configuration built, some context solved at `v` holds an abstract state whose concretization contains `s`. Not every context has to: another activation's entry need not describe this store.",
    link: isaConst("Voblint_CLI", "Analysis_Certified", "analysis_result_covers"), linkText: "analysis_result_covers",
  },
  checks: {
    clause: "checks_sound_at res v s",
    text: "For every check the result lists at `v`: its verdict is not DEAD, `PROVED` implies its condition is true in `s`, and `REFUTED` implies it is false in `s`. `UNKNOWN` claims nothing.",
    link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "checks_sound_at"), linkText: "checks_sound_at",
  },
  next: {
    clause: "next_check residual = Some e",
    text: "The next command the source program will execute is `__voblint_check(e)`.",
    link: isaConst("Voblint_Compile", "Residual_Edges", "next_check"), linkText: "next_check",
  },
  listed: {
    clause: "∃c ∈ set (res_checks res). check_exp c = e ∧ s ∈ ltr_collect … (check_point c)",
    text: "The result lists a check `c` with condition `e`, at a node the store `s` really reaches. The node is found, not assumed: two identical procedure bodies list their checks separately.",
    link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "check_sites"), linkText: "check_sites",
  },
  holds: {
    clause: "(check_verdict c = Decided Check_Proved ⟶ truthy (aval e s)) ∧ (… Check_Refuted ⟶ ¬ truthy (aval e s))",
    text: "Evaluating `e` in the store `s` agrees with the verdict: true for `PROVED`, false for `REFUTED`.",
    link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "checks_sound_at"), linkText: "checks_sound_at",
  },
  listed2: {
    clause: "chk ∈ set (res_checks res)",
    text: "`chk` is one of the checks the result lists.",
    link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "check_sites"), linkText: "check_sites",
  },
  deadv: {
    clause: "check_verdict chk = Dead",
    text: "The result marks that check DEAD: no context solved at its node has a live state.",
    link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "checks_sound_at"), linkText: "checks_sound_at",
  },
  empty: {
    clause: "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores …) (check_point chk) = {}",
    text: "The collecting semantics has no store at the check's node: no run, from any initial store, ever gets there.",
    link: isaConst("Voblint_CFG", "LTR_Collect", "ltr_collect"), linkText: "ltr_collect",
  },
  nodiag: {
    clause: "∀d ∈ set (res_diagnostics res). diagnostic_point d ≠ v",
    text: "The result lists no arithmetic diagnostic, neither a warning nor an error, at node `v`.",
    link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "arithmetic_safe_at"), linkText: "arithmetic_safe_at",
  },
  div: {
    clause: "arithmetic_safe_at (prog_cfg p) v s",
    text: "For every arithmetic expression on the graph's edges at `v`, every divisor evaluates to a non-zero value in `s`. The corollary `run_voblint_arithmetic_intra_safe` states it for one edge at a time.",
    link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "arithmetic_safe_at"), linkText: "arithmetic_safe_at",
  },
  sites: {
    clause: "map (λchk. (check_point chk, check_exp chk)) (res_checks res) = check_sites (prog_cfg p)",
    text: "Read as (node, condition) pairs, the result's checks are exactly the check edges of the compiled graph, in the graph's edge order. Nothing is dropped or invented; pairing them with source lines happens outside the proof.",
    link: isaConst("Voblint_CLI", "Analysis_Run_Sound", "check_sites"), linkText: "check_sites",
  },
};

function renderRuleExplanation(panel, ref) {
  const entry = RULE_EXPLANATIONS[ref];
  const target = panel.querySelector(".rule-explain");

  if (!entry || !target) {
    return;
  }

  const clause = document.createElement("pre");
  clause.className = "rule-clause";
  clause.innerHTML = highlightInner(entry.clause);

  const text = document.createElement("p");
  text.innerHTML = withCode(entry.text);

  const link = document.createElement("a");
  link.className = "isa-link";
  link.href = entry.link;
  link.textContent = `Definition of ${entry.linkText} ↗`;

  target.replaceChildren(clause, text, link);
}

/* Theorem tabs. */
for (const figure of document.querySelectorAll(".scene-theorems")) {
  const tabs = figure.querySelectorAll("[role=tab]");

  for (const tab of tabs) {
    tab.addEventListener("click", () => {
      figure.dataset.theorem = tab.dataset.theorem;

      for (const other of tabs) {
        other.setAttribute("aria-selected", String(other === tab));
      }
    });
  }
}

/* -------------------------------------------------------------------------- */
/* What an abstract value stands for                                          */
/* -------------------------------------------------------------------------- */

/*
 * Each value is its concretization as a predicate on integers. Joins list both sides
 * and the join Voblint computes, so the drawing can show which integers the join adds.
 * The results follow the domains' own join definitions.
 */
const mod = (x, m) => ((x % m) + m) % m;

const GAMMA_PRESETS = [
  { label: "[−2, 5]", kind: "interval", test: (x) => x >= -2 && x <= 5 },
  { label: "[3, +∞]", kind: "interval", test: (x) => x >= 3, tail: "right", note: "The set continues past 12 forever." },
  { label: "≥ 0", kind: "sign", test: (x) => x >= 0, tail: "right" },
  { label: "< 0", kind: "sign", test: (x) => x < 0, tail: "left" },
  { label: "even", kind: "parity", test: (x) => mod(x, 2) === 0, tail: "both" },
  { label: "1 (mod 3)", kind: "congruence", test: (x) => mod(x, 3) === 1, tail: "both" },
  { label: "4 (mod 0)", kind: "congruence", test: (x) => x === 4, note: "Modulus 0 pins the value: exactly 4." },
  {
    label: "≥0 · [0,9] · odd · 1 (mod 3)",
    kind: "Int product",
    test: (x) => x >= 0 && x <= 9 && mod(x, 2) === 1 && mod(x, 3) === 1,
    note: "A product stands for the integers every component allows: here only `1` and `7`.",
  },
  { label: "⊤", kind: "any domain", test: () => true, tail: "both", note: "Top: nothing is known." },
  { label: "⊥", kind: "any domain", test: () => false, note: "Bottom: no value at all. The analysis uses it for unreachable points." },
];

const JOIN_PRESETS = [
  {
    kind: "interval", a: "[−3, −1]", b: "[4, 6]", join: "[−3, 6]",
    left: (x) => x >= -3 && x <= -1, right: (x) => x >= 4 && x <= 6, test: (x) => x >= -3 && x <= 6,
    note: "An interval has no holes, so the join takes in `0` to `3` as well.",
  },
  {
    kind: "interval", a: "[2, 2]", b: "[8, 8]", join: "[2, 8]",
    left: (x) => x === 2, right: (x) => x === 8, test: (x) => x >= 2 && x <= 8,
    note: "Two exact values become five extra candidates: the merged context you will meet with procedures.",
  },
  {
    kind: "sign", a: "< 0", b: "0", join: "≤ 0",
    left: (x) => x < 0, right: (x) => x === 0, test: (x) => x <= 0, tail: "left",
    note: "This join is exact: `≤ 0` is precisely the two sets together.",
  },
  {
    kind: "sign", a: "< 0", b: "> 0", join: "⊤",
    left: (x) => x < 0, right: (x) => x > 0, test: () => true, tail: "both",
    note: "Sign has no value for “not zero”, so the join must admit `0`.",
  },
  {
    kind: "parity", a: "even", b: "odd", join: "⊤",
    left: (x) => mod(x, 2) === 0, right: (x) => mod(x, 2) === 1, test: () => true, tail: "both",
    note: "Exact, but useless: even and odd together are every integer.",
  },
  {
    kind: "congruence", a: "1 (mod 6)", b: "4 (mod 6)", join: "1 (mod 3)",
    left: (x) => mod(x, 6) === 1, right: (x) => mod(x, 6) === 4, test: (x) => mod(x, 3) === 1, tail: "both",
    note: "`gcd(6, 6, 1 − 4) = 3`, and the join is exact.",
  },
  {
    kind: "congruence", a: "1 (mod 3)", b: "2 (mod 3)", join: "⊤",
    left: (x) => mod(x, 3) === 1, right: (x) => mod(x, 3) === 2, test: () => true, tail: "both",
    note: "`gcd(3, 3, 1 − 2) = 1`: modulo 1 everything agrees, so the multiples of 3 come in too.",
  },
];

const SVG_NS = "http://www.w3.org/2000/svg";

for (const figure of document.querySelectorAll(".scene-gamma")) {
  const presets = figure.querySelector(".gamma-presets");
  const formula = figure.querySelector(".gamma-formula");
  const note = figure.querySelector(".gamma-note");
  const svg = figure.querySelector(".gamma-line");
  const modes = figure.querySelectorAll(".gamma-modes [data-mode]");
  const low = -12;
  const high = 12;
  const xOf = (n) => 40 + ((n - low) * 820) / (high - low);

  const axis = document.createElementNS(SVG_NS, "line");
  axis.setAttribute("class", "axis");
  axis.setAttribute("x1", "20");
  axis.setAttribute("x2", "880");
  axis.setAttribute("y1", "50");
  axis.setAttribute("y2", "50");
  svg.append(axis);

  const dots = [];

  for (let n = low; n <= high; n++) {
    const circle = document.createElementNS(SVG_NS, "circle");
    circle.setAttribute("cx", String(xOf(n)));
    circle.setAttribute("cy", "50");
    circle.setAttribute("r", "9");
    svg.append(circle);

    if (n % 2 === 0) {
      const label = document.createElementNS(SVG_NS, "text");
      label.setAttribute("x", String(xOf(n)));
      label.setAttribute("y", "86");
      label.textContent = String(n);
      svg.append(label);
    }

    dots.push({ n, circle });
  }

  const tails = ["left", "right"].map((side) => {
    const text = document.createElementNS(SVG_NS, "text");
    text.setAttribute("class", "tail");
    text.setAttribute("x", side === "left" ? "14" : "886");
    text.setAttribute("y", "56");
    text.textContent = "…";
    svg.append(text);
    return { side, text };
  });

  const draw = (inSet, extra, tail) => {
    for (const { n, circle } of dots) {
      const kind = inSet(n) ? "in" : extra(n) ? "extra" : "out";
      circle.setAttribute("class", `dot-${kind}`);
      circle.setAttribute("r", kind === "out" ? "6" : "9");
    }

    for (const { side, text } of tails) {
      text.style.visibility = tail === side || tail === "both" ? "visible" : "hidden";
    }
  };

  const showGamma = (preset) => {
    formula.innerHTML = `γ(<span>${preset.label}</span>) <span class="eq">in</span> ${preset.kind}`;
    note.innerHTML = withCode(preset.note ?? "");
    draw(preset.test, () => false, preset.tail);
  };

  const showJoin = (preset) => {
    formula.innerHTML = `${preset.a} ⊔ ${preset.b} <span class="eq">=</span> ${preset.join}`;
    note.innerHTML = withCode(preset.note);
    draw((n) => preset.left(n) || preset.right(n), (n) => preset.test(n), preset.tail);
  };

  const render = (mode, index) => {
    const list = mode === "join" ? JOIN_PRESETS : GAMMA_PRESETS;
    const chosen = Math.min(index, list.length - 1);

    figure.dataset.mode = mode;

    for (const button of modes) {
      button.setAttribute("aria-selected", String(button.dataset.mode === mode));
    }

    presets.replaceChildren(
      ...list.map((preset, i) => {
        const button = document.createElement("button");
        button.type = "button";
        button.setAttribute("aria-pressed", String(i === chosen));
        button.innerHTML = mode === "join"
          ? `${preset.a} ⊔ ${preset.b} <small>${preset.kind}</small>`
          : `${preset.label} <small>${preset.kind}</small>`;
        button.addEventListener("click", () => render(mode, i));
        return button;
      }),
    );

    (mode === "join" ? showJoin : showGamma)(list[chosen]);
  };

  for (const button of modes) {
    button.addEventListener("click", () => render(button.dataset.mode, 0));
  }

  render("gamma", 0);
}

/* -------------------------------------------------------------------------- */
/* Inside the top-down solver                                                 */
/* -------------------------------------------------------------------------- */

/*
 * One entry per solver event, transcribed from query/iterate in the vendored solver
 * for the counting loop. "c" is the set of unknowns being computed, in call order.
 */
const TD_STEPS = [
  { eq: "X", c: ["X"], stable: ["X"], point: [], sigma: { E: "⊥", H: "⊥", B: "⊥", X: "⊥" },
    text: "Solve `X`. `X` goes onto the set of unknowns being computed, and its equation needs `H`." },
  { eq: "H", c: ["X", "H"], stable: ["X", "H"], point: [], sigma: { E: "⊥", H: "⊥", B: "⊥", X: "⊥" },
    text: "`H` is not being computed yet, so the solver starts computing it. `H` needs `E`, then `B`." },
  { eq: "E", c: ["X", "H"], stable: ["X", "H", "E"], point: [], sigma: { E: "⊤", H: "⊥", B: "⊥", X: "⊥" },
    text: "`E` depends on nothing: it is `⊤`, any store, and immediately stable." },
  { eq: "B", c: ["X", "H", "B"], stable: ["X", "H", "E", "B"], point: ["H"], sigma: { E: "⊤", H: "⊥", B: "⊥", X: "⊥" },
    text: "`B` needs `H`, but `H` is still being computed: a cycle. The solver answers with `H`'s current value, `⊥`, and marks `H` as a loop point." },
  { eq: "B", c: ["X", "H"], stable: ["X", "H", "E", "B"], point: ["H"], sigma: { E: "⊤", H: "⊥", B: "⊥", X: "⊥" },
    text: "`B` evaluates to `⊥`, which is already its value, so `B` is done for now." },
  { eq: "H", c: ["X", "H"], stable: ["X", "E"], point: ["H"], sigma: { E: "⊤", H: "[0,0]", B: "⊥", X: "⊥" },
    text: "`H` evaluates to `[0,0]`. This round started before `H` was known to be a loop point, so it updates without widening. `H` changed, so `B`, which read `H`, is no longer stable." },
  { eq: "B", c: ["X", "H"], stable: ["X", "E", "H", "B"], point: ["H"], sigma: { E: "⊤", H: "[0,0]", B: "[0,0]", X: "⊥" },
    text: "`H` is evaluated again. `B` is recomputed from the new `H`: `[0,0]`." },
  { eq: "H", c: ["X", "H"], stable: ["X", "E"], point: ["H"], sigma: { E: "⊤", H: "[0,+∞]", B: "[0,0]", X: "⊥" },
    text: "`H`'s equation now gives `[0,1]`. `H` is a loop point and its value grew, so warrowing widens: `[0,+∞]`." },
  { eq: "B", c: ["X", "H"], stable: ["X", "E", "H", "B"], point: ["H"], sigma: { E: "⊤", H: "[0,+∞]", B: "[0,4]", X: "⊥" },
    text: "`B` recomputes: `assume(i < 5)` on `[0,+∞]` gives `[0,4]`." },
  { eq: "H", c: ["X", "H"], stable: ["X", "E"], point: ["H"], sigma: { E: "⊤", H: "[0,5]", B: "[0,4]", X: "⊥" },
    text: "`H`'s equation gives `[0,5]`, below the widened value, so warrowing narrows: `[0,5]`." },
  { eq: "H", c: ["X"], stable: ["X", "E", "H", "B"], point: [], sigma: { E: "⊤", H: "[0,5]", B: "[0,4]", X: "⊥" },
    text: "One more round changes nothing. `H` is stable, stops being computed, and is no longer a loop point." },
  { eq: "X", c: [], stable: ["X", "E", "H", "B"], point: [], sigma: { E: "⊤", H: "[0,5]", B: "[0,4]", X: "[5,5]" },
    text: "Back in `X`: `assume(i ≥ 5)` on `[0,5]` gives `[5,5]`. Everything is stable, and the check `i == 5` holds." },
];

for (const figure of document.querySelectorAll(".scene-td")) {
  const caption = figure.querySelector(".td-caption");
  const equations = figure.querySelectorAll(".td-eq");
  const rows = figure.querySelectorAll(".td-sigma tr");
  const sets = figure.querySelectorAll(".td-chips");
  const chipsBox = figure.querySelector(".td-steps");
  const toggle = figure.querySelector(".loop-play");
  const icon = toggle.querySelector("i");
  let step = 0;
  let previous = null;
  let timer = null;

  const chips = TD_STEPS.map((_, i) => {
    const chip = document.createElement("button");
    chip.type = "button";
    chip.textContent = String(i + 1);
    chip.addEventListener("click", () => {
      setPlaying(false);
      show(i);
    });
    chipsBox.append(chip);
    return chip;
  });

  const show = (next) => {
    step = (next + TD_STEPS.length) % TD_STEPS.length;
    const state = TD_STEPS[step];
    figure.dataset.step = String(step);
    caption.innerHTML = withCode(state.text);

    for (const node of figure.querySelectorAll(".td-node")) {
      node.classList.toggle("is-current", node.dataset.var === state.eq);
      node.querySelector("[data-val]").textContent = state.sigma[node.dataset.var];
    }

    for (const eq of equations) {
      eq.classList.toggle("is-current", eq.dataset.var === state.eq);
    }

    for (const row of rows) {
      const name = row.dataset.var;
      const cell = row.querySelector("td");
      const changed = previous !== null && previous.sigma[name] !== state.sigma[name];
      cell.textContent = state.sigma[name];
      row.classList.remove("changed");

      if (changed) {
        void row.offsetWidth;
        row.classList.add("changed");
      }
    }

    for (const box of sets) {
      const members = state[box.dataset.set];
      box.replaceChildren(
        ...(members.length
          ? members.map((name) => Object.assign(document.createElement("span"), { textContent: name }))
          : [Object.assign(document.createElement("span"), { className: "empty", textContent: "empty" })]),
      );
    }

    chips.forEach((chip, i) => chip.setAttribute("aria-pressed", String(i === step)));
    previous = state;
  };

  const setPlaying = (playing) => {
    clearInterval(timer);
    timer = playing
      ? setInterval(() => {
          if (!figure.classList.contains("is-offscreen")) {
            show(step + 1);
          }
        }, 3200)
      : null;
    icon.className = playing ? "fa-solid fa-pause" : "fa-solid fa-play";
    toggle.setAttribute("aria-label", playing ? "Pause" : "Play");
  };

  toggle.addEventListener("click", () => setPlaying(timer === null));
  figure.querySelector(".td-controls").hidden = false;
  show(0);
  setPlaying(!reducedMotion);
}

/* -------------------------------------------------------------------------- */
/* Voblint and Goblint; the language map                                      */
/* -------------------------------------------------------------------------- */

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

for (const figure of document.querySelectorAll(".scene-island")) {
  const note = figure.querySelector(".island-note");
  const idle = note.textContent;

  for (const region of figure.querySelectorAll("[data-note]")) {
    const show = () => { note.innerHTML = withCode(region.dataset.note); };
    region.addEventListener("pointerenter", show);
    region.addEventListener("focus", show);
    region.addEventListener("pointerleave", () => { note.textContent = idle; });
    region.addEventListener("blur", () => { note.textContent = idle; });
  }
}

/* -------------------------------------------------------------------------- */
/* Isabelle statements                                                        */
/* -------------------------------------------------------------------------- */

/*
 * Colors the theorem statements the way Isabelle/jEdit distinguishes them: outer
 * keywords, the theorem name, free variables and variables bound by a quantifier
 * or lambda. Names that are constants of the development stay plain.
 */
const ISABELLE_CONSTANTS = new Set([
  "star", "pstep", "declared_global", "prog_table", "main_body", "config_terminates",
  "run_voblint", "csim", "prog_cfg", "ltr_collect", "cinit_stores", "analysis_result_covers",
  "checks_sound_at", "next_check", "set", "res_checks", "check_exp", "check_point",
  "check_verdict", "truthy", "aval", "res_diagnostics", "diagnostic_point",
  "arithmetic_safe_at", "map", "check_sites",
]);

const escapeText = (text) => text.replace(/[&<>]/g, (ch) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" })[ch]);
const span = (kind, text) => `<span class="isa-${kind}">${escapeText(text)}</span>`;

function highlightInner(term) {
  const bound = new Set();

  for (const match of term.matchAll(/[∀∃λ]\s*([A-Za-z_][\w\s]*?)\s*(?:\.|∈)/g)) {
    for (const name of match[1].split(/\s+/)) {
      bound.add(name);
    }
  }

  return term.replace(/([A-Za-z_][\w']*)|([∀∃λ∈∧∨⟶¬≠=.])|([^A-Za-z_∀∃λ∈∧∨⟶¬≠=.]+)/g, (whole, word, symbol, rest) => {
    if (word) {
      if (bound.has(word)) return span("bound", word);
      if (/^[A-Z][\w']+$/.test(word)) return span("ctor", word);
      if (ISABELLE_CONSTANTS.has(word)) return escapeText(word);
      return span("free", word);
    }

    return symbol ? span("op", symbol) : escapeText(rest);
  });
}

function highlightIsabelle(source) {
  return source
    .split(/("[^"]*")/)
    .map((part, i) => {
      if (i % 2 === 1) {
        return span("quote", '"') + highlightInner(part.slice(1, -1)) + span("quote", '"');
      }

      return escapeText(part)
        .replace(/^(theorem|corollary|lemma)(\s+)([\w']+)/m, '<span class="isa-keyword">$1</span>$2<span class="isa-name">$3</span>')
        .replace(/\b(assumes|shows|and|fixes|obtains)\b/g, '<span class="isa-sub">$1</span>');
    })
    .join("");
}

for (const pre of document.querySelectorAll(".thm-panel pre")) {
  pre.innerHTML = highlightIsabelle(pre.textContent);
}

/* -------------------------------------------------------------------------- */
/* Reading progress and the graph-to-equations figure                         */
/* -------------------------------------------------------------------------- */

for (const toc of document.querySelectorAll(".doc-toc")) {
  const fill = toc.querySelector(".doc-toc-fill");
  const percent = toc.querySelector(".doc-toc-percent span");
  const main = document.querySelector(".doc-main");
  const links = [...toc.querySelectorAll("a[data-target]")]
    .map((link) => ({ link, section: document.getElementById(link.dataset.target) }))
    .filter(({ section }) => section);
  let frame = 0;

  const update = () => {
    frame = 0;
    const box = main.getBoundingClientRect();
    const read = Math.min(1, Math.max(0, (window.innerHeight * 0.35 - box.top) / box.height));
    fill.style.height = `${(read * 100).toFixed(1)}%`;
    percent.textContent = String(Math.round(read * 100));

    const probe = window.innerHeight * 0.35;
    let current = 0;

    links.forEach(({ section }, i) => {
      if (section.getBoundingClientRect().top <= probe) {
        current = i;
      }
    });

    links.forEach(({ link }, i) => {
      link.classList.toggle("is-read", i < current);
      link.classList.toggle("is-current", i === current);
    });
  };

  const schedule = () => {
    if (!frame) {
      frame = requestAnimationFrame(update);
    }
  };

  window.addEventListener("scroll", schedule, { passive: true });
  window.addEventListener("resize", schedule);
  update();
}

for (const figure of document.querySelectorAll(".scene-eqs")) {
  const parts = figure.querySelectorAll("[data-edge]");

  const highlight = (edge) => {
    for (const part of parts) {
      part.classList.toggle("is-hl", edge !== null && part.dataset.edge === edge);
    }
  };

  for (const part of parts) {
    part.addEventListener("pointerenter", () => highlight(part.dataset.edge));
    part.addEventListener("focus", () => highlight(part.dataset.edge));
    part.addEventListener("pointerleave", () => highlight(null));
    part.addEventListener("blur", () => highlight(null));
  }
}

/* -------------------------------------------------------------------------- */
/* Why this takes so long to prove: live repository figures                   */
/* -------------------------------------------------------------------------- */

/*
 * The site build writes window.VOBLINT_STATS. Without it the markup keeps the figures
 * it shipped with and the breakdown stays hidden.
 */
const SESSION_LABELS = {
  Program_Model: "Program model: VIMP, CFG, compiler",
  Abstract_Interpreter: "Abstract interpreter: domains, solver, framework",
  Analyses: "Analyses: five domains and their results",
  Executable_Surface: "Executable surface: run_voblint, code export",
  Examples: "Examples and regressions",
};

const CORPUS_LABELS = {
  precision: "precision",
  soundness: "soundness",
  "known-imprecision": "known imprecision",
  other: "graph, parser and tooling",
};

const formatCount = (n) => Number(n).toLocaleString("en-US");

/* Shoelace area of a path made only of absolute M/L commands. */
function polygonArea(d) {
  const points = [...d.matchAll(/(-?[\d.]+)[ ,]+(-?[\d.]+)/g)].map((m) => [Number(m[1]), Number(m[2])]);
  let twice = 0;

  points.forEach(([x1, y1], i) => {
    const [x2, y2] = points[(i + 1) % points.length];
    twice += x1 * y2 - x2 * y1;
  });

  return Math.abs(twice) / 2;
}

function statRow(label, detail, parts, total) {
  const row = document.createElement("div");
  row.className = "stats-row";

  const head = document.createElement("p");
  head.innerHTML = `<span>${escapeText(label)}</span><small>${escapeText(detail)}</small>`;

  const bar = document.createElement("div");
  bar.className = "stats-bar";
  bar.style.setProperty("--share", `${((100 * parts.reduce((sum, p) => sum + p.value, 0)) / total).toFixed(2)}%`);

  for (const part of parts) {
    const piece = document.createElement("span");
    piece.className = part.kind;
    piece.style.flexGrow = String(part.value);
    piece.title = `${part.title}: ${formatCount(part.value)}`;
    bar.append(piece);
  }

  row.append(head, bar);
  return row;
}

for (const figure of document.querySelectorAll(".scene-iceberg")) {
  const stats = window.VOBLINT_STATS;

  if (!stats) {
    continue;
  }

  for (const element of figure.querySelectorAll("[data-stat]")) {
    const value = element.dataset.stat.split(".").reduce((obj, key) => obj?.[key], stats);

    if (value !== undefined) {
      element.textContent = formatCount(value);
    }
  }

  /* One area per line across all three shapes: the tip keeps its outline and scales in height,
     the solver berg is the body scaled about its centre. */
  const tip = figure.querySelector(".berg-tip");
  const body = figure.querySelector(".berg-body");
  const bodyArea = polygonArea(body.getAttribute("d"));
  const waterline = 110;
  const wanted = (bodyArea * stats.generated_ocaml) / stats.isabelle.lines;
  const scale = Math.min(2, wanted / polygonArea(tip.getAttribute("d")));
  const solver = figure.querySelector(".berg-solver");
  const shrink = Math.sqrt(stats.solver.lines / stats.isabelle.lines).toFixed(3);
  solver.setAttribute(
    "transform",
    solver.getAttribute("transform").replace(/scale\([^)]*\)/, `scale(-${shrink} ${shrink})`),
  );
  tip.setAttribute(
    "d",
    tip.getAttribute("d").replace(/(-?[\d.]+)[ ,]+(-?[\d.]+)/g, (_, x, y) =>
      `${x} ${(waterline - (waterline - Number(y)) * scale).toFixed(1)}`),
  );

  const sessions = figure.querySelector('[data-stats="sessions"]');
  const widest = Math.max(...stats.isabelle.sessions.map((s) => s.lines));
  sessions.replaceChildren(
    ...stats.isabelle.sessions.map((s) =>
      statRow(
        SESSION_LABELS[s.name] ?? s.name,
        `${formatCount(s.lines)} lines · ${s.theories} theories · ${formatCount(s.proofs)} lemmas`,
        [
          { kind: "code", value: s.code, title: "proof and definitions" },
          { kind: "doc", value: s.doc, title: "documentation" },
          { kind: "blank", value: s.lines - s.code - s.doc, title: "blank" },
        ],
        widest,
      )),
  );

  const corpus = figure.querySelector('[data-stats="corpus"]');
  const kinds = Object.entries(stats.corpus.kinds);
  const most = Math.max(...kinds.map(([, n]) => n));
  corpus.replaceChildren(
    ...kinds.map(([kind, n]) =>
      statRow(CORPUS_LABELS[kind] ?? kind, `${n} programs`, [{ kind: `corpus-${kind}`, value: n, title: kind }], most)),
  );

  const stamp = figure.querySelector(".stats-stamp");
  stamp.textContent = `Counted when the site was built, on ${stats.date}${stats.commit ? ` at commit ${stats.commit}` : ""}.`;
  figure.querySelector(".stats-breakdown").hidden = false;
}

/* -------------------------------------------------------------------------- */
/* Shared stepper                                                             */
/* -------------------------------------------------------------------------- */

/*
 * Wires a play button and step chips to a render function. Chips either ship in the
 * markup (data-goto) or are created here, one per step; the controls stay hidden
 * without script, so the figure's final state is what a no-script reader sees.
 */
function makeStepper(figure, { count, render, controls, chipsBox, interval = 3200, autoplay = !reducedMotion }) {
  const toggle = controls.querySelector(".loop-play");
  const icon = toggle.querySelector("i");
  let step = 0;
  let timer = null;

  let chips = [...chipsBox.querySelectorAll("[data-goto]")];

  if (!chips.length) {
    chips = Array.from({ length: count }, (_, i) => {
      const chip = document.createElement("button");
      chip.type = "button";
      chip.dataset.goto = String(i);
      chip.textContent = String(i + 1);
      chipsBox.append(chip);
      return chip;
    });
  }

  const show = (next) => {
    step = (next + count) % count;
    figure.dataset.step = String(step);
    chips.forEach((chip) => chip.setAttribute("aria-pressed", String(Number(chip.dataset.goto) === step)));
    render(step);
  };

  const setPlaying = (playing) => {
    clearInterval(timer);
    timer = playing
      ? setInterval(() => {
          if (!figure.classList.contains("is-offscreen")) {
            show(step + 1);
          }
        }, interval)
      : null;
    icon.className = playing ? "fa-solid fa-pause" : "fa-solid fa-play";
    toggle.setAttribute("aria-label", playing ? "Pause" : "Play");
  };

  for (const chip of chips) {
    chip.addEventListener("click", () => {
      setPlaying(false);
      show(Number(chip.dataset.goto));
    });
  }

  toggle.addEventListener("click", () => setPlaying(timer === null));
  controls.hidden = false;
  show(0);
  setPlaying(autoplay);

  return { show: (i) => { setPlaying(false); show(i); }, stop: () => setPlaying(false), current: () => step };
}

/* Draws dots for the integers low..high into an SVG row, classed by a predicate. */
function drawDots(svg, { low, high, x0, dx, y, classOf, radius = 6 }) {
  svg.replaceChildren();

  for (let n = low; n <= high; n++) {
    const circle = document.createElementNS(SVG_NS, "circle");
    const kind = classOf(n);
    circle.setAttribute("cx", String(x0 + (n - low) * dx));
    circle.setAttribute("cy", String(y));
    circle.setAttribute("r", String(kind === "out" ? radius * 0.55 : radius));
    circle.setAttribute("class", `dot-${kind}`);
    svg.append(circle);
  }
}

/* -------------------------------------------------------------------------- */
/* Four domains, one value: reduction                                         */
/* -------------------------------------------------------------------------- */

/*
 * Transcribed from refine_round = [refine_interval, refine_congruence], iterated by
 * refine_fix, on the state each domain computes alone for x at the two checks.
 */
const REDUCE_TESTS = {
  "≥ 0": (x) => x >= 0,
  "> 0": (x) => x > 0,
  "[0, 10]": (x) => x >= 0 && x <= 10,
  "[1, 9]": (x) => x >= 1 && x <= 9,
  odd: (x) => mod(x, 2) === 1,
  "1 (mod 4)": (x) => mod(x, 4) === 1,
};

const REDUCE_STEPS = [
  {
    sign: "≥ 0", interval: "[0, 10]", parity: "odd", congruence: "1 (mod 4)", changed: [], proved: false,
    text: "What each domain finds on its own. No component rules out `0` or `10`, so neither check is decided, although together they allow only `1`, `5` and `9`.",
  },
  {
    sign: "≥ 0", interval: "[0, 10]", parity: "odd", congruence: "1 (mod 4)", changed: [], proved: false,
    text: "`refine_interval` intersects sign and interval. `≥ 0` and `[0, 10]` agree, and `[0, 10]` is not a single value that would fix the parity. Nothing changes.",
  },
  {
    sign: "≥ 0", interval: "[1, 9]", parity: "odd", congruence: "1 (mod 4)", changed: ["interval"], proved: true,
    text: "`refine_congruence` intersects parity and congruence, which gives `1 (mod 4)`, and moves the interval's bounds onto that residue class: `0` becomes `1` and `10` becomes `9`. Both checks are now decided.",
  },
  {
    sign: "> 0", interval: "[1, 9]", parity: "odd", congruence: "1 (mod 4)", changed: ["sign"], proved: true,
    text: "The round repeats. `refine_interval` sees `[1, 9]`, which excludes `0`, so the sign sharpens to `> 0`.",
  },
  {
    sign: "> 0", interval: "[1, 9]", parity: "odd", congruence: "1 (mod 4)", changed: [], proved: true,
    text: "Another round changes nothing, so this is the fixpoint. The set is still `{1, 5, 9}`, with a smaller description.",
  },
];

for (const figure of document.querySelectorAll(".scene-reduce")) {
  const rows = [...figure.querySelectorAll(".reduce-row")];
  const caption = figure.querySelector(".reduce-caption");
  const checks = figure.querySelectorAll(".reduce-checks li");
  const line = { low: -2, high: 12, x0: 12, dx: 21.8, y: 12 };

  const axis = figure.querySelector(".reduce-axis svg");

  for (const n of [0, 4, 8, 12]) {
    const label = document.createElementNS(SVG_NS, "text");
    label.setAttribute("x", String(line.x0 + (n - line.low) * line.dx));
    label.setAttribute("y", "16");
    label.textContent = String(n);
    axis.append(label);
  }

  const render = (i) => {
    const state = REDUCE_STEPS[i];
    const together = (x) => ["sign", "interval", "parity", "congruence"].every((c) => REDUCE_TESTS[state[c]](x));

    for (const row of rows) {
      const comp = row.dataset.comp;
      const svg = row.querySelector("svg");

      if (comp === "together") {
        drawDots(svg, { ...line, classOf: (x) => (together(x) ? "in" : "out") });
        continue;
      }

      row.querySelector(".reduce-val").textContent = state[comp];
      row.classList.toggle("changed", state.changed.includes(comp));
      drawDots(svg, { ...line, classOf: (x) => (REDUCE_TESTS[state[comp]](x) ? (together(x) ? "in" : "extra") : "out") });
    }

    caption.innerHTML = withCode(state.text);

    for (const check of checks) {
      const verdict = check.querySelector(".verdict");
      verdict.textContent = state.proved ? "PROVED" : "UNKNOWN";
      verdict.className = `verdict ${state.proved ? "proved" : "unknown"}`;
    }
  };

  makeStepper(figure, {
    count: REDUCE_STEPS.length,
    render,
    controls: figure.querySelector(".reduce-controls"),
    chipsBox: figure.querySelector(".reduce-steps"),
  });
}

/* -------------------------------------------------------------------------- */
/* Strategy trees                                                             */
/* -------------------------------------------------------------------------- */

/*
 * Each tree here is a chain: every node has one continuation. "n" ties a node to the
 * do-notation lines carrying the same data-n; "walk" is what evaluating it under the
 * current σ reads, contributes or returns.
 */
const TREES = {
  edge: {
    nodes: [
      { kind: "QueryL", label: "QueryL H", edge: "λh." },
      { kind: "Answer", label: "Answer (assume (i ≥ 5) h)" },
    ],
    walk: [
      "`QueryL H` reads `σ(H) = [0, 5]` and binds it to `h`. That read is the edge's only dependency.",
      "`Answer` applies the edge's action: `assume (i ≥ 5)` on `[0, 5]` gives `[5, 5]`.",
    ],
    post: "The answer `[5, 5]` is below `σ(X) = [5, 5]`, so `X` is covered. A transfer that also touched globals would add a `QueryG` to read them and a `Side` to write them; the shipped domains keep their whole state local, so their edges compile to exactly this shape.",
  },
  loop: {
    nodes: [
      { kind: "QueryL", label: "QueryL E", edge: "λe." },
      { kind: "QueryL", label: "QueryL B", edge: "λb." },
      { kind: "Answer", label: "Answer ([i := 0] e ⊔ [i := i + 1] b)" },
    ],
    walk: [
      "`QueryL E` reads `σ(E) = ⊤` and binds it to `e`.",
      "`QueryL B` reads `σ(B) = [0, 4]` and binds it to `b`.",
      "`Answer` returns `[0, 0] ⊔ [1, 5] = [0, 5]`.",
    ],
    post: "The answer `[0, 5]` is below `σ(H) = [0, 5]`, and the tree has no side effects, so `H` is covered.",
  },
  call: {
    nodes: [
      { kind: "QueryL", label: "QueryL (pp5, c)", edge: "λcaller." },
      { kind: "Side", label: "Side (Seed entry_f c') entry" },
      { kind: "QueryL", label: "QueryL (exit_f, c')", edge: "λcallee." },
      { kind: "Answer", label: "Answer (combine caller callee)" },
    ],
    walk: [
      "`QueryL (pp5, c)` reads the caller's state: `a = ⊤`.",
      "`enter` binds `n := 2`, the context policy picks `c' = [n ↦ [2, 2]]`, and `Side` contributes `n = [2, 2]` to the global unknown `Seed entry_f c'`.",
      "`QueryL (exit_f, c')` reads the callee's exit under that key: `#ret = [2, 2]`.",
      "`Answer` returns the combined state: `a = [2, 2]`.",
    ],
    post: "The answer is below `σ(pp6, c)`, and the side contribution `n = [2, 2]` is below `σ(Seed entry_f c')`. A post-solution bounds both.",
  },
  entry: {
    nodes: [
      { kind: "QueryG", label: "QueryG (Seed entry_f c)", edge: "λseed." },
      { kind: "Answer", label: "Answer seed" },
    ],
    walk: [
      "`QueryG (Seed entry_f c)` reads the global every call site's `Side` writes to. For `c = [n ↦ [2, 2]]` that is `n = [2, 2]`.",
      "`Answer` returns it as the entry state of this copy of `f`.",
    ],
    post: "The answer is below `σ(entry_f, c)`. Several call sites can write one seed; the Globals setting decides how their contributions combine.",
  },
};

function drawTree(svg, tree) {
  svg.innerHTML = `<defs><marker id="tree-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M0 0 L10 5 L0 10 z" class="arrow-head"/></marker></defs>`;
  const x = 180;
  const gap = tree.nodes.length > 3 ? 92 : 118;
  const top = 44;

  tree.nodes.forEach((node, i) => {
    const y = top + i * gap;

    if (i > 0) {
      const edge = document.createElementNS(SVG_NS, "g");
      edge.setAttribute("class", "tree-edge");
      edge.innerHTML = `<line x1="${x}" y1="${y - gap + 22}" x2="${x}" y2="${y - 24}" marker-end="url(#tree-arrow)"/>`;
      const from = tree.nodes[i - 1];

      if (from.edge) {
        edge.innerHTML += `<text x="${x + 10}" y="${y - gap / 2 + 4}">${escapeText(from.edge)} …</text>`;
      }

      svg.append(edge);
    }

    const group = document.createElementNS(SVG_NS, "g");
    group.setAttribute("class", `tree-node tree-${node.kind.toLowerCase()}`);
    group.dataset.n = String(i + 1);
    const width = Math.min(340, 26 + node.label.length * 7.4);
    group.innerHTML = `<rect x="${x - width / 2}" y="${y - 20}" width="${width}" height="40" rx="${node.kind === "Answer" ? 20 : 8}"/>`
      + `<text x="${x}" y="${y + 5}">${escapeText(node.label)}</text>`;
    svg.append(group);
  });
}

for (const figure of document.querySelectorAll(".scene-trees")) {
  const svg = figure.querySelector(".trees-svg");
  const tabs = figure.querySelectorAll("[role=tab]");
  const codes = figure.querySelectorAll(".trees-code");
  const walk = figure.querySelector(".trees-walk");
  const post = figure.querySelector(".trees-post");
  const controls = figure.querySelector(".trees-controls");
  const chipsBox = figure.querySelector(".trees-steps");
  let tree = TREES.edge;
  let stepper = null;

  const mark = (n) => {
    for (const node of svg.querySelectorAll(".tree-node")) {
      node.classList.toggle("is-current", node.dataset.n === String(n));
    }

    for (const line of figure.querySelectorAll(".trees-code:not([hidden]) [data-n]")) {
      line.classList.toggle("is-current", line.dataset.n === String(n));
    }
  };

  const render = (i) => {
    mark(i + 1);
    walk.replaceChildren(
      ...tree.walk.slice(0, i + 1).map((text, j) => {
        const item = document.createElement("li");
        item.innerHTML = withCode(text);
        item.classList.toggle("is-current", j === i);
        return item;
      }),
    );
    post.innerHTML = i === tree.walk.length - 1 ? `<p>${withCode(tree.post)}</p>` : "";
    post.hidden = i !== tree.walk.length - 1;
  };

  const select = (name) => {
    tree = TREES[name];
    figure.dataset.tree = name;
    tabs.forEach((tab) => tab.setAttribute("aria-selected", String(tab.dataset.tree === name)));
    codes.forEach((code) => { code.hidden = code.dataset.for !== name; });
    drawTree(svg, tree);
    stepper?.stop();
    chipsBox.replaceChildren();
    const fresh = controls.querySelector(".loop-play").cloneNode(true);
    controls.querySelector(".loop-play").replaceWith(fresh);
    stepper = makeStepper(figure, { count: tree.walk.length, render, controls, chipsBox, interval: 2600, autoplay: false });
    stepper.show(tree.walk.length - 1);
  };

  for (const line of figure.querySelectorAll(".trees-code [data-n]")) {
    line.addEventListener("pointerenter", () => mark(line.dataset.n));
    line.addEventListener("pointerleave", () => mark(stepper.current() + 1));
  }

  tabs.forEach((tab) => tab.addEventListener("click", () => select(tab.dataset.tree)));
  select("edge");
}

/* -------------------------------------------------------------------------- */
/* The life of a call                                                         */
/* -------------------------------------------------------------------------- */

/* Values are the interval analyzer's results for the factorial program, per context mode. */
const CALL_VALUES = {
  entry: { caller: "a = ⊤", entry: "n = [2, 2]", ctx: "c' = [n ↦ [2,2]]", seed: "n = [2, 2]", exit: "#ret = [2, 2]", after: "a = [2, 2]" },
  none: { caller: "a = ⊤", entry: "n = [2, 2]", ctx: "c' = ()", seed: "n = [−∞, 2]", exit: "#ret = ⊤", after: "a = ⊤" },
};

const CALL_STAGES = [
  {
    text: "The caller's state at the call site `pp5`, read from the solver's current values. `a` is a local of `main` that nothing has assigned yet, so it may hold any integer.",
    obligation: "Read by `QueryL (pp5, c)`.",
  },
  {
    text: "`enter` evaluates the argument `2` in the caller's state and binds it to `n`. It returns a list of alternatives, each a continuation state paired with an entry state; the interval analysis returns one.",
    obligation: "Obligation `enter_sound_local`: for every caller store in `γ`, some alternative's entry state covers the concrete `call_enter`.",
  },
  {
    text: { entry: "Entry-state contexts use the entry state as the key: `c' = [n ↦ [2, 2]]`. The recursive call `f(n - 1)` enters with `n = [1, 1]` and gets a key of its own.", none: "No context: every call of `f`, from `main` or from `f` itself, uses the single key `()`." },
    obligation: "Obligation `routed_entry_cover`: the key the policy picks is one the semantics admits for this entry.",
  },
  {
    text: { entry: "The entry state goes, as a side effect, to the global unknown `Seed entry_f c'`, which only this call writes. It holds `n = [2, 2]`.", none: "The entry state goes to `Seed entry_f ()`. The recursive call writes `n = 1` into the same key, the lower bound moves, and warrowing widens the value to `[−∞, 2]`." },
    obligation: "The published value stays below `σ` at the seed, which the post-solution guarantees (`routed_seed_publish_bound_seed`).",
  },
  {
    text: { entry: "The call reads the callee's exit under the same key. `f(2)` returns `2 * 1`, so `#ret = [2, 2]`.", none: "The one exit of `f` covers every activation, including ones with the values of `n` that widening added, so the return value is `⊤`." },
    obligation: "Obligation `routed_context_comb`: the exit state read here covers the concrete callee's final store.",
  },
  {
    text: { entry: "`combine` keeps the caller's locals, takes the callee's globals and writes `#ret` into `a`: `a = [2, 2]` at `pp6`, and `a == 2` is PROVED.", none: "`combine` writes `⊤` into `a`, and `a == 2` is UNKNOWN. That answer is imprecise but sound: `⊤` contains `2`." },
    obligation: "Obligation `combine_sound`: `combine_collect` of a covered caller store and a covered callee store is covered.",
  },
];

for (const figure of document.querySelectorAll(".scene-call")) {
  const stages = figure.querySelectorAll(".call-stage");
  const caption = figure.querySelector(".call-caption");
  const obligation = figure.querySelector(".call-obligation");
  const tabs = figure.querySelectorAll(".call-modes [role=tab]");
  let mode = figure.dataset.mode;
  let current = 0;

  const render = (i) => {
    current = i;
    const values = CALL_VALUES[mode];

    for (const element of figure.querySelectorAll("[data-val]")) {
      element.textContent = values[element.dataset.val];
    }

    stages.forEach((stage) => {
      const index = Number(stage.dataset.stage);
      stage.classList.toggle("is-current", index === i);
      stage.classList.toggle("is-done", index < i);
    });

    const stage = CALL_STAGES[i];
    caption.innerHTML = withCode(typeof stage.text === "string" ? stage.text : stage.text[mode]);
    obligation.innerHTML = withCode(stage.obligation);
  };

  const stepper = makeStepper(figure, {
    count: CALL_STAGES.length,
    render,
    controls: figure.querySelector(".call-controls"),
    chipsBox: figure.querySelector(".call-steps"),
  });

  for (const stage of stages) {
    const jump = () => stepper.show(Number(stage.dataset.stage));
    stage.addEventListener("click", jump);
    stage.addEventListener("focus", jump);
  }

  for (const tab of tabs) {
    tab.addEventListener("click", () => {
      mode = tab.dataset.mode;
      figure.dataset.mode = mode;
      tabs.forEach((other) => other.setAttribute("aria-selected", String(other === tab)));
      render(current);
    });
  }
}

/* -------------------------------------------------------------------------- */
/* What a run is: source, graph, trace                                        */
/* -------------------------------------------------------------------------- */

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
    line: "calla", edges: ["body_main"], node: "pp5", store: "a = ?",
    residual: ["a = f(2)", CHECK], frames: [], rets: [], callers: [],
    rules: { source: "start (main body, s₀, [])", graph: "Intra body(main)", trace: "Root, intra" },
    tree: act("main", "Root", ["entry_main", "pp5"]),
    text: "The run starts in `main` with no frames. The source is about to run `a = f(2)`. The matching graph configuration already sits at `pp5`: its trace starts with `Root` at `entry_main` and has taken `main`'s body edge.",
  },
  {
    line: "if", edges: ["call_main", "body_f"], node: "pp0", store: "n = 2, r = 0",
    residual: ["if (n < 2) …", "Restore", CHECK], frames: [FRAME_MAIN], rets: [RET_MAIN], callers: ["main"],
    rules: { source: "Call", graph: "Call, Intra body(f)", trace: "call, intra" },
    tree: act("main", "Root", ["entry_main", "pp5"], act("f(2)", "Call", ["entry_f", "pp0"])),
    text: "The source `Call` evaluates `2`, binds it to `n` in a fresh store, pushes a frame that remembers the caller's store and the destination `a`, and runs `f`'s body followed by `Restore`. The graph takes the call edge, pushes the return point `pp6` and follows `f`'s body edge. The trace opens a new activation, `Call main …`.",
  },
  {
    line: "call", edges: ["ge"], node: "pp2", store: "n = 2, r = 0",
    residual: ["r = f(n - 1)", "return n * r", "Restore", CHECK], frames: [FRAME_MAIN], rets: [RET_MAIN], callers: ["main"],
    rules: { source: "IfFalse", graph: "Intra ¬ n < 2", trace: "intra" },
    tree: act("main", "Root", ["entry_main", "pp5"], act("f(2)", "Call", ["entry_f", "pp0", "pp2"])),
    text: "`n < 2` is false. Both sides take the else branch, and the trace extends its path.",
  },
  {
    line: "if", edges: ["call_f", "body_f"], node: "pp0", store: "n = 1, r = 0",
    residual: ["if (n < 2) …", "Restore", "return n * r", "Restore", CHECK], frames: [FRAME_F2, FRAME_MAIN], rets: [RET_F2, RET_MAIN], callers: ["f(2)", "main"],
    rules: { source: "Call", graph: "Call, Intra body(f)", trace: "call, intra" },
    tree: act("main", "Root", ["entry_main", "pp5"], act("f(2)", "Call", ["entry_f", "pp0", "pp2"], act("f(1)", "Call", ["entry_f", "pp0"]))),
    text: "The recursive call. Each side grows its stack by one entry, a frame, a return point `pp3`, a trace nested one level deeper: `Call (Call (Root …) …) …`. The graph reuses the same node `entry_f`.",
  },
  {
    line: "ret1", edges: ["lt"], node: "pp1", store: "n = 1, r = 0",
    residual: ["return 1", "Restore", "return n * r", "Restore", CHECK], frames: [FRAME_F2, FRAME_MAIN], rets: [RET_F2, RET_MAIN], callers: ["f(2)", "main"],
    rules: { source: "IfTrue", graph: "Intra n < 2", trace: "intra" },
    tree: act("main", "Root", ["entry_main", "pp5"], act("f(2)", "Call", ["entry_f", "pp0", "pp2"], act("f(1)", "Call", ["entry_f", "pp0", "pp1"]))),
    text: "Now `n = 1`, so `n < 2` holds.",
  },
  {
    line: "ret1", edges: ["ret1"], node: "exit_f", store: "n = 1, r = 0, #ret = 1",
    residual: ["Unwind", "Restore", "return n * r", "Restore", CHECK], frames: [FRAME_F2, FRAME_MAIN], rets: [RET_F2, RET_MAIN], callers: ["f(2)", "main"],
    rules: { source: "ReturnSome", graph: "Intra return 1", trace: "intra" },
    tree: act("main", "Root", ["entry_main", "pp5"], act("f(2)", "Call", ["entry_f", "pp0", "pp2"], act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"]))),
    text: "`return 1` writes the return variable `#ret` and turns the rest of the body into `Unwind`. The graph reaches `exit_f`, the one result node that every activation of `f` shares.",
  },
  {
    line: "call", edges: ["resume_f"], node: "pp3", store: "n = 2, r = 1",
    residual: ["SKIP", "return n * r", "Restore", CHECK], frames: [FRAME_MAIN], rets: [RET_MAIN], callers: ["main"],
    rules: { source: "UnwindAct", graph: "Return", trace: "ret: Resume" },
    tree: act("main", "Root", ["entry_main", "pp5"], act("f(2)", "Resume", ["entry_f", "pp0", "pp2", "pp3"], act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true))),
    text: "The source pops its frame: the caller's locals come back and `r := #ret`. The graph pops its return point, jumps to `pp3` without following an edge, and applies `combine_collect`. The trace builds `Resume`: the caller's path continues at `pp3`, and the finished callee stays inside it.",
  },
  {
    line: "retn", edges: [], node: "pp3", store: "n = 2, r = 1",
    residual: ["return n * r", "Restore", CHECK], frames: [FRAME_MAIN], rets: [RET_MAIN], callers: ["main"],
    rules: { source: "Seq1", graph: "no step", trace: "no step" },
    tree: act("main", "Root", ["entry_main", "pp5"], act("f(2)", "Resume", ["entry_f", "pp0", "pp2", "pp3"], act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true))),
    text: "`Seq SKIP c` steps to `c`, and the graph does not move. The simulation allows zero graph steps: `csim` relates both source configurations to `pp3`.",
  },
  {
    line: "retn", edges: ["retn"], node: "exit_f", store: "n = 2, r = 1, #ret = 2",
    residual: ["Unwind", "Restore", CHECK], frames: [FRAME_MAIN], rets: [RET_MAIN], callers: ["main"],
    rules: { source: "ReturnSome", graph: "Intra return n * r", trace: "intra" },
    tree: act("main", "Root", ["entry_main", "pp5"], act("f(2)", "Resume", ["entry_f", "pp0", "pp2", "pp3", "exit_f"], act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true))),
    text: "`return n * r` writes `#ret = 2`. The graph reaches `exit_f` again, this time for the outer activation.",
  },
  {
    line: "calla", edges: ["resume_main"], node: "pp6", store: "a = 2",
    residual: ["SKIP", CHECK], frames: [], rets: [], callers: [],
    rules: { source: "UnwindAct", graph: "Return", trace: "ret: Resume" },
    tree: act("main", "Resume", ["entry_main", "pp5", "pp6"], act("f(2)", "Resume", ["entry_f", "pp0", "pp2", "pp3", "exit_f"], act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true), true)),
    text: "The second `Resume` returns to `main` with `a = 2`. All three stacks are empty again, and `main`'s trace holds both calls, one inside the other.",
  },
  {
    line: "check", edges: [], node: "pp6", store: "a = 2",
    residual: [CHECK], frames: [], rets: [], callers: [],
    rules: { source: "Seq1", graph: "no step", trace: "no step" },
    tree: act("main", "Resume", ["entry_main", "pp5", "pp6"], act("f(2)", "Resume", ["entry_f", "pp0", "pp2", "pp3", "exit_f"], act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true), true)),
    text: "Another source step with no graph counterpart.",
  },
  {
    line: "check", edges: ["check"], node: "pp7", store: "a = 2",
    residual: ["SKIP"], frames: [], rets: [], callers: [],
    rules: { source: "Check", graph: "Intra check(a == 2)", trace: "intra" },
    tree: act("main", "Resume", ["entry_main", "pp5", "pp6", "pp7"], act("f(2)", "Resume", ["entry_f", "pp0", "pp2", "pp3", "exit_f"], act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true), true)),
    text: "The check runs in the store `a = 2`. That store is one element of `ltr_collect pp6`, the set the analysis result at `pp6` has to contain.",
  },
  {
    line: null, edges: ["ret_main"], node: "exit_main", store: "a = 2",
    residual: ["SKIP"], frames: [], rets: [], callers: [],
    rules: { source: "done (SKIP, s, [])", graph: "Intra return", trace: "intra" },
    tree: act("main", "Resume", ["entry_main", "pp5", "pp6", "pp7", "exit_main"], act("f(2)", "Resume", ["entry_f", "pp0", "pp2", "pp3", "exit_f"], act("f(1)", "Call", ["entry_f", "pp0", "pp1", "exit_f"], null, true), true)),
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
    line.addEventListener("pointerenter", () => light(line.dataset.nodes.split(" ").filter(Boolean)));
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

/* -------------------------------------------------------------------------- */
/* The proof chain                                                            */
/* -------------------------------------------------------------------------- */

/*
 * n at pp0 of the factorial program. Runs reach it with n = 2 and n = 1; the solver's
 * values are the interval analyzer's results under each context mode.
 */
const CHAIN = {
  none: {
    buckets: [{ label: "c = ()", members: [1, 2] }],
    gamma: [{ label: "c = ()", low: -Infinity, high: 2 }],
    sets: {
      source: "{n = 2, n = 1}",
      collect: "{n = 2, n = 1}",
      activation: "() ↦ {n = 2, n = 1}",
      gamma: "() ↦ n ∈ [−∞, 2]",
    },
    link: "one context, so the single bucket is the whole set",
    note: "With one context for all of `f`, the bucket and the collecting semantics coincide. The solver's value is `[−∞, 2]` because the entry of `f` was widened, so the abstraction admits every `n` below `1` although no run has one.",
  },
  entry: {
    buckets: [{ label: "c₁", members: [2] }, { label: "c₂", members: [1] }],
    gamma: [{ label: "c₁", low: 2, high: 2 }, { label: "c₂", low: 1, high: 1 }],
    sets: {
      source: "{n = 2, n = 1}",
      collect: "{n = 2, n = 1}",
      activation: "c₁ = [n ↦ [2,2]] ↦ {n = 2}   c₂ = [n ↦ [1,1]] ↦ {n = 1}",
      gamma: "c₁ ↦ n ∈ [2, 2]   c₂ ↦ n ∈ [1, 1]",
    },
    link: "every trace has a context, so the buckets together are exactly the set",
    note: "Each depth of the recursion has its own context, so the set splits into two buckets and each bucket gets an exact interval. No store enters between rungs 3 and 4, and the check in `main` is proved.",
  },
};

for (const figure of document.querySelectorAll(".scene-chain")) {
  const tabs = figure.querySelectorAll("[role=tab]");
  const low = -4;
  const high = 3;
  const x0 = 110;
  const dx = 58;
  const xOf = (n) => x0 + (n - low) * dx;

  const drawRung = (svg, rung, data) => {
    const reached = (n) => n === 1 || n === 2;
    svg.replaceChildren();

    const axis = document.createElementNS(SVG_NS, "line");
    axis.setAttribute("class", "axis");
    axis.setAttribute("x1", "40");
    axis.setAttribute("x2", String(xOf(high) + 30));
    axis.setAttribute("y1", "34");
    axis.setAttribute("y2", "34");
    svg.append(axis);

    const groups = rung === "activation" ? data.buckets.map((b) => ({ label: b.label, has: (n) => b.members.includes(n) }))
      : rung === "gamma" ? data.gamma.map((g) => ({ label: g.label, has: (n) => n >= g.low && n <= g.high, open: g.low === -Infinity }))
      : [];

    for (const group of groups) {
      const members = [];
      for (let n = low; n <= high; n++) {
        if (group.has(n)) members.push(n);
      }
      const left = group.open ? 26 : xOf(members[0]) - 18;
      const right = xOf(members[members.length - 1]) + 18;
      const band = document.createElementNS(SVG_NS, "rect");
      band.setAttribute("class", "chain-band");
      band.setAttribute("x", String(left));
      band.setAttribute("y", "20");
      band.setAttribute("width", String(right - left));
      band.setAttribute("height", "28");
      band.setAttribute("rx", "14");
      svg.append(band);

      const label = document.createElementNS(SVG_NS, "text");
      label.setAttribute("class", "chain-band-label");
      label.setAttribute("x", String((left + right) / 2));
      label.setAttribute("y", "13");
      label.textContent = group.label;
      svg.append(label);
    }

    const inAny = (n) => groups.some((g) => g.has(n));

    for (let n = low; n <= high; n++) {
      const circle = document.createElementNS(SVG_NS, "circle");
      const kind = reached(n) ? "in" : rung === "gamma" && inAny(n) ? "extra" : "out";
      circle.setAttribute("cx", String(xOf(n)));
      circle.setAttribute("cy", "34");
      circle.setAttribute("r", kind === "out" ? "4" : "8");
      circle.setAttribute("class", `dot-${kind}`);
      svg.append(circle);

      const tick = document.createElementNS(SVG_NS, "text");
      tick.setAttribute("class", "chain-tick");
      tick.setAttribute("x", String(xOf(n)));
      tick.setAttribute("y", "62");
      tick.textContent = String(n);
      svg.append(tick);
    }

    const minus = document.createElementNS(SVG_NS, "text");
    minus.setAttribute("class", "chain-tick");
    minus.setAttribute("x", "40");
    minus.setAttribute("y", "62");
    minus.textContent = "−∞";
    svg.append(minus);
  };

  const render = (mode) => {
    const data = CHAIN[mode];
    figure.dataset.mode = mode;
    tabs.forEach((tab) => tab.setAttribute("aria-selected", String(tab.dataset.mode === mode)));

    for (const rung of figure.querySelectorAll(".chain-rung")) {
      drawRung(rung.querySelector("svg"), rung.dataset.rung, data);
      rung.querySelector(".chain-set").textContent = data.sets[rung.dataset.rung];
    }

    for (const link of figure.querySelectorAll("[data-mode-link]")) {
      link.hidden = link.dataset.modeLink !== mode;
    }

    figure.querySelector(".chain-link-note").textContent = data.link;
    figure.querySelector(".chain-note").innerHTML = withCode(data.note);
  };

  tabs.forEach((tab) => tab.addEventListener("click", () => render(tab.dataset.mode)));
  render(figure.dataset.mode);
}

/* -------------------------------------------------------------------------- */
/* A map of the proof                                                         */
/* -------------------------------------------------------------------------- */

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

/* -------------------------------------------------------------------------- */
/* Take a pillar away                                                         */
/* -------------------------------------------------------------------------- */

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

  const place = (x, y) => run.setAttribute("transform", `translate(${x.toFixed(1)} ${y.toFixed(1)})`);

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
      segment.style.transform = leftGone && rightGone ? "translateY(150px)"
        : rightGone ? "rotate(24deg)"
        : leftGone ? "rotate(-24deg)"
        : "none";
      segment.classList.toggle("is-broken", leftGone || rightGone);
    });

    caption.innerHTML = order.length ? order.map((k) => `<span>${withCode(BRIDGE_FAILURES[k])}</span>`).join("") : idle;
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
      const falling = first && x >= stop ? (t - (stop - 40) / 150) : 0;
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
    pillar.addEventListener("click", () => figure.querySelector(`.bridge-toggles [data-pillar="${pillar.dataset.pillar}"]`).click());
  }

  render();

  if (reducedMotion) {
    place(926, 124);
  } else {
    requestAnimationFrame(frame);
  }
}

/* -------------------------------------------------------------------------- */
/* Zoom into one PROVED                                                       */
/* -------------------------------------------------------------------------- */

for (const figure of document.querySelectorAll(".scene-zoom")) {
  const levels = [...figure.querySelectorAll(".zoom-level")];
  const gauge = figure.querySelectorAll(".zoom-gauge [data-goto]");
  const range = figure.querySelector(".zoom-range");
  let level = 0;

  const show = (next) => {
    level = Math.max(0, Math.min(levels.length - 1, next));
    figure.dataset.level = String(level);
    range.value = String(level);

    levels.forEach((card, i) => {
      card.classList.toggle("is-current", i === level);
      card.classList.toggle("is-above", i === level - 1);
      card.classList.toggle("is-past", i < level - 1);
      card.classList.toggle("is-below", i > level);
      card.setAttribute("aria-hidden", String(i !== level));
    });

    gauge.forEach((button) => {
      const i = Number(button.dataset.goto);
      button.setAttribute("aria-pressed", String(i === level));
      button.classList.toggle("is-passed", i < level);
    });
  };

  gauge.forEach((button) => button.addEventListener("click", () => show(Number(button.dataset.goto))));
  figure.querySelector(".zoom-in").addEventListener("click", () => show(level + 1));
  figure.querySelector(".zoom-out").addEventListener("click", () => show(level - 1));
  range.addEventListener("input", () => show(Number(range.value)));
  figure.querySelector(".zoom-controls").hidden = false;
  figure.classList.add("is-interactive");
  show(0);
}
