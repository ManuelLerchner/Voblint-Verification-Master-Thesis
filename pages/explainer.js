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
