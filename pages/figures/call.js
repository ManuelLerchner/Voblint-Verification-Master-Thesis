{
  /* Values are the interval analyzer's results for the factorial program, per context mode. */
  const CALL_VALUES = {
    entry: {
      caller: "a = ⊤",
      entry: "n = [2, 2]",
      ctx: "c' = [n ↦ [2,2]]",
      seed: "n = [2, 2]",
      exit: "#ret = [2, 2]",
      after: "a = [2, 2]",
    },
    none: {
      caller: "a = ⊤",
      entry: "n = [2, 2]",
      ctx: "c' = ()",
      seed: "n = [−∞, 2]",
      exit: "#ret = ⊤",
      after: "a = ⊤",
    },
  };

  const CALL_STAGES = [
    {
      text: "The caller's state at the call site `pp5`, read from the solver's current values. `a` is a local of `main` that nothing has assigned yet, so it may hold any integer.",
      obligation: "Read by `QueryL (pp5, c)`.",
    },
    {
      text: "`enter` evaluates the argument `2` in the caller's state and binds it to `n`. It returns a list of alternatives, each a continuation state paired with an entry state; the interval analysis returns one.",
      obligation:
        "Obligation `enter_sound_local`: for every caller store in `γ`, some alternative's entry state covers the concrete `call_enter`.",
    },
    {
      text: {
        entry:
          "Entry-state contexts use the entry state as the key: `c' = [n ↦ [2, 2]]`. The recursive call `f(n - 1)` enters with `n = [1, 1]` and gets a key of its own.",
        none: "No context: every call of `f`, from `main` or from `f` itself, uses the single key `()`.",
      },
      obligation:
        "Obligation `routed_entry_cover`: the key the policy picks is one the semantics admits for this entry.",
    },
    {
      text: {
        entry:
          "The entry state goes, as a side effect, to the global unknown `Seed entry_f c'`, which only this call writes. It holds `n = [2, 2]`.",
        none: "The entry state goes to `Seed entry_f ()`. The recursive call writes `n = 1` into the same key, the lower bound moves, and warrowing widens the value to `[−∞, 2]`.",
      },
      obligation:
        "The published value stays below `σ` at the seed, which the post-solution guarantees (`routed_seed_publish_bound_seed`).",
    },
    {
      text: {
        entry:
          "The call reads the callee's exit under the same key. `f(2)` returns `2 * 1`, so `#ret = [2, 2]`.",
        none: "The one exit of `f` covers every activation, including ones with the values of `n` that widening added, so the return value is `⊤`.",
      },
      obligation:
        "Obligation `routed_context_comb`: the exit state read here covers the concrete callee's final store.",
    },
    {
      text: {
        entry:
          "`combine` keeps the caller's locals, takes the callee's globals and writes `#ret` into `a`: `a = [2, 2]` at `pp6`, and `a == 2` is PROVED.",
        none: "`combine` writes `⊤` into `a`, and `a == 2` is UNKNOWN. That answer is imprecise but sound: `⊤` contains `2`.",
      },
      obligation:
        "Obligation `combine_sound`: `combine_collect` of a covered caller store and a covered callee store is covered.",
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
        tabs.forEach((other) => {
          other.setAttribute("aria-selected", String(other === tab));
        });
        render(current);
      });
    }
  }
}
