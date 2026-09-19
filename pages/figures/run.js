{
  /*
   * One entry per source step of the factorial run, with the graph steps csim_step matches
   * it to and the trace constructors valid_ltr applies. Residuals flatten the nested Seq;
   * trees list each activation's path, its live callee and whether it has returned.
   */
  const FRAME_MAIN = "Frame {x = ?} x";
  const FRAME_S2 = "Frame {n = 2, m = 0, r = 0} m";
  const FRAME_S1 = "Frame {n = 1, m = 0, r = 0} m";
  const RET_MAIN = "(pp10, x, {x = ?})";
  const RET_S2 = "(pp6, m, {n = 2, m = 0, r = 0})";
  const RET_S2b = "(pp7, r, {n = 2, m = 1, r = 0})";
  const RET_S1 = "(pp6, m, {n = 1, m = 0, r = 0})";
  const RET_S1b = "(pp7, r, {n = 1, m = 0, r = 0})";
  const CHECK = "check(x == 3)";

  /* `kept` are the callees that have returned; a `Resume` holds on to them, so they stay
     drawn inside the activation that made the call. */
  const act = (name, ctor, path, child = null, done = false, kept = []) => ({
    name,
    ctor,
    path,
    child,
    done,
    kept,
  });

  const RUN_STEPS = [
    {
      entry: "x = ?",
      line: "callsum",
      edges: ["body_main"],
      node: "pp9",
      store: "x = ?",
      residual: ["x = sum(2)", CHECK],
      frames: [],
      rets: [],
      callers: [],
      rules: {
        source: "start (main body, s₀, [])",
        graph: "Intra body(main)",
        trace: "Root, intra",
      },
      tree: act("main", "Root", ["entry_main", "pp9"], null, false, []),
      text: "**Source**: the rest of the program is `x = sum(2)` then the check, with no frames yet. **CFG**: `main`'s body edge has been taken, so the run sits at `pp9`. **Trace**: a single `Root` activation whose path is `entry_main`, `pp9`.",
    },
    {
      entry: "n = 2, m = 0, r = 0",
      line: "if",
      edges: ["call_main", "body_sum"],
      node: "pp2",
      store: "n = 2, m = 0, r = 0",
      residual: ["if (n < 1) …", "m = dec(n)", "r = sum(m)", "return r + n", "Restore", CHECK],
      frames: [FRAME_MAIN],
      rets: [RET_MAIN],
      callers: ["main"],
      rules: { source: "Call", graph: "Call, Intra body(sum)", trace: "call, intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act("sum(2)", "Call", ["entry_sum", "pp2"], null, false, []),
        false,
        [],
      ),
      text: "**Source**: `Call` evaluates `2`, binds it to `n` in a fresh store and pushes a frame that remembers `main`'s store and the destination `x`. **CFG**: the call edge into `entry_sum`, then `sum`'s body edge, with `pp10` pushed as the return point. **Trace**: a `Call` activation opens under the root. All three stacks grew by exactly one.",
    },
    {
      entry: "n = 2, m = 0, r = 0",
      line: "mdec",
      edges: ["ge"],
      node: "pp5",
      store: "n = 2, m = 0, r = 0",
      residual: ["m = dec(n)", "r = sum(m)", "return r + n", "Restore", CHECK],
      frames: [FRAME_MAIN],
      rets: [RET_MAIN],
      callers: ["main"],
      rules: { source: "IfFalse", graph: "Intra ¬ n < 1", trace: "intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act("sum(2)", "Call", ["entry_sum", "pp2", "pp5"], null, false, []),
        false,
        [],
      ),
      text: "**Source**: `IfFalse` drops the then-branch, leaving `m = dec(n)` next. **CFG**: the `¬ n < 1` edge to `pp5`. **Trace**: the same activation extends its path. Nothing pushed anywhere: a branch happens inside one activation.",
    },
    {
      entry: "x = 2",
      line: "retdec",
      edges: ["call_dec", "body_dec"],
      node: "pp0",
      store: "x = 2",
      residual: ["return x - 1", "Restore", "r = sum(m)", "return r + n", "Restore", CHECK],
      frames: [FRAME_S2, FRAME_MAIN],
      rets: [RET_S2, RET_MAIN],
      callers: ["sum(2)", "main"],
      rules: { source: "Call", graph: "Call, Intra body(dec)", trace: "call, intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Call",
          ["entry_sum", "pp2", "pp5"],
          act("dec(2)", "Call", ["entry_dec", "pp0"], null, false, []),
          false,
          [],
        ),
        false,
        [],
      ),
      text: "**Source**: a second `Call`, this time binding `2` to `dec`'s `x`, so the frame stack is three deep. **CFG**: the call edge to `entry_dec` and `dec`'s body edge, with `pp6` pushed. **Trace**: a `Call` nested inside the one for `sum(2)`.",
    },
    {
      entry: "x = 2",
      line: "retdec",
      edges: ["ret_dec"],
      node: "exit_dec",
      store: "x = 2",
      residual: ["Restore", "r = sum(m)", "return r + n", "Restore", CHECK],
      frames: [FRAME_S2, FRAME_MAIN],
      rets: [RET_S2, RET_MAIN],
      callers: ["sum(2)", "main"],
      rules: { source: "Return", graph: "Intra return x - 1", trace: "intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Call",
          ["entry_sum", "pp2", "pp5"],
          act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, false, []),
          false,
          [],
        ),
        false,
        [],
      ),
      text: "**Source**: `Return` leaves `Restore` at the head of the program. **CFG**: the `return x - 1` edge lands on `exit_dec`. **Trace**: the innermost activation's path now ends at its exit. Nothing has popped on any side yet.",
    },
    {
      entry: "n = 2, m = 0, r = 0",
      line: "rsum",
      edges: ["resume_dec"],
      node: "pp6",
      store: "n = 2, m = 1, r = 0",
      residual: ["r = sum(m)", "return r + n", "Restore", CHECK],
      frames: [FRAME_MAIN],
      rets: [RET_MAIN],
      callers: ["main"],
      rules: { source: "Restore", graph: "Resume m := dec(n)", trace: "resume" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act("sum(2)", "Resume", ["entry_sum", "pp2", "pp5", "pp6"], null, false, [
          act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
        ]),
        false,
        [],
      ),
      text: "**Source**: `Restore` pops the frame and writes `1` into `m`. **CFG**: the resume edge back to `pp6`, popping the return point. **Trace**: `dec(2)` is finished and kept inside a `Resume`. This is the pop the recursion has not reached yet.",
    },
    {
      entry: "n = 1, m = 0, r = 0",
      line: "if",
      edges: ["call_sum", "body_sum"],
      node: "pp2",
      store: "n = 1, m = 0, r = 0",
      residual: [
        "if (n < 1) …",
        "m = dec(n)",
        "r = sum(m)",
        "return r + n",
        "Restore",
        "return r + n",
        "Restore",
        CHECK,
      ],
      frames: [FRAME_S2, FRAME_MAIN],
      rets: [RET_S2b, RET_MAIN],
      callers: ["sum(2)", "main"],
      rules: { source: "Call", graph: "Call, Intra body(sum)", trace: "call, intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Resume",
          ["entry_sum", "pp2", "pp5", "pp6"],
          act("sum(1)", "Call", ["entry_sum", "pp2"], null, false, []),
          false,
          [act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, [])],
        ),
        false,
        [],
      ),
      text: "**Source**: the recursive `Call`, binding `1` to a fresh `n`. **CFG**: the call edge into `entry_sum` again, the very same node as the first activation. **Trace**: a `Call` nested inside the `Resume`, so the finished `dec(2)` is still there beneath it.",
    },
    {
      entry: "n = 1, m = 0, r = 0",
      line: "mdec",
      edges: ["ge"],
      node: "pp5",
      store: "n = 1, m = 0, r = 0",
      residual: [
        "m = dec(n)",
        "r = sum(m)",
        "return r + n",
        "Restore",
        "return r + n",
        "Restore",
        CHECK,
      ],
      frames: [FRAME_S2, FRAME_MAIN],
      rets: [RET_S2b, RET_MAIN],
      callers: ["sum(2)", "main"],
      rules: { source: "IfFalse", graph: "Intra ¬ n < 1", trace: "intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Resume",
          ["entry_sum", "pp2", "pp5", "pp6"],
          act("sum(1)", "Call", ["entry_sum", "pp2", "pp5"], null, false, []),
          false,
          [act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, [])],
        ),
        false,
        [],
      ),
      text: "**Source**: `IfFalse` again, since `1 < 1` does not hold. **CFG**: the `¬ n < 1` edge to `pp5`. **Trace**: the live activation extends its path, and the stacks stay where they are.",
    },
    {
      entry: "x = 1",
      line: "retdec",
      edges: ["call_dec", "body_dec", "ret_dec"],
      node: "exit_dec",
      store: "x = 1",
      residual: [
        "Restore",
        "r = sum(m)",
        "return r + n",
        "Restore",
        "return r + n",
        "Restore",
        CHECK,
      ],
      frames: [FRAME_S1, FRAME_S2, FRAME_MAIN],
      rets: [RET_S1, RET_S2b, RET_MAIN],
      callers: ["sum(1)", "sum(2)", "main"],
      rules: {
        source: "Call, Return",
        graph: "Call, Intra body(dec), Intra return",
        trace: "call, intra",
      },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Resume",
          ["entry_sum", "pp2", "pp5", "pp6"],
          act(
            "sum(1)",
            "Call",
            ["entry_sum", "pp2", "pp5"],
            act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, false, []),
            false,
            [],
          ),
          false,
          [act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, [])],
        ),
        false,
        [],
      ),
      text: "**Source**: `Call` then `Return`, so `dec` is entered and finished in one move. **CFG**: the call edge, `dec`'s body and its return edge. **Trace**: a fourth activation, the deepest the run gets.",
    },
    {
      entry: "n = 1, m = 0, r = 0",
      line: "rsum",
      edges: ["resume_dec"],
      node: "pp6",
      store: "n = 1, m = 0, r = 0",
      residual: ["r = sum(m)", "return r + n", "Restore", "return r + n", "Restore", CHECK],
      frames: [FRAME_S2, FRAME_MAIN],
      rets: [RET_S2b, RET_MAIN],
      callers: ["sum(2)", "main"],
      rules: { source: "Restore", graph: "Resume m := dec(n)", trace: "resume" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Resume",
          ["entry_sum", "pp2", "pp5", "pp6"],
          act("sum(1)", "Resume", ["entry_sum", "pp2", "pp5", "pp6"], null, false, [
            act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
          ]),
          false,
          [act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, [])],
        ),
        false,
        [],
      ),
      text: "**Source**: `Restore` writes `0` into `m` and pops. **CFG**: the resume edge to `pp6`. **Trace**: the second `dec` closes into a `Resume`. Push, pop, push again: a run is not a stack that only grows.",
    },
    {
      entry: "n = 0, m = 0, r = 0",
      line: "if",
      edges: ["call_sum", "body_sum"],
      node: "pp2",
      store: "n = 0, m = 0, r = 0",
      residual: ["if (n < 1) …", "return r + n", "Restore", "return r + n", "Restore", CHECK],
      frames: [FRAME_S1, FRAME_S2, FRAME_MAIN],
      rets: [RET_S1b, RET_S2b, RET_MAIN],
      callers: ["sum(1)", "sum(2)", "main"],
      rules: { source: "Call", graph: "Call, Intra body(sum)", trace: "call, intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Resume",
          ["entry_sum", "pp2", "pp5", "pp6"],
          act(
            "sum(1)",
            "Resume",
            ["entry_sum", "pp2", "pp5", "pp6"],
            act("sum(0)", "Call", ["entry_sum", "pp2"], null, false, []),
            false,
            [act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, [])],
          ),
          false,
          [act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, [])],
        ),
        false,
        [],
      ),
      text: "**Source**: the third `Call` of `sum`, with `n` bound to `0`. **CFG**: the same `entry_sum` and the same body edge as the other two. **Trace**: `Call (Call (Root …) …) …`. The nesting lives in the trace, not in the graph.",
    },
    {
      entry: "n = 0, m = 0, r = 0",
      line: "ret0",
      edges: ["lt", "ret0"],
      node: "exit_sum",
      store: "n = 0, m = 0, r = 0",
      residual: [
        "return 0",
        "Restore",
        "return r + n",
        "Restore",
        "return r + n",
        "Restore",
        CHECK,
      ],
      frames: [FRAME_S1, FRAME_S2, FRAME_MAIN],
      rets: [RET_S1b, RET_S2b, RET_MAIN],
      callers: ["sum(1)", "sum(2)", "main"],
      rules: { source: "IfTrue, Return", graph: "Intra n < 1, Intra return 0", trace: "intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Resume",
          ["entry_sum", "pp2", "pp5", "pp6"],
          act(
            "sum(1)",
            "Resume",
            ["entry_sum", "pp2", "pp5", "pp6"],
            act("sum(0)", "Call", ["entry_sum", "pp2", "pp3", "exit_sum"], null, false, []),
            false,
            [act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, [])],
          ),
          false,
          [act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, [])],
        ),
        false,
        [],
      ),
      text: "**Source**: `IfTrue` this time, and `Return` hands back `0`. **CFG**: the `n < 1` edge to `pp3` and the `return 0` edge to `exit_sum`. **Trace**: this activation's path ends at the exit and the recursion stops growing.",
    },
    {
      entry: "n = 1, m = 0, r = 0",
      line: "retn",
      edges: ["resume_sum"],
      node: "pp7",
      store: "n = 1, m = 0, r = 0",
      residual: ["return r + n", "Restore", "return r + n", "Restore", CHECK],
      frames: [FRAME_S2, FRAME_MAIN],
      rets: [RET_S2b, RET_MAIN],
      callers: ["sum(2)", "main"],
      rules: { source: "Restore", graph: "Resume r := sum(m)", trace: "resume" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Resume",
          ["entry_sum", "pp2", "pp5", "pp6"],
          act("sum(1)", "Resume", ["entry_sum", "pp2", "pp5", "pp6", "pp7"], null, false, [
            act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
            act("sum(0)", "Call", ["entry_sum", "pp2", "pp3", "exit_sum"], null, true, []),
          ]),
          false,
          [act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, [])],
        ),
        false,
        [],
      ),
      text: "**Source**: `Restore` writes `0` into `r` and pops a frame. **CFG**: the resume edge to `pp7`. **Trace**: `sum(0)` is retained, finished, inside a `Resume`.",
    },
    {
      entry: "n = 1, m = 0, r = 0",
      line: "retn",
      edges: ["retn"],
      node: "exit_sum",
      store: "n = 1, m = 0, r = 0",
      residual: ["return r + n", "Restore", "return r + n", "Restore", CHECK],
      frames: [FRAME_S2, FRAME_MAIN],
      rets: [RET_S2b, RET_MAIN],
      callers: ["sum(2)", "main"],
      rules: { source: "Return", graph: "Intra return r + n", trace: "intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Resume",
          ["entry_sum", "pp2", "pp5", "pp6"],
          act(
            "sum(1)",
            "Resume",
            ["entry_sum", "pp2", "pp5", "pp6", "pp7", "exit_sum"],
            null,
            false,
            [
              act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
              act("sum(0)", "Call", ["entry_sum", "pp2", "pp3", "exit_sum"], null, true, []),
            ],
          ),
          false,
          [act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, [])],
        ),
        false,
        [],
      ),
      text: "**Source**: `Return` evaluates `r + n` to `1`. **CFG**: the `return r + n` edge to `exit_sum`, the same exit all three activations use. **Trace**: the path of `sum(1)` now ends there too.",
    },
    {
      entry: "n = 2, m = 0, r = 0",
      line: "retn",
      edges: ["resume_sum"],
      node: "pp7",
      store: "n = 2, m = 1, r = 1",
      residual: ["return r + n", "Restore", CHECK],
      frames: [FRAME_MAIN],
      rets: [RET_MAIN],
      callers: ["main"],
      rules: { source: "Restore", graph: "Resume r := sum(m)", trace: "resume" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act("sum(2)", "Resume", ["entry_sum", "pp2", "pp5", "pp6", "pp7"], null, false, [
          act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
          act(
            "sum(1)",
            "Resume",
            ["entry_sum", "pp2", "pp5", "pp6", "pp7", "exit_sum"],
            null,
            true,
            [
              act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
              act("sum(0)", "Call", ["entry_sum", "pp2", "pp3", "exit_sum"], null, true, []),
            ],
          ),
        ]),
        false,
        [],
      ),
      text: "**Source**: `Restore` writes `1` into `r` in `sum(2)` and pops. **CFG**: the resume edge to `pp7`. **Trace**: `sum(1)` closes into a `Resume`, carrying `sum(0)` inside it.",
    },
    {
      entry: "n = 2, m = 0, r = 0",
      line: "retn",
      edges: ["retn"],
      node: "exit_sum",
      store: "n = 2, m = 1, r = 1",
      residual: ["return r + n", "Restore", CHECK],
      frames: [FRAME_MAIN],
      rets: [RET_MAIN],
      callers: ["main"],
      rules: { source: "Return", graph: "Intra return r + n", trace: "intra" },
      tree: act(
        "main",
        "Root",
        ["entry_main", "pp9"],
        act(
          "sum(2)",
          "Resume",
          ["entry_sum", "pp2", "pp5", "pp6", "pp7", "exit_sum"],
          null,
          false,
          [
            act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
            act(
              "sum(1)",
              "Resume",
              ["entry_sum", "pp2", "pp5", "pp6", "pp7", "exit_sum"],
              null,
              true,
              [
                act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
                act("sum(0)", "Call", ["entry_sum", "pp2", "pp3", "exit_sum"], null, true, []),
              ],
            ),
          ],
        ),
        false,
        [],
      ),
      text: "**Source**: `Return` evaluates `r + n` to `3`. **CFG**: the `return r + n` edge to `exit_sum`. **Trace**: the outermost `sum` activation reaches its exit.",
    },
    {
      entry: "x = ?",
      line: "check",
      edges: ["resume_main"],
      node: "pp10",
      store: "x = 3",
      residual: [CHECK],
      frames: [],
      rets: [],
      callers: [],
      rules: { source: "Restore", graph: "Resume x := sum(2)", trace: "resume" },
      tree: act("main", "Resume", ["entry_main", "pp9", "pp10"], null, false, [
        act("sum(2)", "Resume", ["entry_sum", "pp2", "pp5", "pp6", "pp7", "exit_sum"], null, true, [
          act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
          act(
            "sum(1)",
            "Resume",
            ["entry_sum", "pp2", "pp5", "pp6", "pp7", "exit_sum"],
            null,
            true,
            [
              act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
              act("sum(0)", "Call", ["entry_sum", "pp2", "pp3", "exit_sum"], null, true, []),
            ],
          ),
        ]),
      ]),
      text: "**Source**: the last `Restore` pops the final frame and writes `3` into `x`. **CFG**: the resume edge to `pp10`. **Trace**: the whole call tree survives inside the root's `Resume`, and every stack is empty again.",
    },
    {
      entry: "x = ?",
      line: "check",
      edges: ["check"],
      node: "pp11",
      store: "x = 3",
      residual: ["SKIP"],
      frames: [],
      rets: [],
      callers: [],
      rules: { source: "Check", graph: "Intra check(x == 3)", trace: "intra" },
      tree: act("main", "Resume", ["entry_main", "pp9", "pp10", "pp11"], null, false, [
        act("sum(2)", "Resume", ["entry_sum", "pp2", "pp5", "pp6", "pp7", "exit_sum"], null, true, [
          act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
          act(
            "sum(1)",
            "Resume",
            ["entry_sum", "pp2", "pp5", "pp6", "pp7", "exit_sum"],
            null,
            true,
            [
              act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
              act("sum(0)", "Call", ["entry_sum", "pp2", "pp3", "exit_sum"], null, true, []),
            ],
          ),
        ]),
      ]),
      text: "**Source**: `Check` runs in the store `x = 3`. **CFG**: the check edge to `pp11`. **Trace**: the root's path reaches `pp10`, so this store belongs to what a sound answer at `pp10` must contain.",
    },
    {
      entry: "x = ?",
      line: null,
      edges: ["ret_main"],
      node: "exit_main",
      store: "x = 3",
      residual: ["SKIP"],
      frames: [],
      rets: [],
      callers: [],
      rules: { source: "done (SKIP, s, [])", graph: "Intra return", trace: "intra" },
      tree: act("main", "Resume", ["entry_main", "pp9", "pp10", "pp11", "exit_main"], null, false, [
        act("sum(2)", "Resume", ["entry_sum", "pp2", "pp5", "pp6", "pp7", "exit_sum"], null, true, [
          act("dec(2)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
          act(
            "sum(1)",
            "Resume",
            ["entry_sum", "pp2", "pp5", "pp6", "pp7", "exit_sum"],
            null,
            true,
            [
              act("dec(1)", "Call", ["entry_dec", "pp0", "exit_dec"], null, true, []),
              act("sum(0)", "Call", ["entry_sum", "pp2", "pp3", "exit_sum"], null, true, []),
            ],
          ),
        ]),
      ]),
      text: "**Source**: nothing is left to do. **CFG**: `main`'s implicit return edge still fires, landing on `exit_main`. **Trace**: the root's path ends at the exit, which is where `source_completes_ltr_collect_exit` puts the final store.",
    },
  ];

  /* What the observers answer about this one activation. The store is only known for the
     activation the run is currently inside, so the others say what they can. */
  function observerTitle(a, sink, store, caller) {
    const end = a.path[a.path.length - 1];
    const lines = [
      `path t = ${a.path.length} nodes, ${a.path.join(" -> ")}`,
      `sink_node t = ${end}`,
      a === sink ? `sink_store t = {${store}}` : "sink_store t = the store it ended with",
      `caller_of t = ${caller ?? "None"}`,
    ];
    return lines.join("\n");
  }

  function renderActivation(a, sink, store, caller = null) {
    const box = document.createElement("div");
    box.className = "run-act";
    box.classList.toggle("is-done", a.done);
    box.classList.toggle("is-sink", a === sink);
    box.title = observerTitle(a, sink, store, caller);

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

    for (const done of a.kept ?? []) {
      box.append(renderActivation(done, sink, store, a.name));
    }

    if (a.child) {
      box.append(renderActivation(a.child, sink, store, a.name));
    }

    return box;
  }

  function sinkOf(a) {
    return a.child && !a.child.done ? sinkOf(a.child) : a;
  }

  /* Newest entry on top, oldest resting on the floor, so the two stacks can be read
     against each other entry by entry. */
  function fillStack(list, items, empty) {
    list.replaceChildren(
      ...(items.length ? items : [empty]).map((text, i) => {
        const item = document.createElement("li");
        if (items.length) {
          const depth = document.createElement("span");
          depth.className = "run-depth";
          depth.textContent = String(items.length - i);
          item.append(depth);
        }
        const body = document.createElement("span");
        body.className = "run-slab";
        body.innerHTML = withCode(`\`${text}\``);
        item.append(body);
        item.classList.toggle("empty", !items.length);
        item.classList.toggle("top", Boolean(items.length) && i === 0);
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

      tree.replaceChildren(renderActivation(state.tree, sinkOf(state.tree), state.store));

      for (const [kind, text] of Object.entries(state.rules ?? {})) {
        const rule = figure.querySelector(`[data-rule="${kind}"]`);
        if (rule) {
          rule.textContent = text;
          rule.classList.toggle("none", text === "no step");
        }
      }

      figure.querySelector(".run-store").textContent = `{${state.store}}`;
      /* The commentary is one sentence per pillar, laid out under the pillar it is about. */
      const said = state.text.split(/\*\*(Source|CFG|Trace)\*\*:\s*/).filter(Boolean);
      if (said.length === 6) {
        caption.replaceChildren(
          ...[0, 2, 4].map((i) => {
            const cell = document.createElement("p");
            cell.className = "run-say";
            cell.innerHTML = `<b>${said[i]}</b> ${withCode(said[i + 1].trim())}`;
            return cell;
          }),
        );
        caption.classList.add("is-split");
      } else {
        caption.classList.remove("is-split");
        caption.innerHTML = withCode(state.text);
      }
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

  /* The same code-and-graph pair with no run on it: hovering a line still lights its nodes. */
  for (const figure of document.querySelectorAll(".scene-cfgmap")) {
    const nodes = figure.querySelectorAll(".run-nodes [data-node]");
    for (const line of figure.querySelectorAll(".run-code [data-nodes]")) {
      const names = line.dataset.nodes.split(" ").filter(Boolean);
      const light = (on) => {
        for (const node of nodes) {
          node.classList.toggle("is-hover", on && names.includes(node.dataset.node));
        }
      };
      line.addEventListener("pointerenter", () => light(true));
      line.addEventListener("pointerleave", () => light(false));
    }
  }
}
