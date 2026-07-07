# Interval executable witnesses and runs

Executable demonstrations of the interval analysis, running the vendored `TD_side`
solver via the code generator. Demonstrations, not part of the domain definition
(which lives one level up in `Instances/Interval/`).

- `Exec_Ivl_Run` — codegen probe + solver run; also the update-rule menu (`run_menu`)
  comparison (`loop_head_across_update_rules`).
- `Exec_Ivl_Ctx_Run` / `Exec_Ivl_Ctx_Gen_Run` — earlier context-sensitive runs (fixed
  contexts). Largely superseded by the flagship below, which does value-derived contexts
  end-to-end; kept as the smaller fixed-context witnesses.
- `Exec_Ivl_Mode_Compiled_Run` — the value-derived digest flagship at the interval
  domain (sibling of Sign's `Exec_Sign_Mode_Compiled_Run`): a program with a **while
  loop** and procedure calls, contexts projected from an ordinary local via
  `ivl_decode` (a numeric-threshold bucket), showing the digest keeps `G` in separate
  partitions (`[0,5]` / `[9,9]`) where the context-blind read merges to `[0,9]`. The
  second dissimilar instance of the generic `value_digest_reader` kernel. Also carries:
  the update-rule menu (`iv_digest_across_update_rules`), a **proven-sound** widening
  loop (`wide_abstracts`), and GraphViz output — `wide_dot` (annotated per-node
  intervals) and `iv_digest_dot` (context-clustered, one cluster per digest mode with
  its separated `G`), both via the generic `show_val` renderers.
