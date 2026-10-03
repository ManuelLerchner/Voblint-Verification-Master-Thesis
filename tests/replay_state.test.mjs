// The replay reducer (pages/replay_state.js) on hand-written schema 2 event
// streams. Needs no build: `node --test tests/replay_state.test.mjs`.

import assert from "node:assert/strict";
import { test } from "node:test";

import { sharedGlobalValues, sharedWriteHint } from "../pages/shared-hints.js";

import {
  checkAgainstResult,
  copyState,
  createCache,
  emptyState,
  localKey,
  reduce,
} from "../pages/replay_state.js";

const unit = { kind: "unit" };
const L = (node) => ({ kind: "local", node, context: unit });
const G = { kind: "program_global", name: "g" };
const key = (node) => localKey(L(node));

// exit queries a loop head that queries itself (a widening point), then the loop head
// changes, destabilizing exit, which is evaluated again.
const stream = [
  { event: "start", unknown: L("exit_main") },
  { event: "iterate", unknown: L("exit_main"), called: true, stable: false, wpoint: false },
  { event: "solve", unknown: L("exit_main") },
  { event: "eq", unknown: L("exit_main") },
  { event: "stable_add", unknown: L("exit_main") },
  { event: "query_local", current: L("exit_main"), target: L("pp1") },
  { event: "iterate", unknown: L("pp1"), called: true, stable: false, wpoint: false },
  { event: "solve", unknown: L("pp1") },
  { event: "eq", unknown: L("pp1") },
  { event: "stable_add", unknown: L("pp1") },
  { event: "query_local", current: L("pp1"), target: L("pp1") },
  { event: "wpoint_add", unknown: L("pp1") },
  { event: "add_infl", unknown: L("pp1"), reader: L("pp1") },
  { event: "value_local", current: L("pp1"), target: L("pp1"), value: "⊥" },
  { event: "side", current: L("pp1"), target: G, value: "1" },
  { event: "update_global", unknown: G, old: "⊥", new: "1" },
  { event: "destabilize", unknown: G },
  { event: "answer", current: L("pp1"), value: "[0,0]" },
  { event: "widen", unknown: L("pp1") },
  { event: "update_local", unknown: L("pp1"), old: "⊥", new: "[0,0]" },
  { event: "destabilize", unknown: L("pp1") },
  { event: "stable_remove", unknown: L("pp1") },
  { event: "iterate", unknown: L("pp1"), called: true, stable: false, wpoint: true },
  { event: "resolve", unknown: L("pp1") },
  { event: "eq", unknown: L("pp1") },
  { event: "stable_add", unknown: L("pp1") },
  { event: "answer", current: L("pp1"), value: "[0,0]" },
  { event: "wpoint_remove", unknown: L("pp1") },
  { event: "add_infl", unknown: L("pp1"), reader: L("exit_main") },
  { event: "value_local", current: L("exit_main"), target: L("pp1"), value: "[0,0]" },
  { event: "answer", current: L("exit_main"), value: "[0,0]" },
  { event: "update_local", unknown: L("exit_main"), old: "⊥", new: "[0,0]" },
].map((event, index) => ({ step: index + 1, ...event }));

function fold(events) {
  return events.reduce(reduce, emptyState());
}

test("the reducer leaves its argument alone", () => {
  const before = emptyState();
  const after = reduce(before, stream[0]);

  assert.equal(before.stack.length, 0);
  assert.deepEqual(after.stack, [key("exit_main")]);
});

test("queries nest: the stack is the root and the open queries", () => {
  const at = (n) => fold(stream.slice(0, n)).stack;

  assert.deepEqual(at(11), [key("exit_main"), key("pp1"), key("pp1")]);
  assert.deepEqual(at(14), [key("exit_main"), key("pp1")]);
  assert.deepEqual(fold(stream).stack, [key("exit_main")]);
  assert.deepEqual(fold(stream).problems, []);
});

test("stable set only from stable_add and stable_remove", () => {
  const mid = fold(stream.slice(0, 22));

  assert.ok(!mid.stable.has(key("pp1")));
  assert.deepEqual([...mid.cascade], [key("pp1")]);
  assert.deepEqual([...fold(stream).stable].sort(), [key("exit_main"), key("pp1")].sort());
});

test("influence is a dynamic relation: destabilize drops the readers", () => {
  assert.deepEqual([...fold(stream.slice(0, 13)).infl.get(key("pp1"))], [key("pp1")]);
  assert.equal(fold(stream.slice(0, 21)).infl.get(key("pp1")), undefined);
  assert.deepEqual([...fold(stream).infl.get(key("pp1"))], [key("exit_main")]);
});

test("widening-point membership apart from widening applied", () => {
  const widened = fold(stream.slice(0, 19));

  assert.ok(widened.wpoints.has(key("pp1")));
  assert.equal(widened.widened, key("pp1"));
  assert.equal(fold(stream.slice(0, 20)).widened, null);
  assert.ok(!fold(stream).wpoints.has(key("pp1")));
});

test("counters", () => {
  const { counters } = fold(stream);

  assert.equal(counters.evaluations.get(key("pp1")), 2);
  assert.equal(counters.evaluations.get(key("exit_main")), 1);
  assert.equal(counters.updates.get(key("pp1")), 1);
  assert.equal(counters.updates.get("G:@g"), 1);
  assert.equal(counters.destabilizations.get(key("pp1")), 1);
});

test("globals keep their contributions and the last change", () => {
  const g = fold(stream).globals.get("G:@g");

  assert.equal(g.value, "1");
  assert.deepEqual(g.last, { old: "⊥", new: "1" });
  assert.equal(g.contributions.length, 1);
});

test("entry initialization draws the recorded side even after a bottom seed answer", () => {
  const seed = { kind: "activation_seed", procedure: "main", context: unit };
  const before = fold([
    { event: "query_global", current: L("entry_main"), target: seed, value: "⊥" },
  ]);
  const after = reduce(before, {
    event: "side", current: L("entry_main"), target: G, value: "interval: g=[0,0]",
  });

  assert.deepEqual(after.eventEdges, [
    { from: key("entry_main"), to: "G:@g", kind: "side" },
  ]);
  assert.deepEqual(before.eventEdges, [
    { from: "G:main|unit", to: key("entry_main"), kind: "read" },
  ]);
  assert.equal(after.globals.get("G:@g").value, "⊥");
});

test("destabilization fans out only to currently recorded readers", () => {
  let state = fold([
    { event: "add_infl", unknown: G, reader: L("old_reader") },
    { event: "destabilize", unknown: G },
    { event: "add_infl", unknown: G, reader: L("pp1") },
    { event: "add_infl", unknown: G, reader: L("pp1") },
    { event: "add_infl", unknown: G, reader: L("pp2") },
    { event: "add_infl", unknown: L("pp1"), reader: L("exit_main") },
    { event: "stable_add", unknown: L("pp1") },
    { event: "update_global", unknown: G, old: "⊥", new: "interval: g=[0,0]" },
  ]);

  // An update alone must not invent a write or fan-out.
  assert.deepEqual(state.eventEdges, []);
  state = reduce(state, { event: "destabilize", unknown: G });
  assert.deepEqual(state.eventEdges, [
    { from: "G:@g", to: key("pp1"), kind: "destabilize" },
    { from: "G:@g", to: key("pp2"), kind: "destabilize" },
  ]);
  assert.equal(state.infl.has("G:@g"), false);
  assert.equal(state.stable.has(key("pp1")), true);

  state = reduce(state, { event: "stable_remove", unknown: L("pp1") });
  assert.deepEqual(state.eventEdges, []);
  assert.equal(state.stable.has(key("pp1")), false);
  state = reduce(state, { event: "destabilize", unknown: L("pp1") });
  assert.deepEqual(state.eventEdges, [
    { from: key("pp1"), to: key("exit_main"), kind: "destabilize" },
  ]);
  assert.deepEqual(reduce(state, { event: "destabilize", unknown: G }).eventEdges, []);
});

test("event arrows agree when seeking across snapshots and disappear on other events", () => {
  const events = [
    { event: "side", current: L("entry_main"), target: G, value: "0" },
    { event: "add_infl", unknown: G, reader: L("pp1") },
    { event: "add_infl", unknown: G, reader: L("pp2") },
    { event: "destabilize", unknown: G },
    { event: "stable_remove", unknown: L("pp1") },
    { event: "destabilize", unknown: G },
  ];
  const cache = createCache(events, 2);

  for (const n of [4, 0, 1, 6, 4, 5]) {
    assert.deepEqual(cache.stateAt(n).eventEdges, fold(events.slice(0, n)).eventEdges);
  }
  const copy = copyState(cache.stateAt(4));
  copy.eventEdges[0].to = "unrelated";
  assert.equal(cache.stateAt(4).eventEdges[0].to, key("pp1"));
});

test("the snapshot cache agrees with a plain fold at every step", () => {
  const cache = createCache(stream, 4);

  for (const n of [0, 3, 9, 17, 5, stream.length, 1]) {
    assert.deepEqual([...cache.stateAt(n).stable], [...fold(stream.slice(0, n)).stable]);
    assert.deepEqual(cache.stateAt(n).stack, fold(stream.slice(0, n)).stack);
  }
});

test("the replay matches the result it came with", () => {
  const records = [
    ...stream,
    { event: "result", unknown: L("exit_main"), value: "[0,0]" },
    { event: "result", unknown: L("pp1"), value: "[0,0]" },
  ];

  assert.deepEqual(checkAgainstResult(records), []);
  assert.equal(
    checkAgainstResult([...stream, { event: "result", unknown: L("pp1"), value: "[1,1]" }])
      .length > 0,
    true,
  );
});

// Shared-global hints distinguish a write's reported effect from the shared result.

test("shared write hints keep contribution and final value separate", () => {
  const values = sharedGlobalValues({globals: ["g"], unknowns: [
    {name: "g", reachable: true, lines: ["interval:", "  g=[42,42]"]}]});
  assert.deepEqual([...values], [["g", "[42,42]"]]);
  const hint = sharedWriteHint("g: [17,17]", "g", values);
  assert.equal(hint.text, "⇢ g: [17,17] · final g: [42,42]");
  assert.match(hint.title, /not an individual solver trace event/);
});

test("shared values read each global from its own unknown", () => {
  const values = sharedGlobalValues({globals: ["g", "h", "k"], unknowns: [
    {name: "g", reachable: true, lines: ["interval:", "  g=⊤", "sign:", "  g=+"]},
    {name: "h", reachable: true, lines: ["order:", "  h ≤ g"]},
    {name: "k", reachable: false, lines: []}]});
  assert.equal(values.get("g"), "interval ⊤ · sign +");
  assert.equal(values.get("h"), undefined);
  assert.equal(values.get("k"), "⊥");
  assert.equal(sharedWriteHint("h: 17", "h", values).text, "⇢ h: 17 · final h: unavailable");
  assert.equal(sharedGlobalValues(null).size, 0);
});
