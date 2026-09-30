// The replay reducer (pages/replay_state.js) on hand-written schema 2 event
// streams. Needs no build: `node --test tests/replay_state.test.mjs`.

import assert from "node:assert/strict";
import { test } from "node:test";

import {
  checkAgainstResult,
  createCache,
  emptyState,
  localKey,
  reduce,
} from "../pages/replay_state.js";

const unit = { kind: "unit" };
const L = (node) => ({ kind: "local", node, context: unit });
const G = { kind: "analysis_global" };
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
  assert.equal(counters.updates.get("G:Global"), 1);
  assert.equal(counters.destabilizations.get(key("pp1")), 1);
});

test("globals keep their contributions and the last change", () => {
  const g = fold(stream).globals.get("G:Global");

  assert.equal(g.value, "1");
  assert.deepEqual(g.last, { old: "⊥", new: "1" });
  assert.equal(g.contributions.length, 1);
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
