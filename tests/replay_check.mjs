// Reads one JSON Lines trace (schema 2) on stdin, replays it with the page's reducer, and
// prints the mismatches against the result records as a JSON list (empty when the
// replayed final state is the result run_voblint returned).

import { readFileSync } from "node:fs";

import { checkAgainstResult, parseEvents } from "../pages/replay_state.js";

const problems = checkAgainstResult(parseEvents(readFileSync(0, "utf8")));

process.stdout.write(`${JSON.stringify(problems)}\n`);
