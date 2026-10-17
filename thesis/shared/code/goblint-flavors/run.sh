#!/bin/sh
# Runs Goblint on C versions of the 28-flavors fixtures and prints one line per
# program and configuration. results.tsv records the output for Goblint
# 5320a6b741e5 (the revision the thesis links). Goblint is not part of CI.
#
# usage: thesis/shared/code/goblint-flavors/run.sh /path/to/goblint > results.tsv
G=${1:?usage: run.sh GOBLINT}
cd "$(dirname "$0")" || exit 1
I="--enable ana.int.interval"
INT="$I --enable ana.int.congruence --set ana.int.refinement fixpoint"
THRESH="--enable ana.int.interval_threshold_widening"
for f in vanilla coffee coffee_bounded fudge narrow_works narrow_works_lb blackcurrant blackcurrant_lt \
  reset_eq reset_eq_lt sign_not_inductive; do
  while IFS='|' read -r name opts; do
    # gnu17: newer GCC headers use C23 keywords that Goblint's CIL rejects.
    # $opts is a list of options and must split into words.
    # shellcheck disable=SC2086
    v=$("$G" --set 'pre.cppflags[+]' -std=gnu17 $opts "$f.c" 2>&1 |
      sed -En 's/.*Assertion "([^"]*)" (will succeed|is unknown|will fail).*/\1: \2/p' |
      tr '\n' ';')
    printf '%s\t%s\t%s\n' "$f" "$name" "$v"
  done <<CFG
default|
interval|$I
interval+thresholds|$I $THRESH
interval+thresholds-comparisons|$I $THRESH --set ana.int.interval_threshold_widening_constants comparisons
interval+gas9|$I --set solvers.td3.widen_gas 9
interval+gas10|$I --set solvers.td3.widen_gas 10
int|$INT
int+gas2|$INT --set solvers.td3.widen_gas 2
int+gas3|$INT --set solvers.td3.widen_gas 3
int+thresholds-comparisons|$INT $THRESH --set ana.int.interval_threshold_widening_constants comparisons
CFG
done
