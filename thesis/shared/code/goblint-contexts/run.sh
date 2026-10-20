#!/bin/sh
# Runs Goblint on C versions of the procedure fixtures of the evaluation's
# context comparison and prints one line per program and configuration: the
# number of checks in the program, then each reported check with its verdict.
# A check Goblint reports nothing for was found unreachable. results.tsv
# records the output for Goblint 6127869c56c6 (the revision the thesis links).
# Goblint is not part of CI.
#
# usage: thesis/shared/code/goblint-contexts/run.sh /path/to/goblint > results.tsv
G=${1:?usage: run.sh GOBLINT}
cd "$(dirname "$0")" || exit 1
I="--enable ana.int.interval"
CS="--set ana.activated[+] call_string --set ana.ctx_sens ['call_string'] --set ana.context.callString_length"
for f in ctxs3 chain5 chain3 chain3_entry circle countdown; do
  n=$(grep -c '__goblint_check' "$f.c")
  while IFS='|' read -r name opts; do
    # gnu17: newer GCC headers use C23 keywords that Goblint's CIL rejects.
    # $opts is a list of options and must split into words.
    # shellcheck disable=SC2086
    v=$("$G" --set 'pre.cppflags[+]' -std=gnu17 $opts "$f.c" 2>&1 |
      sed -En 's/.*Assertion "([^"]*)" (will succeed|is unknown|will fail).*/\1: \2/p' |
      tr '\n' ';')
    printf '%s\t%s\t%s\t%s\n' "$f" "$name" "$n" "$v"
  done <<CFG
insensitive|$I --set ana.context.gas_value 0
insensitive+narrow-globs|$I --set ana.context.gas_value 0 --enable solvers.td3.narrow-globs.enabled
callstring1|$I $CS 1
callstring5|$I $CS 5
full|$I
gas10|$I --set ana.context.gas_value 10
CFG
done
