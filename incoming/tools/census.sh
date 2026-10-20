#!/bin/bash
# Cloud port (claude-ai, 2026-10-19, order CLOUD-MATH-2) of order LEAN-32's mkcensus.sh (be0ce32f):
# HANDOFF rule 27's census. usage: census.sh LABEL SOURCE.lean "PREDICTION"     Needs EVD, REPO.
# Appends the census tails in this folder (census-tail.lean: theorem constants under ClassicalLean
# by privateToUserName and .thmInfo, the axiom gate's predicate; census-all-tail.lean: every
# constant the file adds) to the source, elaborates each through ev.sh, and writes the sorted name
# lists $EVD/census/LABEL_thm.names and LABEL_all.names; prints the two counts. Unlike the original it
# elaborates with rule 20's four flags (review 1 of CLOUD-MATH-2). Labels must be new (ev.sh refuses reuse).
: "${EVD:?set EVD}" "${REPO:?set REPO}"
T=$(cd "$(dirname "$0")" && pwd)
L=$1; S=$2; P=$3
{ [ -z "$L" ] || [ -z "$S" ] || [ -z "$P" ]; } && { echo "usage: census.sh LABEL SOURCE PREDICTION"; exit 97; }
mkdir -p "$EVD/census"
export PATH=$HOME/.elan/bin:$PATH
F=(-Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3)
cat "$S" "$T/census-tail.lean" > "$EVD/census/${L}_thm.lean"
cat "$S" "$T/census-all-tail.lean" > "$EVD/census/${L}_all.lean"
"$T/ev.sh" "census_${L}_thm" "$P" nice -n 10 lake env lean "${F[@]}" "$EVD/census/${L}_thm.lean" >/dev/null; r1=$?
"$T/ev.sh" "census_${L}_all" "$P" nice -n 10 lake env lean "${F[@]}" "$EVD/census/${L}_all.lean" >/dev/null; r2=$?
grep -o 'NAME .*' "$EVD/census_${L}_thm.out" | LC_ALL=C sort > "$EVD/census/${L}_thm.names"
grep -o 'CONST .*' "$EVD/census_${L}_all.out" | grep -v '^CONST$' | LC_ALL=C sort > "$EVD/census/${L}_all.names"
echo "$L rc=$r1/$r2 $(grep -o 'CENSUS [0-9]*' "$EVD/census_${L}_thm.out") $(grep -o 'ALLCONST [0-9]*' "$EVD/census_${L}_all.out") names=$(wc -l < "$EVD/census/${L}_thm.names")/$(wc -l < "$EVD/census/${L}_all.names")"
[ $r1 -eq 0 ] && [ $r2 -eq 0 ]
