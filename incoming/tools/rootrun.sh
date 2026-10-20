#!/bin/bash
# Cloud port (claude-ai, 2026-10-19, order CLOUD-MATH-2) of order LEAN-32's rootrun.sh (4d739a45):
# HANDOFF rule 38. A tool that imports ClassicalLean runs only on a fresh root build.
# usage: rootrun.sh LABEL "PREDICTION" cmd args...     Needs EVD and REPO.
# First runs the build at the current HEAD (output LABEL-build.out) and logs its rc, its job count
# and `git rev-parse HEAD` (label LABEL-build). Only if that rc is 0 does it run the command (output
# LABEL.out), logged with HEAD read again; otherwise the command is refused, logged NOT RUN, exit 95.
# The build command is the one variable ROOTRUN_BUILD (default `nice -n 10 lake build`), so the
# planted test swaps only it (ROOTRUN_BUILD=false). DSMain's cap and night window are not ported.
# A label already used is refused, logged NOT RUN (rule 17; added in the port).
: "${EVD:?set EVD}" "${REPO:?set REPO}"
L=$1; P=$2; shift 2
BUILD=${ROOTRUN_BUILD:-nice -n 10 lake build}
log() { printf '%s\t%s\trc=%s\tpred=%s\tcmd=%s\n' "$(date -u +%FT%TZ)" "$1" "$2" "$3" "$4" >> "$EVD/evidence.log"; }
if [ -z "$L" ] || [ -z "$P" ] || [ -z "$1" ]; then log "$L" "NOT RUN" "(none)" "rootrun refused: no label, prediction or command"; echo "refused"; exit 97; fi
if [ -e "$EVD/$L.out" ] || [ -e "$EVD/$L-build.out" ]; then log "$L" "NOT RUN" "$P" "rootrun refused: label $L already used: $*"; echo "refused: label used"; exit 97; fi
export PATH=$HOME/.elan/bin:$PATH
cd "$REPO" || exit 99
h1=$(git rev-parse HEAD)
# shellcheck disable=SC2086
$BUILD > "$EVD/$L-build.out" 2>&1; brc=$?
jobs=$(grep -o 'Build completed successfully ([0-9]* jobs)' "$EVD/$L-build.out" | grep -o '[0-9]*' | head -1)
warn=$(grep -c 'warning:' "$EVD/$L-build.out")
bh=$(sha256sum "$EVD/$L-build.out" | cut -c1-64)
log "$L-build" "$brc" "root build before $L" "rootrun build: $BUILD :: head $h1 jobs ${jobs:-none} warnings $warn :: out $L-build.out sha256 $bh"
if [ $brc -ne 0 ]; then
  log "$L" "NOT RUN" "$P" "rootrun refused by rule 38: build rc $brc at $h1: $*"
  echo "rule 38: not run (build rc $brc)"; exit 95
fi
h2=$(git rev-parse HEAD)
"$@" > "$EVD/$L.out" 2>&1; rc=$?
oh=$(sha256sum "$EVD/$L.out" | cut -c1-64)
log "$L" "$rc" "$P" "rootrun $* :: head $h2 :: out $L.out sha256 $oh"
echo "build rc=$brc jobs=${jobs:-none} warnings=$warn head=$h1; command rc=$rc head=$h2"; exit $rc
