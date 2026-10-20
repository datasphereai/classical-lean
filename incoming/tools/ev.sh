#!/bin/bash
# Cloud port (claude-ai, 2026-10-19, for order CLOUD-MATH-2) of order LEAN-32's ev.sh (ee1d209e):
# HANDOFF rule 23's helper. The same log line format, so evcite.py and citecheck.py read it.
# usage: ev.sh LABEL "PREDICTION" cmd args...    (runs in $REPO; output to $EVD/LABEL.out)
#        ev.sh --nolean LABEL "PREDICTION" cmd args...   (the same; the flag is kept for LEAN-32's
#                                                         call shapes and changes nothing here)
# Needs EVD (the evidence directory, outside the repository) and REPO (the clone's root) set.
# Refuses, logged NOT RUN, without a label, a prediction or a command. Every run line ends with
# the sha256 of its output file (rule 17). DSMain's night window and memory cap are not ported:
# a cloud VM has neither timer. A label already used (its LABEL.out exists) is refused, logged NOT
# RUN, so a saved output is never overwritten (rule 17; added in the port, review 1 of CLOUD-MATH-2).
[ "$1" = --nolean ] && shift
L=$1; P=$2; shift 2
: "${EVD:?set EVD to the evidence directory}" "${REPO:?set REPO to the repository root}"
log() { printf '%s\t%s\trc=%s\tpred=%s\tcmd=%s\n' "$(date -u +%FT%TZ)" "$1" "$2" "$3" "$4" >> "$EVD/evidence.log"; }
if [ -z "$L" ] || [ -z "$P" ] || [ -z "$1" ]; then log "$L" "NOT RUN" "(none)" "refused: no label, prediction or command"; echo "refused"; exit 97; fi
if [ -e "$EVD/$L.out" ]; then log "$L" "NOT RUN" "$P" "refused: label $L already used: $*"; echo "refused: label used"; exit 97; fi
export PATH=$HOME/.elan/bin:$PATH
cd "$REPO" || exit 99
"$@" > "$EVD/$L.out" 2>&1; rc=$?
h=$(sha256sum "$EVD/$L.out" | cut -c1-64)
log "$L" "$rc" "$P" "$* :: out $L.out sha256 $h"
echo "rc=$rc"; exit $rc
