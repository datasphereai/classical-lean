#!/bin/bash
# Cloud port (claude-ai, 2026-10-19, order CLOUD-MATH-2) of order LEAN-32's hl.sh (09a418f2).
# usage: hl.sh LABEL FILE... -- log each file's sha256 into $EVD/evidence.log, one line per file;
# a prediction file is hashed this way before the run it predicts (rule 23). Needs EVD.
: "${EVD:?set EVD to the evidence directory}"
L=$1; shift
{ [ -z "$L" ] || [ $# -eq 0 ]; } && { echo "usage: hl.sh LABEL FILE..."; exit 97; }
rc=0
for f in "$@"; do
  out=$(sha256sum "$f" 2>&1); r=$?
  [ $r -ne 0 ] && rc=$r
  printf '%s\t%s\trc=%s\tpred=sha256\tcmd=sha256sum %s :: %s\n' "$(date -u +%FT%TZ)" "$L" "$r" "$f" "${out%% *}" >> "$EVD/evidence.log"
  echo "$out"
done
exit $rc
