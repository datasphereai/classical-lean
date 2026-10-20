#!/bin/bash
# Cloud port (claude-ai, 2026-10-19, order CLOUD-MATH-2) of order LEAN-32's el.sh (18260c3e):
# HANDOFF rules 20 and 37. Elaborates a Lean file with rule 20's four flags; output LABEL.out,
# logged with its rc. Before Lean runs, probecheck.py reads the file's text (a module: its lines
# changed against $BASE) and refuses the run while a token is not cleared, logged NOT RUN with
# the tokens. EL_PROBE=1 marks a probe run (the order's own probes, not subject to the check).
# After rc 0, every `#check` name in the file is logged as a PROBED line. The allowlist's sha256 is
# logged whenever it differs from the last logged value.
# A label already used (LABEL.out exists) is refused, logged NOT RUN (rule 17; added in the port).
# usage: el.sh LABEL FILE [N]      Needs EVD, REPO and BASE set; $EVD/allowlist.txt must exist.
: "${EVD:?set EVD}" "${REPO:?set REPO}" "${BASE:?set BASE to the base commit of the branch}"
T=$(cd "$(dirname "$0")" && pwd)
L=$1; F=$2
{ [ -z "$L" ] || [ -z "$F" ]; } && { echo "usage: el.sh LABEL FILE [N]"; exit 97; }
log() { printf '%s\t%s\trc=%s\tpred=%s\tcmd=%s\n' "$(date -u +%FT%TZ)" "$1" "$2" "$3" "$4" >> "$EVD/evidence.log"; }
if [ -e "$EVD/$L.out" ]; then log "$L" "NOT RUN" "compile-fix run" "refused: label $L already used: el.sh $F"; echo "refused: label used"; exit 97; fi
a=$(sha256sum "$EVD/allowlist.txt" | cut -d' ' -f1)
last=$(grep -o 'allowlist.txt :: [0-9a-f]*' "$EVD/evidence.log" 2>/dev/null | tail -1 | awk '{print $3}')
[ "$a" != "$last" ] && "$T/hl.sh" allowlist "$EVD/allowlist.txt" > /dev/null
if [ "${EL_PROBE:-0}" != 1 ]; then
  chk=$(python3 -I "$T/probecheck.py" check "$F" 2>&1); c=$?
  if [ $c -ne 0 ]; then log "$L" "NOT RUN" "compile-fix run" "refused by rule 37 (probecheck rc $c): el.sh $F :: $chk"; echo "rule 37: not run: $chk"; exit 96; fi
fi
export PATH=$HOME/.elan/bin:$PATH
cd "$REPO" || exit 99
nice -n 10 lake env lean -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3 "$F" > "$EVD/$L.out" 2>&1; rc=$?
echo "rc=$rc" >> "$EVD/$L.out"
tag=""; [ "${EL_PROBE:-0}" = 1 ] && tag=" (probe run, not subject to rule 37)"
h=$(sha256sum "$EVD/$L.out" | cut -c1-64)
log "$L" "$rc" "compile-fix run" "el.sh $F$tag :: out $L.out sha256 $h"
if [ $rc -eq 0 ]; then
  for n in $(python3 -I "$T/probecheck.py" record "$L" "$F"); do log "$L" "0" "probe" "PROBED $n"; done
fi
echo "rc=$rc"; head -"${3:-60}" "$EVD/$L.out"; exit $rc
