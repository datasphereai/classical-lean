#!/bin/bash
# CLOUD-MATH-2, rule 39: finish a commit message. usage: finishmsg.sh BODY OUT
# OUT = BODY (its trailer lines removed), a blank line, the line evcite.py prints (generated here,
# last, from $EVD/evidence.log), a blank line, the two attribution trailers.
: "${EVD:?set EVD}" "${T:?set T}"
B=$1; O=$2
{ [ -z "$B" ] || [ -z "$O" ]; } && { echo "usage: finishmsg.sh BODY OUT"; exit 97; }
ev=$(python3 -I "$T/evcite.py" "$EVD/evidence.log") || { echo "evcite failed"; exit 98; }
{ grep -v -e '^Co-Authored-By: ' -e '^Claude-Session: ' "$B" | sed -e :a -e '/^\n*$/{$d;N;ba' -e '}'
  echo; echo "$ev"; echo
  echo "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
  echo "Claude-Session: https://claude.ai/code/session_019tga5LT3iStpcstjGMLwLU"; } > "$O"
