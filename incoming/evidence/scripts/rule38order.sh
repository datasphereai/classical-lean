#!/bin/bash
# CLOUD-MATH-3, rule 38's test with the real build: in evidence.log, the LABEL-build line comes
# before the LABEL line, and both name the same head. usage: rule38order.sh LABEL   Needs EVD.
: "${EVD:?set EVD}"
L=${1:?usage: rule38order.sh LABEL}
a=$(grep -n $'\t'"$L"$'-build\t' "$EVD/evidence.log" | head -1)
b=$(grep -n $'\t'"$L"$'\t' "$EVD/evidence.log" | head -1)
na=${a%%:*}; nb=${b%%:*}
ha=$(echo "$a" | grep -o 'head [0-9a-f]*' | head -1); hb=$(echo "$b" | grep -o 'head [0-9a-f]*' | head -1)
echo "build line $na ($ha); command line $nb ($hb)"
[ -n "$na" ] && [ -n "$nb" ] && [ "$na" -lt "$nb" ] && [ -n "$ha" ] && [ "$ha" = "$hb" ] && echo "ORDER OK" && exit 0
echo "ORDER BAD"; exit 1
