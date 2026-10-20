#!/bin/bash
# CLOUD-MATH-2 End check 3: copy the evidence folder into incoming/evidence/, leaving out every file
# over 1 MB (find -size +1M), and print the number of files copied and left out.
: "${EVD:?}" "${REPO:?}"
D=$REPO/incoming/evidence
mkdir -p "$D"
cd "$EVD" || exit 99
n=0; m=0
while IFS= read -r -d '' f; do
  if [ -n "$(find "$f" -size +1M)" ]; then m=$((m+1)); echo "LEFT OUT $f"; continue; fi
  mkdir -p "$D/$(dirname "$f")"; cp -p "$f" "$D/$f"; n=$((n+1))
done < <(find . -type f -print0)
echo "copied $n, left out $m"
