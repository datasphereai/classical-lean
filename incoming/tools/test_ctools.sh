#!/bin/bash
# claude-ai 2026-10-19: planted-fault tests of the cloud toolkit (ctools/) before it ships in
# CLOUD-MATH-2's incoming/tools/. Runs on DSMain against the clean clone ~/api-credit/cl-9c0639c,
# evidence in a scratch folder outside it. Each line: TEST name, expected, got, OK/BAD.
# usage: test_ctools.sh TOOLS_DIR
set -u
T=${1:?usage: test_ctools.sh TOOLS_DIR}
export PATH=$HOME/.elan/bin:$PATH
# REPO and BASE: the clean clone and its commit (defaults: claude-ai's DSMain clone). The test's own
# evidence folder is CTEST (default /tmp/ctools-test); it is wiped first, so it must never be the
# session's evidence folder: the script refuses when CTEST equals EVD.
[ -n "${EVD:-}" ] && [ "${CTEST:-/tmp/ctools-test}" = "$EVD" ] && { echo "refused: CTEST equals EVD"; exit 97; }
export REPO=${REPO:-$HOME/api-credit/cl-9c0639c} BASE=${BASE:-9c0639c} EVD=${CTEST:-/tmp/ctools-test}
rm -rf "$EVD"; mkdir -p "$EVD"; cp "$T/allowlist.txt" "$EVD/"
bad=0
chk() { if [ "$2" = "$3" ]; then echo "TEST $1 expected=$2 got=$3 OK"; else echo "TEST $1 expected=$2 got=$3 BAD"; bad=$((bad+1)); fi; }
# 1 ev.sh refuses without a prediction, and logs NOT RUN
"$T/ev.sh" t1 "" true >/dev/null; chk ev-no-prediction 97 $?
grep -q $'\tt1\trc=NOT RUN' "$EVD/evidence.log"; chk ev-logged-NOT-RUN 0 $?
# 2 ev.sh runs and logs rc with the output's sha256
"$T/ev.sh" t2 "rc 0" true >/dev/null; chk ev-runs 0 $?
grep -q $'\tt2\trc=0\tpred=rc 0\tcmd=true :: out t2.out sha256 ' "$EVD/evidence.log"; chk ev-line-format 0 $?
# 3 el.sh refuses a file using a name nobody probed
CTEST_T3="$EVD/t3.lean"
printf 'theorem probe_target_t3 (a b : Nat) (h : a < b) : a + 1 ≤ b := Nat.succ_le_of_lt h\n' > "$EVD/t3.lean"
"$T/el.sh" t3 "$EVD/t3.lean" >/dev/null; chk el-unprobed-refused 96 $?
grep -q 'NOT CLEARED: Nat.succ_le_of_lt' "$EVD/evidence.log"; chk el-refusal-names-token 0 $?
# 4 a probe run clears it, logged PROBED
printf '#check @Nat.succ_le_of_lt\n' > "$EVD/t4.lean"
EL_PROBE=1 "$T/el.sh" t4 "$EVD/t4.lean" >/dev/null; chk el-probe-run 0 $?
grep -q 'cmd=PROBED Nat.succ_le_of_lt' "$EVD/evidence.log"; chk el-PROBED-line 0 $?
"$T/el.sh" t3b "$EVD/t3.lean" >/dev/null; chk el-after-probe-runs 0 $?
# 5 el.sh with a failing Lean file reports its rc (not 0) and logs it
printf 'theorem t5_false : (1 : Nat) = 2 := rfl\n' > "$EVD/t5.lean"
"$T/el.sh" t5 "$EVD/t5.lean" >/dev/null; r=$?; [ $r -ne 0 ] && [ $r -ne 96 ]; chk el-lean-error-rc 0 $?
# 6 rootrun refuses when the build fails, and runs after a good build, build line first
ROOTRUN_BUILD=false "$T/rootrun.sh" t6 "rc 0" true >/dev/null; chk rootrun-bad-build 95 $?
grep -q $'\tt6\trc=NOT RUN' "$EVD/evidence.log"; chk rootrun-logged-NOT-RUN 0 $?
ROOTRUN_BUILD=true "$T/rootrun.sh" t6b "rc 0" true >/dev/null; chk rootrun-good-build 0 $?
a=$(grep -n $'\tt6b-build\t' "$EVD/evidence.log" | cut -d: -f1); b=$(grep -n $'\tt6b\t' "$EVD/evidence.log" | cut -d: -f1)
[ -n "$a" ] && [ -n "$b" ] && [ "$a" -lt "$b" ]; chk rootrun-build-before-command 0 $?
# 7 evcite writes the citation; citecheck passes it and catches a label left out
echo "COMMIT aaaaaaa" >> "$EVD/evidence.log"
"$T/ev.sh" t7a "rc 0" true >/dev/null; "$T/ev.sh" t7b "rc 0" true >/dev/null
cite=$(python3 -I "$T/evcite.py" "$EVD/evidence.log"); chk evcite-rc 0 $?
echo "COMMIT bbbbbbb" >> "$EVD/evidence.log"
printf 'msg\n\n%s\n' "$cite" > "$EVD/msg-good.txt"
python3 -I "$T/citecheck.py" "$EVD/evidence.log" --message "$EVD/msg-good.txt" bbbbbbb >/dev/null; chk citecheck-good 0 $?
printf 'msg\n\n%s\n' "${cite%, t7b}" > "$EVD/msg-bad.txt"
python3 -I "$T/citecheck.py" "$EVD/evidence.log" --message "$EVD/msg-bad.txt" bbbbbbb >/dev/null; chk citecheck-left-out 1 $?
python3 -I "$T/evcite.py" >/dev/null 2>&1; chk evcite-needs-log 1 $?
# 8 briefcheck refuses an undated clock time
printf 'run before 12:30 tonight\n' > "$EVD/b1.txt"; printf 'run before 2026-10-20 12:30 EDT\n' > "$EVD/b2.txt"
python3 -I "$T/briefcheck.py" "$EVD/b1.txt" >/dev/null; chk briefcheck-undated 3 $?
python3 -I "$T/briefcheck.py" "$EVD/b2.txt" >/dev/null; chk briefcheck-dated 0 $?
# 9 census counts theorem constants under ClassicalLean, private ones included, and nothing else
printf 'import Lean.Elab.Command\nnamespace ClassicalLean.CensusTest\ntheorem one_eq : (1 : Nat) = 1 := rfl\nprivate theorem two_eq : (2 : Nat) = 2 := rfl\ndef three : Nat := 3\nend ClassicalLean.CensusTest\ntheorem outside_eq : (4 : Nat) = 4 := rfl\n' > "$EVD/c1.lean"
out=$("$T/census.sh" c1 "$EVD/c1.lean" "CENSUS 2"); chk census-rc 0 $?
echo "$out" | grep -q 'CENSUS 2 '; chk census-count-2 0 $?
# 10 every tool refuses with EVD unset
( unset EVD; "$T/ev.sh" t10 "x" true >/dev/null 2>&1 ); r=$?; [ $r -ne 0 ]; chk ev-needs-EVD 0 $?
( unset BASE; "$T/el.sh" t10 "$EVD/t3.lean" >/dev/null 2>&1 ); r=$?; [ $r -ne 0 ]; chk el-needs-BASE 0 $?
( unset EVD; python3 -I "$T/probecheck.py" check "$CTEST_T3" >/dev/null 2>&1 ); r=$?; [ $r -ne 0 ]; chk probecheck-needs-EVD 0 $?
# 11 hl.sh logs one line per file in the format evcite reads, and refuses with no file
echo hello > "$EVD/h1.txt"
"$T/hl.sh" h1 "$EVD/h1.txt" >/dev/null; chk hl-runs 0 $?
grep -q $'\th1\trc=0\tpred=sha256\tcmd=sha256sum '"$EVD/h1.txt"' :: ' "$EVD/evidence.log"; chk hl-line-format 0 $?
"$T/hl.sh" h2 >/dev/null; chk hl-no-file 97 $?
# 12 a label already used is refused by ev.sh, el.sh and rootrun.sh, and the saved output is kept
before=$(sha256sum "$EVD/t2.out")
"$T/ev.sh" t2 "rc 0" false >/dev/null; chk ev-label-reuse 97 $?
[ "$(sha256sum "$EVD/t2.out")" = "$before" ]; chk ev-output-kept 0 $?
"$T/el.sh" t3b "$EVD/t3.lean" >/dev/null; chk el-label-reuse 97 $?
ROOTRUN_BUILD=true "$T/rootrun.sh" t6b "rc 0" true >/dev/null; chk rootrun-label-reuse 97 $?
# 13 rootrun with a failed build does not run the command at all
ROOTRUN_BUILD=false "$T/rootrun.sh" t13 "not run" touch "$EVD/ran" >/dev/null; chk rootrun-refused-rc 95 $?
[ ! -e "$EVD/ran" ]; chk rootrun-command-not-run 0 $?
# 14 probecheck on modules (lines changed against BASE), in a throwaway clone with no build
git clone -q "$REPO" "$EVD/clone"; m=$(cd "$EVD/clone" && git ls-files 'ClassicalLean/*.lean' | head -1)
( export REPO="$EVD/clone" BASE=HEAD
  printf 'theorem zz_new_t14 (a b : Nat) (h : a < b) : a + 1 ≤ b := Nat.lt_iff_add_one_le.mp h\n' > "$REPO/ClassicalLean/ZzProbeTest.lean"
  python3 -I "$T/probecheck.py" check "$REPO/ClassicalLean/ZzProbeTest.lean" >/dev/null; echo "new $?"
  python3 -I "$T/probecheck.py" check "$REPO/$m" >/dev/null; echo "unchanged $?"
  printf '\ntheorem zz_changed_t14 (a b : Nat) (h : a < b) : a + 1 ≤ b := Nat.lt_iff_add_one_le.mp h\n' >> "$REPO/$m"
  python3 -I "$T/probecheck.py" check "$REPO/$m" >/dev/null; echo "changed $?" ) > "$EVD/t14.txt"
grep -qx 'new 4' "$EVD/t14.txt"; chk probecheck-new-module-unprobed 0 $?
grep -qx 'unchanged 0' "$EVD/t14.txt"; chk probecheck-unchanged-module-cleared 0 $?
grep -qx 'changed 4' "$EVD/t14.txt"; chk probecheck-changed-line-unprobed 0 $?
# 15 citecheck in repository mode over real commits in a throwaway clone
git clone -q "$REPO" "$EVD/clone2"; b=$(git -C "$EVD/clone2" rev-parse HEAD)
"$T/ev.sh" c15a "rc 0" true >/dev/null
printf 'one\n\n%s\n' "$(python3 -I "$T/evcite.py" "$EVD/evidence.log")" > "$EVD/m15a.txt"
echo a > "$EVD/clone2/zz15a"; git -C "$EVD/clone2" add zz15a; git -C "$EVD/clone2" -c user.name=t -c user.email=t@t commit -q -F "$EVD/m15a.txt"
echo "COMMIT $(git -C "$EVD/clone2" rev-parse --short HEAD)" >> "$EVD/evidence.log"
python3 -I "$T/citecheck.py" "$EVD/evidence.log" "$EVD/clone2" "$b" > "$EVD/t15a.txt"; chk citecheck-repo-good 0 $?
"$T/ev.sh" c15b "rc 0" true >/dev/null; "$T/ev.sh" c15c "rc 0" true >/dev/null
c=$(python3 -I "$T/evcite.py" "$EVD/evidence.log"); printf 'two\n\n%s\n' "${c%, c15c}" > "$EVD/m15b.txt"
echo b > "$EVD/clone2/zz15b"; git -C "$EVD/clone2" add zz15b; git -C "$EVD/clone2" -c user.name=t -c user.email=t@t commit -q -F "$EVD/m15b.txt"
echo "COMMIT $(git -C "$EVD/clone2" rev-parse --short HEAD)" >> "$EVD/evidence.log"
python3 -I "$T/citecheck.py" "$EVD/evidence.log" "$EVD/clone2" "$b" > "$EVD/t15b.txt"; chk citecheck-repo-left-out 1 $?
# 16 the census elaborates with rule 20's four flags
grep -q 'census_c1_thm.*-DmaxSynthPendingDepth=3' "$EVD/evidence.log"; chk census-flags 0 $?
cd "$REPO" && [ -z "$(git status --porcelain)" ]; chk repo-still-clean 0 $?
echo "BAD=$bad"
