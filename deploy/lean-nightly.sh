#!/bin/bash
# lean-nightly.sh - nightly check of the classical-lean Lean library (deploy/, order LEAN-4; from LEAN-2).
# Pulls the clone (--ff-only), builds it with `lake build`, runs the library's three gates
# (tools/AxiomGate.lean, tools/check_sorry.py, tools/VacuityGate.lean) and writes a one-screen
# status file, atomically (temp file in the same folder, then mv). Runs as an ordinary user; no sudo.
# Line 1 is "Lean: OK - ..." only when every step ran and passed; anything else is "Lean: ATTENTION - ...".
#
# Settings come from ~/.config/lean-nightly/config, written by deploy/install.sh. The file is read
# as KEY=value lines; it is never run as shell code. Keys: CLONE_DIR, STATUS_FILE, LOG_DIR,
# STATE_DIR (used here) and REPO_URL, BIN_DIR, NIGHTLY_TIME (used by the installer).
set -u

CONFIG="$HOME/.config/lean-nightly/config"
CLONE_DIR=""; STATUS_FILE=""; LOG_DIR=""; STATE_DIR=""
if [ ! -r "$CONFIG" ]; then
    echo "lean-nightly: no config file at $CONFIG (run deploy/install.sh first)" >&2
    exit 2
fi
while IFS= read -r line || [ -n "$line" ]; do
    case "$line" in ''|'#'*) continue ;; esac
    key=${line%%=*}; val=${line#*=}
    case "$key" in
        CLONE_DIR|STATUS_FILE|LOG_DIR|STATE_DIR) printf -v "$key" '%s' "$val" ;;
        REPO_URL|BIN_DIR|NIGHTLY_TIME) ;;
        *) echo "lean-nightly: unknown key '$key' in $CONFIG" >&2; exit 2 ;;
    esac
done <"$CONFIG"
for k in CLONE_DIR STATUS_FILE LOG_DIR STATE_DIR; do
    [ -n "${!k}" ] || { echo "lean-nightly: $k is missing from $CONFIG" >&2; exit 2; }
done

REPO="$CLONE_DIR"
STATUS="$STATUS_FILE"
STATUS_DIR=$(dirname "$STATUS_FILE")
PIN_STATE="$STATE_DIR/.lean-nightly-mathlib-pin"
LOCK="$STATE_DIR/.lean-nightly.lock"
KEEP_LOGS=14
MAX_AXIOMS=0      # LEAN-3 (2026-10-07): any project axiom is ATTENTION

export PATH="$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"

mkdir -p "$LOG_DIR" "$STATE_DIR" "$STATUS_DIR"
exec 9>"$LOCK"
if ! flock -n 9; then
    echo "lean-nightly: another run holds $LOCK; exiting" >&2
    exit 0
fi

START_EPOCH=$(date +%s)
START_HUMAN=$(date '+%Y-%m-%d %H:%M:%S %Z')
LOG="$LOG_DIR/lean-nightly-$(date +%Y%m%dT%H%M%S).log"
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

FAILS=()       # short phrases for line 1
DETAIL=""      # the error excerpt for the body (first failure only)
PULL_LINE="not run"; CACHE_LINE="not run"; BUILD_LINE="not run"
AXIOM_LINE="not run"; SORRY_LINE="not run"; VACUITY_LINE="not run"

log() { printf '%s\n' "$*" >>"$LOG"; }

# run <name> <outfile> <cmd...>: run in $REPO, tee output into the log, return the command's own exit code
run() {
    local name=$1 out=$2; shift 2
    log "=== $name: $* ($(date '+%H:%M:%S'))"
    ( cd "$REPO" && "$@" ) >"$out" 2>&1
    local rc=$?
    cat "$out" >>"$LOG"
    log "=== $name rc=$rc"
    return $rc
}

fail() {    # fail <phrase> <file-with-error-text>
    FAILS+=("$1")
    if [ -z "$DETAIL" ] && [ -n "${2:-}" ] && [ -f "$2" ]; then
        # first 20 lines from the first error-looking line; the whole head if none matches
        local at
        at=$(grep -m1 -n -E '^error|FAIL|fatal|error:' "$2" | cut -d: -f1)
        DETAIL="$1:"$'\n'"$(tail -n +"${at:-1}" "$2" | grep -v '^✔' | head -20)"
    fi
}

mathlib_pin() {
    python3 -I -c 'import json,sys
m=json.load(open(sys.argv[1]))
print(next(p["rev"] for p in m["packages"] if p["name"]=="mathlib"))' "$REPO/lake-manifest.json" 2>/dev/null
}

# --- 1. pull
if run pull "$WORK/pull" git pull --ff-only; then
    PULL_LINE=$(tail -1 "$WORK/pull")
    PULL_OK=1
else
    PULL_LINE="FAILED (rc=$?)"
    fail "pull failed" "$WORK/pull"
    PULL_OK=0
fi

# --- 2. Mathlib cache, only when the pin moved (or was never fetched by this script)
BUILD_OK=0
if [ $PULL_OK = 1 ]; then
    PIN=$(mathlib_pin)
    if [ -z "$PIN" ]; then
        CACHE_LINE="FAILED: cannot read the mathlib rev from lake-manifest.json"
        fail "cannot read Mathlib pin" ""
        CACHE_OK=0
    elif [ -f "$PIN_STATE" ] && [ "$(cat "$PIN_STATE")" = "$PIN" ]; then
        CACHE_LINE="skipped: mathlib pin unchanged ($PIN)"
        CACHE_OK=1
    elif run cache "$WORK/cache" nice -n 19 lake exe cache get; then
        CACHE_LINE="ran: mathlib pin ${PIN} ($(grep -v '^[[:space:]]*$' "$WORK/cache" | tail -1 | tr -d '\r'))"
        printf '%s\n' "$PIN" >"$PIN_STATE"
        CACHE_OK=1
    else
        CACHE_LINE="FAILED (rc=$?)"
        fail "lake exe cache get failed" "$WORK/cache"
        CACHE_OK=0
    fi

    # --- 3. build
    if [ $CACHE_OK = 1 ]; then
        if run build "$WORK/build" nice -n 19 lake build; then
            BUILD_LINE=$(grep -E '^Build completed' "$WORK/build" | tail -1)
            [ -n "$BUILD_LINE" ] || BUILD_LINE="rc=0"
            BUILD_OK=1
        else
            BUILD_LINE="FAILED (rc=$?)"
            fail "build failed" "$WORK/build"
        fi
    fi
fi

# --- 4. gates (need a built library)
THEOREMS=""; WRITTEN=""; AXIOM_NAMES=""; AXIOM_COUNT=""
if [ $BUILD_OK = 1 ]; then
    # T: top-level theorem/lemma declarations, counted in code only (LEAN-8): comments and docstrings
    # (nested /- ... -/ blocks and -- to end of line) are removed first, so a prose line that starts
    # with "theorem" is not counted. Library files only, declarations at the start of a line.
    WRITTEN=$(cd "$REPO" && python3 -I -c '
import re, pathlib
pat = re.compile(r"^(@\[[^]]*\] *)?((private|protected|noncomputable) +)*(theorem|lemma) ")
def code(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i): depth += 1; i += 2; continue
        if depth and src.startswith("-/", i): depth -= 1; i += 2; continue
        if depth:
            if src[i] == "\n": out.append("\n")
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return "".join(out)
files = sorted(pathlib.Path("ClassicalLean").rglob("*.lean")) + [pathlib.Path("ClassicalLean.lean")]
print(sum(1 for f in files for line in code(f.read_text()).splitlines() if pat.match(line)))
')
    [ "${WRITTEN:-0}" -gt 0 ] || fail "theorem grep found nothing" ""
    SORRY_WARN=$(grep -cE "declaration uses .sorry." "$WORK/build")
    if run axiom-gate "$WORK/axiom" nice -n 19 lake env lean tools/AxiomGate.lean; then
        AXIOM_LINE=$(grep -m1 -E '^axiom gate PASS' "$WORK/axiom")
        THEOREMS=$(grep -m1 -oE 'PASS — [0-9]+ theorem' "$WORK/axiom" | grep -oE '[0-9]+')
        AXIOM_NAMES=$(grep -oE '← [^],]+' "$WORK/axiom" | sed 's/^← //; s/^ClassicalLean\.//' | sort -u | paste -sd, -)
        if [ -n "$AXIOM_NAMES" ]; then
            AXIOM_COUNT=$(printf '%s\n' "$AXIOM_NAMES" | tr ',' '\n' | wc -l)
        else
            AXIOM_COUNT=0
        fi
        EXC=$(grep -m1 -oE '[0-9]+ scoped exception' "$WORK/axiom")
        case "$AXIOM_LINE" in *"scoped exception"*) ;; *) [ -n "$EXC" ] && AXIOM_LINE="$AXIOM_LINE; $EXC(s)" ;; esac
        if [ -z "$AXIOM_LINE" ] || [ -z "$THEOREMS" ]; then
            fail "axiom gate output not understood" "$WORK/axiom"
        elif [ "$AXIOM_COUNT" -gt "$MAX_AXIOMS" ]; then
            fail "$AXIOM_COUNT project axiom(s): $AXIOM_NAMES (allowed $MAX_AXIOMS)" "$WORK/axiom"
        fi
    else
        AXIOM_LINE="FAILED (rc=$?)"
        fail "axiom gate failed" "$WORK/axiom"
    fi

    if run check-sorry "$WORK/sorry" python3 -I tools/check_sorry.py; then
        SORRY_LINE=$(grep -m1 -E '^check_sorry PASS' "$WORK/sorry")
        [ -n "$SORRY_LINE" ] || { SORRY_LINE="rc=0 but no PASS line"; fail "check_sorry output not understood" "$WORK/sorry"; }
    else
        SORRY_LINE="FAILED (rc=$?)"
        fail "check_sorry failed (sorry or banned proof)" "$WORK/sorry"
    fi
    if [ "$SORRY_WARN" -gt 0 ]; then
        fail "build reports $SORRY_WARN sorry" "$WORK/build"
    fi

    if run vacuity-gate "$WORK/vacuity" nice -n 19 lake env lean tools/VacuityGate.lean; then
        VACUITY_LINE=$(grep -m1 -E '^vacuity gate PASS' "$WORK/vacuity")
        [ -n "$VACUITY_LINE" ] || { VACUITY_LINE="rc=0 but no PASS line"; fail "vacuity gate output not understood" "$WORK/vacuity"; }
    else
        VACUITY_LINE="FAILED (rc=$?)"
        fail "vacuity gate failed" "$WORK/vacuity"
    fi
fi

# --- 5. status
END_EPOCH=$(date +%s)
DUR=$((END_EPOCH - START_EPOCH))
COMMIT=$(git -C "$REPO" log -1 --format='%h %cs' 2>/dev/null || echo "unknown")

if [ ${#FAILS[@]} -eq 0 ] && [ $BUILD_OK = 1 ]; then
    LINE1="Lean: OK - $COMMIT, $WRITTEN theorems written, $THEOREMS constants checked, 0 sorry, $AXIOM_COUNT axioms (${AXIOM_NAMES:-none})"
else
    [ ${#FAILS[@]} -eq 0 ] && FAILS+=("a step did not run")
    LINE1="Lean: ATTENTION - $(IFS=';'; echo "${FAILS[*]}" | sed 's/;/; /g')"
fi

TMP=$(mktemp "$STATUS_DIR/.LEAN.md.XXXXXX") || { echo "lean-nightly: cannot create temp file in $STATUS_DIR" >&2; exit 1; }
{
    echo "$LINE1"
    echo
    echo "- run: $START_HUMAN, took ${DUR}s, on commit $COMMIT"
    echo "- pull: $PULL_LINE"
    echo "- mathlib cache: $CACHE_LINE"
    echo "- build: $BUILD_LINE"
    echo "- axiom gate: $AXIOM_LINE"
    echo "- check_sorry: $SORRY_LINE"
    echo "- vacuity gate: $VACUITY_LINE"
    echo "- full log: $LOG"
    if [ -n "$DETAIL" ]; then
        echo
        echo '```'
        printf '%s\n' "$DETAIL"
        echo '```'
    fi
} >"$TMP"
chmod 0640 "$TMP"
mv -f "$TMP" "$STATUS"
log "=== status: $LINE1"

# --- 6. keep the newest $KEEP_LOGS run logs
ls -1t "$LOG_DIR"/lean-nightly-*.log 2>/dev/null | tail -n +$((KEEP_LOGS + 1)) | xargs -r rm -f --

case "$LINE1" in "Lean: OK"*) exit 0 ;; *) exit 1 ;; esac
