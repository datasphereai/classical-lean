#!/bin/bash
# install.sh - install the nightly classical-lean check for the current user (order LEAN-4).
#
#   deploy/install.sh --repo <git URL or path of the classical-lean repository> [--no-timer]
#
# Installs, without sudo and only under $HOME: elan and the Lean toolchain the library pins, a
# clone of the library, the Mathlib build cache, the nightly script, and a systemd user timer that
# runs it daily. Then it runs the check once and prints line 1 of the status file.
#
# Every prerequisite is checked before anything is written; a missing one stops the installer with
# one line naming it. Running the installer again changes nothing that is already in place.
#
# --no-timer   write the unit files but do not enable the timer (for machines without a systemd
#              user session); the first check then runs the script directly.
set -u

say() { echo "install.sh: $*"; }
die() { echo "install.sh: $*" >&2; exit 1; }

REPO_ARG=""
NO_TIMER=0
while [ $# -gt 0 ]; do
    case "$1" in
        --repo) [ $# -ge 2 ] || die "--repo needs a value"; REPO_ARG=$2; shift 2 ;;
        --repo=*) REPO_ARG=${1#--repo=}; shift ;;
        --no-timer) NO_TIMER=1; shift ;;
        -h|--help) sed -n '2,15p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
        *) die "unknown option '$1' (see --help)" ;;
    esac
done

HERE=$(cd "$(dirname "$0")" && pwd)
CONFIG_DIR="$HOME/.config/lean-nightly"
CONFIG="$CONFIG_DIR/config"
UNIT_DIR="$HOME/.config/systemd/user"
ELAN="$HOME/.elan/bin/elan"

# Defaults; an existing config file overrides them.
REPO_URL=""
CLONE_DIR="$HOME/lean/classical-lean"
STATUS_FILE="$HOME/lean/status/LEAN.md"
LOG_DIR="$HOME/lean/logs"
STATE_DIR="$HOME/lean"
BIN_DIR="$HOME/.local/bin"
NIGHTLY_TIME="03:30"

# Same reader as lean-nightly.sh: KEY=value lines, known keys only, never run as shell code.
read_config() {
    local line key val
    while IFS= read -r line || [ -n "$line" ]; do
        case "$line" in ''|'#'*) continue ;; esac
        key=${line%%=*}; val=${line#*=}
        case "$key" in
            REPO_URL|CLONE_DIR|STATUS_FILE|LOG_DIR|STATE_DIR|BIN_DIR|NIGHTLY_TIME)
                printf -v "$key" '%s' "$val" ;;
            *) die "unknown key '$key' in $CONFIG" ;;
        esac
    done <"$CONFIG"
}

HAVE_CONFIG=0
if [ -f "$CONFIG" ]; then
    HAVE_CONFIG=1
    read_config
    if [ -n "$REPO_ARG" ] && [ "$REPO_ARG" != "$REPO_URL" ]; then
        die "--repo $REPO_ARG differs from REPO_URL=$REPO_URL in $CONFIG; edit the config file instead"
    fi
else
    REPO_URL=$REPO_ARG
fi
[ -n "$REPO_URL" ] || die "no repository given: run with --repo <git URL or path of classical-lean>"
for v in CLONE_DIR STATUS_FILE LOG_DIR STATE_DIR BIN_DIR; do
    case "${!v}" in /*) ;; *) die "$v must be an absolute path, not '${!v}'" ;; esac
done
[[ "$NIGHTLY_TIME" =~ ^([01][0-9]|2[0-3]):[0-5][0-9]$ ]] || die "NIGHTLY_TIME must be HH:MM, not '$NIGHTLY_TIME'"

# ---------------------------------------------------------------- 1. prerequisites (nothing written yet)
need() {    # need <command> <package to install>
    command -v "$1" >/dev/null 2>&1 \
        || die "'$1' is not installed. Install the package '$2' (on Ubuntu: sudo apt install $2) and run this again."
}
need git git
need curl curl
need tar tar
need gzip gzip
need python3 python3
need flock util-linux
if [ $NO_TIMER = 0 ]; then
    need systemctl systemd
    systemctl --user show-environment >/dev/null 2>&1 \
        || die "no systemd user session ('systemctl --user' does not answer). Log in normally, or run with --no-timer."
fi

nearest_dir() {    # the path itself, or its nearest existing parent
    local d=$1
    while [ ! -d "$d" ]; do d=$(dirname "$d"); done
    printf '%s\n' "$d"
}
for p in "$CLONE_DIR" "$STATUS_FILE" "$LOG_DIR" "$STATE_DIR" "$BIN_DIR" "$CONFIG_DIR" "$UNIT_DIR"; do
    d=$(nearest_dir "$p")
    [ -w "$d" ] || die "cannot write under $d (needed for $p)"
done

NEED_DOWNLOAD=0
[ -x "$ELAN" ] || NEED_DOWNLOAD=1
[ -d "$CLONE_DIR/.lake/packages/mathlib" ] || NEED_DOWNLOAD=1
if [ $NEED_DOWNLOAD = 1 ]; then
    d=$(nearest_dir "$CLONE_DIR")
    free_kb=$(df -Pk "$d" | awk 'NR==2 {print $4}')
    [ "$free_kb" -ge $((15 * 1024 * 1024)) ] \
        || die "only $((free_kb / 1024 / 1024)) GB free under $d; the Lean toolchain and Mathlib need about 12 GB. Free 15 GB and run this again."
    curl -fsSI --max-time 20 https://raw.githubusercontent.com >/dev/null 2>&1 \
        || die "cannot reach https://raw.githubusercontent.com; the toolchain and Mathlib are downloaded from the internet."
fi
if [ ! -d "$CLONE_DIR/.git" ]; then
    [ ! -e "$CLONE_DIR" ] || die "$CLONE_DIR exists but is not a git clone; move it away or set CLONE_DIR in $CONFIG"
    git ls-remote "$REPO_URL" HEAD >/dev/null 2>&1 || die "cannot read the repository $REPO_URL"
fi

# ---------------------------------------------------------------- 2. config file
if [ $HAVE_CONFIG = 0 ]; then
    mkdir -p "$CONFIG_DIR"
    tmp=$(mktemp "$CONFIG_DIR/.config.XXXXXX")
    {
        echo "# lean-nightly settings, written by deploy/install.sh. KEY=value, absolute paths."
        for v in REPO_URL CLONE_DIR STATUS_FILE LOG_DIR STATE_DIR BIN_DIR NIGHTLY_TIME; do
            printf '%s=%s\n' "$v" "${!v}"
        done
    } >"$tmp"
    mv "$tmp" "$CONFIG"
    say "wrote $CONFIG"
fi

# ---------------------------------------------------------------- 3. elan, the clone, the toolchain
if [ ! -x "$ELAN" ]; then
    say "installing elan (the Lean version manager) into $HOME/.elan"
    tmp=$(mktemp -d)
    curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$tmp/elan-init.sh" \
        || { rm -rf "$tmp"; die "downloading elan-init.sh failed"; }
    sh "$tmp/elan-init.sh" -y --default-toolchain none --no-modify-path >"$tmp/log" 2>&1 \
        || { tail -5 "$tmp/log" >&2; rm -rf "$tmp"; die "elan-init.sh failed"; }
    rm -rf "$tmp"
fi
export PATH="$HOME/.elan/bin:$PATH"

if [ ! -d "$CLONE_DIR/.git" ]; then
    say "cloning $REPO_URL into $CLONE_DIR"
    mkdir -p "$(dirname "$CLONE_DIR")"
    nice -n 19 git clone -q "$REPO_URL" "$CLONE_DIR" || die "git clone failed"
else
    origin=$(git -C "$CLONE_DIR" remote get-url origin 2>/dev/null)
    [ "$origin" = "$REPO_URL" ] || die "$CLONE_DIR is a clone of '$origin', not of $REPO_URL"
fi

TOOLCHAIN=$(tr -d '[:space:]' <"$CLONE_DIR/lean-toolchain")
if ! "$ELAN" toolchain list | awk '{print $1}' | grep -qxF "$TOOLCHAIN"; then
    say "installing the Lean toolchain $TOOLCHAIN"
    nice -n 19 "$ELAN" toolchain install "$TOOLCHAIN" >/dev/null || die "elan toolchain install $TOOLCHAIN failed"
fi

# ---------------------------------------------------------------- 4. the script and the units
put() {    # put <source> <destination> <mode>: write only when the content differs; returns 0 if written
    if [ -f "$2" ] && cmp -s "$1" "$2"; then return 1; fi
    mkdir -p "$(dirname "$2")"
    local tmp
    tmp=$(mktemp "$(dirname "$2")/.$(basename "$2").XXXXXX")
    cp "$1" "$tmp" && chmod "$3" "$tmp" && mv -f "$tmp" "$2"
    say "wrote $2"
    return 0
}
SCRIPT="$BIN_DIR/lean-nightly.sh"
put "$HERE/lean-nightly.sh" "$SCRIPT" 0755 || true

render() {
    sed -e "s|@SCRIPT@|$SCRIPT|g" -e "s|@STATUS_FILE@|$STATUS_FILE|g" -e "s|@NIGHTLY_TIME@|$NIGHTLY_TIME|g" "$1"
}
UNITS_CHANGED=0
tmpd=$(mktemp -d)
trap 'rm -rf "$tmpd"' EXIT
for u in lean-nightly.service lean-nightly.timer; do
    render "$HERE/$u.in" >"$tmpd/$u"
    if put "$tmpd/$u" "$UNIT_DIR/$u" 0644; then UNITS_CHANGED=1; fi
done
if command -v systemd-analyze >/dev/null 2>&1; then
    # Verifying needs a running systemd user manager; without one (a container, an empty
    # environment) say so and carry on, but stop on a real rejection.
    if ! out=$(systemd-analyze --user verify "$UNIT_DIR/lean-nightly.service" \
            "$UNIT_DIR/lean-nightly.timer" 2>&1); then
        case "$out" in
            *"Failed to initialize manager"*|*"RuntimeDirectory"*)
                say "unit files not verified here (no systemd user manager): $(printf '%s' "$out" | head -1)" ;;
            *)
                printf '%s\n' "$out" >&2
                die "systemd-analyze rejected the unit files in $UNIT_DIR" ;;
        esac
    elif [ -n "$out" ]; then
        printf '%s\n' "$out" >&2
    fi
fi

# ---------------------------------------------------------------- 5. the timer
if [ $NO_TIMER = 0 ]; then
    if [ $UNITS_CHANGED = 1 ]; then
        systemctl --user daemon-reload
        if systemctl --user is-active -q lean-nightly.timer; then
            systemctl --user restart lean-nightly.timer
        fi
    fi
    if ! systemctl --user is-enabled -q lean-nightly.timer 2>/dev/null; then
        systemctl --user enable --now lean-nightly.timer 2>/dev/null || die "could not enable lean-nightly.timer"
        say "enabled lean-nightly.timer (daily at $NIGHTLY_TIME)"
    fi
    linger=$(loginctl show-user "$(id -un)" -p Linger --value 2>/dev/null)
    if [ "$linger" = "no" ]; then
        say "note: user timers run only while you are logged in. To run them after a reboot without logging in, an administrator runs:"
        say "  sudo loginctl enable-linger $(id -un)"
    fi
else
    say "--no-timer: unit files are in $UNIT_DIR, timer not enabled"
fi

# ---------------------------------------------------------------- 6. the first check
if [ -e "$STATUS_FILE" ]; then
    say "status file exists, first check skipped: $STATUS_FILE"
    say "line 1: $(head -1 "$STATUS_FILE")"
    exit 0
fi
say "running the first check (the first run downloads the Mathlib cache and builds; this takes a while)"
if [ $NO_TIMER = 0 ]; then
    systemctl --user start lean-nightly.service
else
    if command -v ionice >/dev/null 2>&1; then
        nice -n 19 ionice -c3 /bin/bash "$SCRIPT"
    else
        nice -n 19 /bin/bash "$SCRIPT"
    fi
fi
[ -f "$STATUS_FILE" ] || die "the first check wrote no status file; see the newest log in $LOG_DIR"
line1=$(head -1 "$STATUS_FILE")
say "line 1: $line1"
case "$line1" in "Lean: OK"*) exit 0 ;; *) exit 1 ;; esac
