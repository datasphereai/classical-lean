# deploy/ - the nightly check of this library

This folder installs a nightly check of the classical-lean library on a Linux machine. It runs as
an ordinary user and never needs sudo.

## What the check is

The library is a set of mathematical proofs written in Lean, a language whose compiler checks
proofs. Every night the check does five things:

1. It pulls the newest version of the library.
2. It builds the library. Building means the compiler checks every proof again.
3. It runs the library's three gates: small programs that look for problems the compiler accepts.
   - `tools/AxiomGate.lean` checks that every theorem rests only on Lean's three standard axioms.
     An axiom is a statement assumed without proof.
   - `tools/check_sorry.py` checks that no proof is left unfinished. Lean marks an unfinished
     proof with the word `sorry`.
   - `tools/VacuityGate.lean` checks that no theorem is empty, such as one that only proves
     "true".
4. It writes the result to a status file.
5. It keeps the logs of the newest 14 runs.

Line 1 of the status file is the answer. When everything passed it looks like this:

    Lean: OK - 299cc09 2026-10-07, 946 theorems written, 1662 constants checked, 0 sorry, 0 axioms (none)

- **Theorems written** counts the `theorem` and `lemma` lines in the source files.
- **Constants checked** is the axiom gate's count. It is larger, because Lean also generates
  theorems of its own.

When anything fails or does not run, line 1 starts with `Lean: ATTENTION -` and says what failed.
The lines below it give each step's own result and the first lines of the error.

## Install

You need git, curl, tar, gzip, python3, flock (from util-linux) and about 15 GB of free disk.
Lean and its mathematics library, Mathlib, are downloaded, and together they take about 12 GB.
The installer checks all of this first. If something is missing, it stops with one line naming it
and writes nothing.

From a clone of this repository:

    deploy/install.sh --repo <git URL or path of the classical-lean repository>

For example, on the machine that holds the shared repository:

    deploy/install.sh --repo /data/git/classical-lean.git

The installer:

1. writes the settings file `~/.config/lean-nightly/config`;
2. installs elan, the Lean version manager, into `~/.elan`, and the Lean version the library asks
   for;
3. clones the library into `~/lean/classical-lean`;
4. copies the nightly script to `~/.local/bin/lean-nightly.sh`;
5. writes two systemd user units into `~/.config/systemd/user/`: `lean-nightly.service` runs the
   check, and `lean-nightly.timer` starts it every night at 03:30;
6. runs the check once. The first run downloads the Mathlib build cache and builds the library;
   this takes several minutes.

The status file is `~/lean/status/LEAN.md` and the logs are in `~/lean/logs/`.

Running the installer again changes nothing that is already in place. It is safe to repeat.

### Options

- `--no-timer`: for a machine without a systemd user session, for example a container. The unit
  files are written but the timer is not turned on, and the first check runs directly.

### Timers after a reboot

A user timer runs only while its user is logged in, unless "linger" is on. The installer tells
you if it is off, and prints the one command an administrator runs to turn it on:

    sudo loginctl enable-linger <your user name>

## Settings

`~/.config/lean-nightly/config` holds one `KEY=value` per line. Paths must be absolute.

| Key | Default | What it is |
|---|---|---|
| `REPO_URL` | none; give `--repo` | where the library is pulled from |
| `CLONE_DIR` | `~/lean/classical-lean` | the working copy that is built |
| `STATUS_FILE` | `~/lean/status/LEAN.md` | the result |
| `LOG_DIR` | `~/lean/logs` | one log per run, the newest 14 kept |
| `STATE_DIR` | `~/lean` | the lock file, and the Mathlib version the cache was fetched for |
| `BIN_DIR` | `~/.local/bin` | where the nightly script is installed |
| `NIGHTLY_TIME` | `03:30` | when the timer fires, local time |

To use other values, write the file yourself before the first install. The installer never
overwrites an existing settings file. For example, a machine that publishes the status for a
dashboard might use `STATUS_FILE=/opt/datasphere/status/LEAN.md`.

## Run, read, remove

- Run the check now: `systemctl --user start lean-nightly.service`
- Read the result: `head -1 ~/lean/status/LEAN.md`
- See the next run: `systemctl --user list-timers lean-nightly.timer`
- Remove: `systemctl --user disable --now lean-nightly.timer`, then delete the two unit files, the
  script, `~/.config/lean-nightly/` and `~/lean/`. Remove `~/.elan` too if nothing else uses Lean.

## Files here

- `install.sh`: the installer.
- `lean-nightly.sh`: the nightly check. The installer copies it to `BIN_DIR`.
- `lean-nightly.service.in`, `lean-nightly.timer.in`: unit templates. The installer fills in the
  script path, the status file and the time.
