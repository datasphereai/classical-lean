# Round 32 — `deploy/`: the nightly check, packaged for a fresh machine (order LEAN-4)

Session: Claude Code `session_01KyYusMNSHJap88c9A6s6K2` on DSMain, as dustin, executing order
`LEAN-4` (`records/orders/20261007T193300Z__claude-ai__order-lean4-package-nightly.md`), on branch
`package-nightly` in the worktree `~/lean/classical-lean-package-nightly`. Nothing was pushed.

**No module under `ClassicalLean/` was added or changed.** The new top-level folder `deploy/` holds
`install.sh`, `lean-nightly.sh`, `lean-nightly.service.in`, `lean-nightly.timer.in` and `README.md`.
The six gates do not look at `deploy/`: they scan `ClassicalLean/` and `ClassicalLean.lean`, and gate
6 only checks that Lean modules are named in the records. Nothing was bent to make them fit. What was
checked on `deploy/` instead:

- `bash -n` on both scripts.
- The `~/CLAUDE.md` banned-vocabulary grep: 0 hits.
- A grep for `DSMain|dustin|/opt/datasphere|dsrec`: only in `README.md`, as an example.
- A from-scratch install in a throwaway HOME under `env -i`, with `--no-timer`. Elan, toolchain
  v4.34.0, clone and Mathlib cache (8908 files downloaded) all started from nothing. Its line 1:
  `Lean: OK - 299cc09 2026-10-07, 946 theorems written, 1662 constants checked, 0 sorry, 0 axioms (none)`.
  `systemd-analyze --user verify` of the generated units returned rc=0.
- A second installer run in that HOME: identical listings of all 177266 entries (path, size,
  mtime in ns) and identical sha256 sums of the installed files.
- git hidden by a PATH of symlinks to every other tool, in an empty HOME: one line, rc=1, and 0
  files left.
- DSMain moved to the packaged script with its own config `~/.config/lean-nightly/config`
  (outside the repo). LEAN-2's files are kept as `*.pre-lean4`. Line 1 is unchanged and the timer
  still fires at 03:30.

Found by the first fresh run and fixed in `afb4eb4`: `systemd-analyze --user verify` cannot run
without a systemd user manager, and the installer had taken that for a rejection of the units.

HANDOFF §6 gains the dated line for the LEAN-3 push (`ea592cf..299cc09`, Dustin, 2026-10-07).

## Commits (branch `package-nightly`)

- `37a700e` — deploy/: installer and nightly check for a fresh machine.
- `afb4eb4` — deploy/install.sh: no systemd user manager is a note, not a rejection, when
  verifying units.
- the records commit that adds this fragment.
