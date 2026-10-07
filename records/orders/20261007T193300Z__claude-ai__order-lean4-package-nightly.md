<!-- Copied verbatim on 2026-10-07 from /opt/datasphere/lane/inbox/threads/staging/LEAN-4-order.md (DSMain lane; sha256 c42d1744226d54e4e168c4ee199e447b8352f46994747a190b90432dde74996d, checked before reading), per records/README.md rule 2. Copied after the work began. -->

# LEAN-4: package the nightly Lean check so a fresh machine can install it

From claude-ai (claude-ai-58), 2026-10-07 15:33 EDT. For the same plain Claude Code session on DSMain, as dustin. Follows LEAN-3-report.md (84a8ffca): disc_biquadratic_23 is proved, and Dustin pushed the branch at 15:32 EDT. His terminal printed `ea592cf..299cc09  prove-disc-biquadratic -> master` for `To /data/git/classical-lean.git`.

This is item 2 of DIRECTION-20261007.md (8a6746a8): "Package that server so someone else can install it on a fresh machine." It starts with the part item 1 built, the nightly Lean check from LEAN-1 and LEAN-2.

Goal: one script installs, on a fresh Linux machine as an ordinary user, everything LEAN-1 and LEAN-2 set up by hand: elan and the pinned Lean toolchain, a clone of classical-lean, the Mathlib cache, a first build with the three gates, and the nightly timer writing a status file. Then DSMain itself runs the packaged copy, so there is one script to keep, not two.

## Step 0, before anything else

1. Run `systemctl --user start lean-nightly.service`, then `systemctl --user show lean-nightly.service -p Result`, then line 1 of /opt/datasphere/status/LEAN.md. Predicted: `Result=success` and `Lean: OK - 299cc09 2026-10-07, 946 theorems written, 1662 constants checked, 0 sorry, 0 axioms (none)`. If line 1 is not OK, stop here and report; do nothing else.
2. Run `loginctl show-user dustin -p Linger`. User timers fire only while dustin's user manager is running. With Linger=no, after a reboot the 03:30 check and the map's 15-minute timer wait until he logs in. If it says no, put `sudo loginctl enable-linger dustin` at the top of the report as Dustin's one paste. Do not run it.
3. Run `git -C ~/lean/classical-lean branch -d prove-disc-biquadratic`. It refuses unless the branch is merged; master should now be at 299cc09, the branch tip.

## Scope

- As dustin, no sudo. Do not touch /opt/datasphere-mcp/, the store, or credential files.
- Branch `package-nightly` from master at 299cc09. Do the branch work in a separate worktree (`git worktree add`), so the real clone at ~/lean/classical-lean stays on master and the 03:30 run is unaffected. Commit as you go. Do not push.
- The package goes in the repo, in a new top-level folder `deploy/`: the installer, the nightly script generalised from ~/bin/lean-nightly.sh, the two unit templates, and a short README.md in plain words for someone who has never used Lean.
- The installer never uses sudo. If something it needs is missing (git, curl, python3, a systemd user session), it stops with one plain line naming what to install. If linger is off, it prints the sudo line and carries on.
- Nothing in deploy/ names DSMain, dustin, /opt/datasphere or dsrec, except as an example in the README. DSMain's own values (status file /opt/datasphere/status/LEAN.md, repository /data/git/classical-lean.git) go in a small config file outside the repo. The default status file for anyone else is inside their own home; the README names it.
- Keep LEAN-2's behaviour as it is today: the flock, nice 19 and idle I/O, the Mathlib cache fetched only when the pin changes, logs pruned to the newest 14, ATTENTION on any failure, project axioms allowed 0 (LEAN-3), and the T and C counts on line 1.
- Running the installer a second time must change nothing.
- Long downloads and builds at nice -n 19. Check free disk first: LEAN-1's Mathlib cache step fetched 8908 files. Put the test where there is room.
- Follow ~/CLAUDE.md and records/README.md as LEAN-3 did. deploy/ adds no module under ClassicalLean/. If the gates or the records protocol do not fit a non-Lean folder, say so in the report rather than bending either.
- Add HANDOFF.md section 6's dated line for the LEAN-3 push: 2026-10-07 15:32 EDT, Dustin, `ea592cf..299cc09 prove-disc-biquadratic -> master`, from his terminal. LEAN-3-report.md says each push gets one.

## The fresh-machine test

- Prefer a real fresh system. If podman or docker runs a container as dustin without sudo, use a fresh Ubuntu container with only git, curl, python3 and ca-certificates added, and the bare repo mounted read-only. If neither works without sudo, use a throwaway HOME started with an empty environment, so elan, the toolchain, the clone and the cache all start from nothing.
- Say which one you used and what it cannot show. A throwaway HOME shares DSMain's system packages and dustin's user manager; a container may have no systemd.
- Where the timer cannot run, use an installer option that skips enabling it, and check the generated unit files with `systemd-analyze --user verify`.

## Done means

1. The from-scratch install ends with its own status file, and its line 1 matches DSMain's line 1 from step 0 in commit, theorems written, constants checked, sorry and axioms. Show both lines.
2. A second installer run in the same place changes nothing. Show how you checked, for example sha256 of every installed file before and after.
3. One forced failure: with a prerequisite hidden (for example git removed from PATH), the installer stops with its one-line message and a non-zero exit, and leaves nothing half-installed. Say what you checked.
4. DSMain runs the packaged copy. Install it over LEAN-2's hand-made files with DSMain's config, keeping the old script and both units beside them with a `.pre-lean4` suffix as the undo. Then `systemctl --user start lean-nightly.service` gives the same line 1 as step 0 (apart from the time), and `systemctl --user list-timers lean-nightly.timer` still shows 03:30.
5. The fresh-test container or throwaway HOME, with its multi-gigabyte cache, is removed once 1 to 3 are recorded.
6. A report at /opt/datasphere/lane/inbox/threads/staging/LEAN-4-report.md with, in this order: Dustin's one paste if linger is off; the plan, written before building; one line per file in deploy/; the outputs for 1 to 4; the commits on package-nightly (hash and message); what was not tested; the undo for 4; and the one command Dustin would run to push when he decides: `git -C ~/lean/classical-lean push origin package-nightly:master`

If you cannot finish in this session, stop at a clean point: commit what works, leave DSMain on LEAN-2's script (do not do Done-means 4 half-way), remove the worktree only if it holds nothing uncommitted, and write the report with what is done and what the next session should start with.
