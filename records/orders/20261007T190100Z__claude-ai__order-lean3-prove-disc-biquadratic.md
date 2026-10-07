<!-- Copied verbatim on 2026-10-07 from /opt/datasphere/lane/inbox/threads/staging/LEAN-3-order.md (DSMain lane), per records/README.md rule 2. The copy was made after the work began, not before: the order arrived as a lane file and this repository copy is late. -->

# LEAN-3: close the open hole - prove disc_biquadratic_23

From claude-ai, 2026-10-07 15:01. Dustin's words: "the first thing I want to do after this is close the open hole in the library so that it is fully proven." For the same plain Claude Code session on DSMain, as dustin. Follows LEAN-2-report.md (85a66254): the nightly check is live and shows 1 axiom.

Goal: the classical-lean library has no project axioms. `disc_biquadratic_23 : (discr K1).natAbs = 2304` in ClassicalLean/NumberTheory/CompositumDiscriminant.lean:301 (|disc Q(sqrt 2, sqrt 3)| = 2304 = 2^8 * 3^2) becomes a theorem with a real proof, and the two theorems that rest on it (K1_K2_isCoprime, disc_K_eq_240_pow_4) rest only on propext, Classical.choice and Quot.sound.

Scope:
- As dustin, no sudo, in ~/lean/classical-lean. Do not touch /opt/datasphere-mcp/, the store, or credential files.
- Work on a new local branch, prove-disc-biquadratic. Commit as you go. Do not push: pushing to /data/git/classical-lean.git is Dustin's call at the end, because his working copy on helios shares that repo.
- The repo has no CLAUDE.md of its own. (Corrected 2026-10-07 15:20: the first version of this order said to follow "the repo's own CLAUDE.md"; none exists on DSMain or in helios's ~/work/classical-lean.) Follow ~/CLAUDE.md on DSMain, which this session already loads, including its banned-vocabulary grep, and the naming style of the existing files.
- Before building, read the file and what K1 is, and write a short plan at the top of the report: the route you will take and why. Candidate routes, for you to judge, not a prescription: find an explicit integral basis (for example 1, sqrt2, sqrt3, (sqrt2 + sqrt6)/2) and prove it spans the ring of integers, using Mathlib's tools for this (the discriminant bound discr_mul_isIntegral_mem_adjoin, and the Eisenstein-at-p lemmas Mathlib uses for the cyclotomic ring of integers); or get the value from the discriminants of the quadratic subfields if Mathlib has what that needs. Check what Mathlib v4.34.0 actually provides before choosing.
- No sorry, no new axiom, no native_decide outside the directories the repo already permits. Every gate must pass.
- Keep long builds at nice -n 19. Work for as long as the proof needs; this may be the hardest single item in the library. If a route fails, say why in the report and try the next one.

Done means:
1. The axiom declaration is gone and a theorem with the same name and statement proves it.
2. `lake build` passes, and all three gates pass, with the axiom gate showing 0 scoped exceptions.
3. ~/bin/lean-nightly.sh is tightened so any project axiom (more than 0) means ATTENTION. Then run `systemctl --user start lean-nightly.service` on the branch build and show the LEAN.md line 1. It should read `Lean: OK - ... 0 axioms`. Put the real clone back on master afterwards if the nightly job needs master, and say how you handled that.
4. A report at /opt/datasphere/lane/inbox/threads/staging/LEAN-3-report.md: the route taken, the commits on the branch (hash and message), the gate output, and the one command Dustin would run to push the branch when he decides to.

If you cannot finish in this session, stop at a clean point: commit what builds, write the report with what is proven so far and what is left, and say what the next session should start with.
