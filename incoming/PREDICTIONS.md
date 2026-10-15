# Predictions for End check 1 (order CLOUD-MATH-1, rule 6)

Written by Claude Code cloud session `session_01HV9mMLe9qSe13nN9hMyEBJ` once every module's text
was final (after the reviews: items 139, 136, 131 and 137 PASS with no finding; item 135 PASS with
one MINOR docstring finding, fixed and confirmed by a fresh reviewer), and committed before End
check 1, at the branch state `cc65251` plus this commit (which also removes `incoming/README.md`,
no draft being left). Until this commit the axiom gate
was not run on the new modules, no census of theorem constants was run on them, no CI log was
read (only the step results of `gh run view --json jobs`), and the job count of a whole-library
`lake build` was not read (whole-library builds ran during the work, ahead of each vacuity-gate
run, with their output discarded unread).

The five gates run on the clean tree, in the order's order. Each prediction below, with how it
was made.

## 1. `lake build`

**Predicted: rc 0, `Build completed successfully (4175 jobs).`, 0 lines with `warning:`.**

How: the job count was measured at 4170 at `e2fac6d` (setup build). The import closure of
`ClassicalLean` was counted from the source files' import headers (a script that follows every
`import` / `public import` line from `ClassicalLean.lean` through the repository and
`.lake/packages`, stopping at the toolchain's own `Init`/`Std`/`Lean`): 4004 modules at
`e2fac6d`, so 166 jobs beyond the modules; the same script on the final `ClassicalLean.lean`
gives 4009, the 5 new modules and no Mathlib file new to the closure (each new Mathlib import,
`Mathlib.Probability.UniformOn`, `Mathlib.Analysis.InnerProductSpace.PiL2`,
`Mathlib.Probability.Martingale.Convergence` and `Mathlib.Probability.Kernel.IonescuTulcea.Traj`,
is already in the closure at `e2fac6d`). The model "jobs = closure + 165" was checked against the
five per-module builds of the work (`lake build <Module>`: 1876, 2339, 2560, 2516, 3052 jobs
against closures 1711, 2174, 2395, 2351, 2887; 165 each); the library target adds one job more
(4170 = 4004 + 166). 4170 + 5 + 0 = 4175. Warnings: each module built alone with 0 warnings.
The script (`closure.py`, sha256 `874913c99f805d541f12c97a12a9fab2d9d75493160f1276d1b333fa3e2198f6`)
is in the appendix.

## 2. `lake env lean tools/AxiomGate.lean`

**Predicted: PASS, 3302 theorem constants (3228 + 74), 0 scoped exceptions.**

How (blind, by hand from the source; no Lean count of the new modules). The model of which
declarations are theorem constants was calibrated on three toy files outside the library (not
on the new modules): written `theorem`/`lemma` (private ones included, counted by user name as
`tools/AxiomGate.lean` does); one auxiliary `<thm>._proof_1_k` per `omega` call in a theorem
body; one `<def>.eq_1` per definition of the module unfolded by `simp`, `simp only` or `rw`
(not by `unfold`), private definitions included, none for a definition whose `eq_1` already
exists in an imported module (`shannonEntropy`: `Entropy.lean` unfolds it already); the
`_proof_` lemmas of a definition with proof fields; no constant from proofs inside a theorem's
statement, from `simp [h]` with a local hypothesis, from `field_simp`, `positivity`,
`nlinarith`, `norm_num`, `decide`, `split_ifs` or `unfold`, and none from `example`s.

| module | written theorems | `omega` auxiliaries | `eq_1` / `_proof_` | predicted |
|---|---|---|---|---|
| `Probability/Reflection` | 18 | 14 | `walk`, `flipFrom`, `step` `eq_1` (3) | 35 |
| `Analysis/StatePrices` | 2 | 0 | `sysMap._proof_1`, `_proof_2` (2) | 4 |
| `InformationTheory/HanInequality` | 12 | 3 | `marg.eq_1` (1) | 16 |
| `Analysis/FrankWolfe` | 4 | 1 | none | 5 |
| `Probability/PolyaUrn` | 11 | 2 | `urnShare.eq_1` (1) | 14 |
| **total** | 47 | 20 | 7 | **74** |

Range, for the parts the model is least sure of: `field_simp` in `fw_general` (LEAN-24 measured
0 to 8 `_simp_` helpers per call; the calibration 0), and `congr_simp` or `eq_def` lemmas not
seen in the calibration: 74 to 82.

Not blind, said plainly: the cold review of `Analysis/StatePrices` (136) listed that module's
constants in its text (4 theorem constants among them), and the cold review of
`InformationTheory/HanInequality` (131) gave "constants from the module: 20" (all kinds, not
only theorems). Both reviews were read before this file was written; the counts above come from
the model and were not changed to fit them.

## 3. `python3 -I tools/check_sorry.py`

**Predicted: PASS, 127 files under `ClassicalLean` (122 + 5).**

## 4. `lake env lean tools/VacuityGate.lean`

**Predicted: PASS — `no vacuous theorems in [ClassicalLean] (1 reviewed helpers and 0
VACUOUS-PENDING on tools/vacuity_reviewed.txt); rule 5 ran out of its 400000 heartbeats on 0
theorems`.** No new entry in `tools/vacuity_reviewed.txt`; no UNCHECKED, no KERNEL-REJECTED.
(The gate was run during the work, as rule 6 allows, with the modules imported: PASS with the
same line, before the reviews.)

## 5. `python3 -I tools/check_records.py`

**Predicted: PASS, 127 modules under `ClassicalLean`, every one named in the records, 82 files
searched, 1 named exemption (`Simplex/Hessian.lean`).**

## Appendix: the import-closure script

```python
import os, re, sys, subprocess
ROOT='/home/user/classical-lean'
pkgs = {}
pk = ROOT + '/.lake/packages'
srcroots = [ROOT] + [os.path.join(pk, d) for d in os.listdir(pk)]
def find(mod):
    rel = mod.replace('.', '/') + '.lean'
    for r in srcroots:
        p = os.path.join(r, rel)
        if os.path.exists(p): return p
    return None
imp_re = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»]+)', re.M)
def imports(path):
    txt = open(path, encoding='utf-8').read()
    out = []; i = 0; n = len(txt)
    while i < n:
        if txt.startswith('/-', i):
            depth = 0
            while i < n:
                if txt.startswith('/-', i): depth += 1; i += 2
                elif txt.startswith('-/', i):
                    depth -= 1; i += 2
                    if depth == 0: break
                else: i += 1
            continue
        if txt.startswith('--', i):
            j = txt.find('\n', i); i = n if j < 0 else j + 1; continue
        if txt[i].isspace(): i += 1; continue
        j = txt.find('\n', i); line = txt[i: n if j < 0 else j]
        m = re.match(r'(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»]+)', line)
        if m: out.append(m.group(1)); i = n if j < 0 else j + 1; continue
        if line.strip() in ('module', 'prelude'): i = n if j < 0 else j + 1; continue
        break
    return out
def closure(roots_text):
    seen=set(); core=set(); stack=list(roots_text)
    while stack:
        m=stack.pop()
        if m in seen or m in core: continue
        p=find(m)
        if p is None:
            core.add(m); continue
        seen.add(m)
        stack.extend(imports(p))
    return seen, core
which = sys.argv[1]
if which == 'old':
    txt = subprocess.run(['git','show','e2fac6d:ClassicalLean.lean'],capture_output=True,text=True,cwd=ROOT).stdout
else:
    txt = open(ROOT+'/ClassicalLean.lean').read()
roots = imp_re.findall(txt)
seen, core = closure(roots + [])
seen.add('ClassicalLean')
print(which, 'noncore modules in closure (incl. ClassicalLean root):', len(seen))
open(f'/tmp/claude-0/-home-user-classical-lean/19408406-f39d-5a72-8f6f-124d894b525a/scratchpad/closure-{which}.txt','w').write('\n'.join(sorted(seen))+'\n')
```
