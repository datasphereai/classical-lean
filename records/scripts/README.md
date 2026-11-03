# records/scripts/ and records/plan/ — the files the docstrings cite

The library's module docstrings cite check scripts, saved outputs, witness notes and plan documents by the
names the orders used. This table maps each cited name to the copy kept here. A line number after a module
name is the line of that module's docstring where the citation sits, at the commit that made this table.

| as cited in a docstring | file here | origin (order; box or lane path) | bytes | sha256 |
|---|---|---|---|---|
| `checks.py`, with order LEAN-23 named on the line (Simpson line 41, LinearProgram 55, EulerMaclaurin 46, MinMax 68) | `records/scripts/LEAN-23/checks.py` | LEAN-23; DSMain `~/lean/lean23-checks/checks.py` | 15481 | `f8f51fcd455ba5c608fc71159058c7b4427892614b343dbb3e491e7adcdcba67` |
| `checks.py`, with order LEAN-24 named on the line (Sufficiency 140, NeymanPearson 79, JamesStein 48, GlivenkoCantelli 47, MethodOfTypes 68) | `records/scripts/LEAN-24/checks.py` | LEAN-24; DSMain `~/lean/lean24-checks/checks.py` | 16908 | `b20201bf10f4d805a5574669c2c12e024f0f5f7f8e6c8f2b167276115fcc1b8f` |
| `~/lean/lean25-checks/checks.py` (FiniteGame 88, ArbitrageCycle 57, Tremaux 76) | `records/scripts/LEAN-25/checks.py` | LEAN-25; DSMain `~/lean/lean25-checks/checks.py` | 10522 | `8451818148d5162d1f914de124d0afc3f10913eb3febcb77ae26a380d88f6116` |
| `checks.py`, with order LEAN-27 named on the line or in the bullet list it sits in (GeneralizedLeastSquares 43, EffectiveSampleSize 77 and its bullets at 80 and 83, MinMax 39, Kantorovich 47) | `records/scripts/LEAN-27/checks.py` | LEAN-27; DSMain `~/lean/lean27-checks/checks.py` | 8938 | `d35de1f56e94bc49d69df19c5c684a27b0f4573dabc80a63ec70e872999cafc7` |
| `chk2.out` (Kantorovich 47; the saved output of LEAN-27's `checks.py`) | `records/scripts/LEAN-27/chk2.out` | LEAN-27; DSMain `~/lean/lean27-checks/chk2.out` | 2916 | `c23af4bde3778bbb784c13995e746087100ed1aef3b5b66984d6a518de7fb911` |
| `checks.py`, with order LEAN-28 named on the line (GamblersRuin 85, FiniteGame 87); its line labelled `85.affine` is LEAN-28's report line 116 | `records/scripts/LEAN-28/checks.py` | LEAN-28; DSMain `~/lean/lean28-checks/checks.py` | 17271 | `cafa7dc8519697738e08ad2e8b1b441642aeb89fc30650430db1318ab10f25cb` |
| `LEAN-28-check80b.py` | `records/scripts/LEAN-28/check80b.py` | LEAN-28; lane `inbox/threads/staging/lean/LEAN-28-check80b.py` | 3257 | `e22807bc6b50368749b4e00f24aae2e4932f2684fd2894d5ce8c131aded21e48` |
| `lean/LEAN-29-checks.py` ("order LEAN-29's exact checks", GamblersRuin 133) | `records/scripts/LEAN-29/checks.py` | LEAN-29; lane `inbox/threads/staging/lean/LEAN-29-checks.py` | 21676 | `8e82051348b8e71e67636322dd406d0f791c319d9313e9b993acf578ad023dc5` |
| `checks95.py` ("the order's own script", GamblersRuin 133) | `records/scripts/LEAN-29/checks95.py` | LEAN-29; DSMain `~/lean/lean29-checks/checks95.py` | 3497 | `b531f3e0326617e7f1f81fe9dcbc9c138e1c50ffb2d708a203cf61388e96c3ee` |
| `lean/LEAN-30-checks.py` | `records/scripts/LEAN-30/checks.py` | LEAN-30; lane `inbox/threads/staging/lean/LEAN-30-checks.py` | 29272 | `6af2e0421ffd01df5a8ea28f094945b2173b5729356c3ac500e06fc3c02ddcf7` |
| `lean/LEAN-31-checks.py` | `records/scripts/LEAN-31/checks.py` | LEAN-31; lane `inbox/threads/staging/lean/LEAN-31-checks.py` | 26708 | `0038352f642b79804c03d9da731efd4ac8857ae8ab38c1f0326e3c7f586dc936` |
| `checks109.py` | `records/scripts/LEAN-32/checks109.py` | LEAN-32; DSMain `~/lean/lean32-checks/scripts/checks109.py` | 2766 | `12b8eb0b66644d5846b5c1f7b100424b3c72b75ef8f0727aa76f52824bb4e5bf` |
| `lean/LEAN-36/data/witnesses.txt` | `records/scripts/LEAN-36/witnesses.txt` | LEAN-36; lane `inbox/threads/staging/lean/LEAN-36/data/witnesses.txt` | 6578 | `2bc14e815ecf3ceb8f2bbe34268aa2831ca7884ed7015fe6f683e838dc719d17` |
| `w143-runs.py` | `records/scripts/LEAN-37/w143-runs.py` | LEAN-37; DSMain `~/lean/lean37-checks/w143/runs.py` | 448 | `45f469e02d7ff6b2dd5a1c1486f6969863cc62a6dc5221be54d056bf004c5e77` |
| `w145-cycles.py` | `records/scripts/LEAN-37/w145-cycles.py` | LEAN-37; DSMain `~/lean/lean37-checks/w145/cycles.py` (LEAN-37 ruling-1's pin) | 693 | `d5f62c79684d9361f868b987e249aea1fbcab551a521d3088c1477d012ae11e0` |
| `w149-series.py` | `records/scripts/LEAN-37/w149-series.py` | LEAN-37; DSMain `~/lean/lean37-checks/w149/series.py` (LEAN-37 ruling-1's pin) | 1139 | `0e8145adf49f11793ba7e0a56c694314def7e7da5fe150dde575c7613502fea3` |
| `MATH-PLAN-library-2-checks.py` (the plan's search script) | `records/scripts/MATH-PLAN-library-2/checks.py` | the plan's search script; DSMain `~/lean/lean27-checks/MATH-PLAN-library-2-checks.py` (byte-identical to lane `inbox/threads/staging/MATH-PLAN-library-2-checks.py`) | 89055 | `92eedbc6598361a06a50bdf3a1b4fa1698c1d1d7a3dfe783cc79dd9c1c38307e` |
| "the plan", "the plan's row" followed by a number (a numbered row of this file) | `records/plan/MATH-PLAN-library-2.md` | the plan; lane `inbox/threads/staging/MATH-PLAN-library-2.md` | 71296 | `6b265caaf3b2ce89d3be4349c94d684fd4b70c8af7f8b8f35a7986498aae7166` |
| `MATH-PLAN-library-2-bridges-2.md`; "bridge" or "row" followed by a number from 154 to 175 (a row of this file) | `records/plan/MATH-PLAN-library-2-bridges-2.md` | the bridges file as of order LEAN-39 (rows 154 to 175), a dated snapshot; lane `inbox/threads/staging/lean/MATH-PLAN-library-2/MATH-PLAN-library-2-bridges-2.md` | 70695 | `4fd72d941e5f057ca1ad1ad65b2cd899601a9f08b3e2db816218e1010c08bae5` |
| the folder `~/lean/lean29-checks/` (GamblersRuin 133: "kept with the order's evidence") | `records/scripts/LEAN-29/` (both files above) | LEAN-29; DSMain `~/lean/lean29-checks/` | — | — |
| `tools/check_sorry.py` | `tools/check_sorry.py` | this repository | — | — |
| `tools/banned_vocab_scan.py` | `tools/banned_vocab_scan.py` | this repository | — | — |
| `ROADMAP.md` | `ROADMAP.md` | this repository | — | — |
| `HANDOFF.md` | `HANDOFF.md` | this repository | — | — |
| `records/rounds/20261028T194100Z__round-76-interlacing-minimax-lp-runs-prices-progeny.md` | that file under `records/rounds/` | this repository | — | — |
| `reviews/stmt-j2.md` | none | cited by Wolstenholme line 18 (order G-10, September 2026); not in this repository, its history, the owner's records or the archived full-history bundle; the docstring's claim of a cold review has no surviving file | — | — |

These are the exact check scripts, outputs, witness notes and plan documents the library's docstrings cite,
copied unchanged from the orders' evidence (each sha256 above is the source's), run at the time of their orders
and not maintained since (LEAN-23's needs numpy). The bridges file is a snapshot dated to order PUBLIC-1 and
grows in the owner's private copy. A docstring that calls one of them "outside the repository" or "in the
lane" was written before this copy. "The lane" is the owner's private work-order folder. "The lane's
API-CREDIT-1 work" names the order under which proof drafts (ids like `d127-r1-s2`, not in the repository)
were bought from the Anthropic Batch API in October 2026 and then adapted by the sessions the docstrings name.
A host name in a docstring is one of the owner's machines. Nothing in a proof depends on any of this.
