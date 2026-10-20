"""CLOUD-MATH-2 job 1: restructure 150's statement file so [DecidableEq n] is bound where used."""
import sys
p = sys.argv[1]
s = open(p, encoding='utf-8').read()
reps = [
 ("""CLOUD-MATH-2): the namespace and docstrings, and, on the three private helpers whose statements do
not use the section's `[DecidableEq n]`, `omit [DecidableEq n] in` with `classical` in the proof
where the proof needs it, and the binder `[DecidableEq n]` written on `pinv`, which before took it
only through `exists_penrose`, so that the definition keeps the draft's type.
-/""",
  """CLOUD-MATH-2): the namespace and docstrings, and `[DecidableEq n]` bound where it is used. The
draft's section `variable` line gave it to the three private helpers, whose statements do not use
it; here the section takes it only after `pinv`, the helpers' proofs use `classical` where they need
it, and `pinv`, which in the draft took it only through `exists_penrose`, binds it itself, so that
`pinv` and every theorem about it keep the draft's types.
-/"""),
 ("variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]\n\nomit [DecidableEq n] in\n",
  "variable {m n : Type*} [Fintype m] [Fintype n]\n\n"),
 ("  sorry\n\nomit [DecidableEq n] in\n/-- Every real", "  sorry\n\n/-- Every real"),
 ("  sorry\n\nomit [DecidableEq n] in\n/-- The four Penrose equations have", "  sorry\n\n/-- The four Penrose equations have"),
 ("""(`pinv_unique`).

The binder `[DecidableEq n]` keeps the draft's signature: the draft's `pinv` took the section's
instance through `exists_penrose`, whose statement does not use it, and with the instance omitted
there it is written here, so that `pinv` and every theorem about it keep the draft's types. -/
noncomputable def pinv [DecidableEq n] (A : Matrix m n ℝ) : Matrix n m ℝ :=
  Classical.choose (exists_penrose A)
""",
  """(`pinv_unique`).

The binder `[DecidableEq n]` keeps the draft's signature: the draft's `pinv` took the section's
instance through `exists_penrose`, whose statement does not use it. -/
noncomputable def pinv [DecidableEq n] (A : Matrix m n ℝ) : Matrix n m ℝ :=
  Classical.choose (exists_penrose A)

variable [DecidableEq n]
"""),
]
for a, b in reps:
    if s.count(a) != 1:
        sys.exit(f'not found once: {a[:60]!r}')
    s = s.replace(a, b)
open(p, 'w', encoding='utf-8').write(s)
print('ok')
