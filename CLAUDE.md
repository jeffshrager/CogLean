# Working on CogLean

CogLean is a Mathlib-style library of cognitive theory in Lean 4 (see `README.md`). Theories are stated as **cognitive** propositions (postulates), not as programs, and the phenomena are proved from them. Write about the library and the theories, not about history.

## Build

- Lean 4.35.0 via elan in `~/.elan`: `export PATH=$HOME/.elan/bin:$PATH`.
- Each theory is a Lake project (currently `EPAM/`): `cd EPAM && lake build`.
- Core Lean only so far, no Mathlib (ACT-R may change that).
- Every theorem fully proved: no `sorry`; `#print axioms` shows only `propext`, `Quot.sound`, `Classical.choice`.
- Generated files: `EPAM/Epam/ListA.lean` (from `EPAM/gen_lista.py`, run in `EPAM/`) and `EPAM/Epam/Fig41Alt.lean` (from `EPAM/analysis/gen_alt.py`, run in `EPAM/analysis/`). Edit the generators, not the outputs.
- `.lake/` is excluded through `.git/info/exclude`; the owner's global gitignore ignores `.gitignore` files, so don't rely on one.

## Conventions

- Commit after every successful major change without asking. Push only when asked.
- Session summaries: a new file per checkpoint, `seshsums/YYYYMMDD_HHMM_seshsum.md`, then commit (and push when asked).
- Prototype in Python with semantics identical to the Lean definitions when iterating on experiments (see `EPAM/analysis/robustness.py`), then certify in Lean with `decide`.
- Open work is tracked in `OPEN_ISSUES.md`.
