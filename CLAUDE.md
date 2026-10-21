# Working on CogLean

CogLean is a Mathlib-style library of cognitive theory in Lean 4 (see `README.md`). Theories are stated as **cognitive** propositions (postulates), not as programs, and the phenomena are proved from them. Write about the library and the theories, not about history.

## Build

- Lean 4.35.0 via elan in `~/.elan`: `export PATH=$HOME/.elan/bin:$PATH`.
- `CogLib/` is the general library, a Lake package that imports no theory. Each theory is its own Lake package (currently `EPAM/` and `StrategyChoice/`) that requires CogLib by path: `cd EPAM && lake build` builds both.
- Keep the split clean: general constructs, general theorems, and theory-neutral phenomena go in CogLib; a theory's directory holds its postulates (as choices of CogLib constructs), its parameters, its experiments, and its phenomena theorems.
- Core Lean only, no Mathlib. Probabilities are core `Rat`; `decide +kernel` evaluates concrete rationals (plain `decide` gets stuck on them). Mathlib, when ACT-R needs `Real.log`/`exp`, goes in an `ACTR/` package only; CogLib stays core-only.
- `../ACT-R/` (outside the repo) is the ACT-R 7 standalone build: executables, tutorial (`.content/tutorial/`), docs; no module source.
- Every theorem fully proved: no `sorry`; `#print axioms` shows only `propext`, `Quot.sound`, `Classical.choice`.
- Generated files: `EPAM/Epam/ListA.lean` (from `EPAM/gen_lista.py`, run in `EPAM/`) and `EPAM/Epam/Fig41Alt.lean` (from `EPAM/analysis/gen_alt.py`, run in `EPAM/analysis/`). Edit the generators, not the outputs.
- `.lake/` is excluded through `.git/info/exclude`; the owner's global gitignore ignores `.gitignore` files, so don't rely on one.

## Conventions

- Commit after every successful major change without asking. Push only when asked.
- Session summaries: a new file per checkpoint, `seshsums/YYYYMMDD_HHMM_seshsum.md`, then commit (and push when asked).
- Prototype in Python with semantics identical to the Lean definitions when iterating on experiments (see `EPAM/analysis/robustness.py`), then certify in Lean with `decide`.
- Open work is tracked in `OPEN_ISSUES.md`.
