# Implementation notes (blind implementation)

Files: `mdsim.py` (simulator), `example.json` (smoke-test parameters),
`selftest.py` (hand-checked tests; `python3 selftest.py`, 66 checks, all pass).

## Open choices (parameters under `open_choices`)

- **O1** (`"true"` default | `"stored"`): whole-route "correct" is judged against
  the true sum of the presented problem x. `"stored"` judges against the sum of
  the recognized problem y. Note the log field `correct` is always vs x's true sum.
- **O2** (`"zero"` default | `"copy"` | `"table"` | `"correct"`): initial whole
  associations of a newly discriminated x.
  - `zero`: answer list = `answers`, all strengths 0. x is then recognized but
    retrieval is exhausted (T = 0) and it goes to columns; with O3=`stored` it
    builds its own associations from column answers.
  - `copy`: copy of y's associations, taken *after* this trial's step-2
    strengthening. Warning: with the example parameters this traps x on y's
    wrong answer forever (strength > c, keeps getting +inc). This is why it is
    not the default.
  - `table`: x's entry in `whole` (missing answers 0) over `answers`.
  - `correct`: `answers`, all 0 except x's true sum = `o2_strength` (top-level
    parameter, default 1/2).
  New associations are created only if the net actually changed and x has none yet.
- **O3** (`"stored"` default | `"none"`): after a columns-route trial, if x is
  stored in the net (i.e. has whole associations), the columns answer's
  strength in x's associations gets +inc (+2*inc if it equals x's true sum),
  added with strength 0 first if absent. Not stored -> nothing.
- **O4** (other underdetermined points, my choices):
  1. Single-digit associations are per *ordered* pair (3+4 and 4+3 separate,
     keyed by first-addend digit, second-addend digit).
     `open_choices.single_commutative: true` makes them shared.
  2. Total strength T = 0 (e.g. a stored problem with no associations): retrieval
     is exhausted immediately with 0 searches (logged `searches: 0`). For fingers,
     T' = elab/(1+elab) > 0 always, so fingers can always draw.
  3. Drawing: one `rng.random()` u per search; answers scanned in insertion order
     of the association table (the `answers` list order, then any answers added
     later); zero-strength answers skipped; first answer with u < cum/T (as float).
  4. Counting: one `rng.random()` per object: u < qs skip; u < qs+qd count twice;
     else once. RNG call order per column: retrieval searches, then the one
     fingers search (if reached), then counting draws.
  5. Learning step order: single-digit strengthening, whole strengthening,
     discrimination (+ O2), then O3.
  6. A familiar problem that is listed but absent from `whole` gets all-zero
     associations. Answers present in a `whole` table but not in `answers` are
     kept (appended after `answers`).
  7. When a test node replaces a terminal and x is learned, x is the problem
     itself, so x is always recognized as itself thereafter (images never move).
  8. Columns are added in the order units, tens, hundreds (the RNG order and the
     log order).
  9. `fingers` stage: the temporary strength of d+e is (s+elab)/(1+elab); if d+e
     is missing from the answer list it is treated as 0. The stated answer is the
     drawn one if its temporary strength > c1 (it can be a wrong answer if that
     answer's strength is large).
  10. `seed` defaults to 0, `repeats` to 1, `learning` to false, inc/inc1 to 0.
  11. Floats in the JSON are converted via their repr (0.05 -> 1/20).

## Ambiguities noticed

- Whether whole-route strengthening's "associations that were used" means y's
  (I used y's, as the spec literally says).
- Whether a wrong whole-route answer when x is recognized as itself (y = x)
  should do anything to the net: learning x's own code is a no-op, so
  `net_learned` is false.
- "Strengthening (single-digit) ... correct for the column (d + e)": I take
  correct as the digit sum d+e itself, not including any carry.
- Behaviour when T = 0 is not defined by section 4 (it assumes T > 0); see O4.2.
- Whether d+e and e+d share associations (O4.1).
- The `searches` field when not recognized: 0.
- Default single answer list if `single.answers` is omitted: I use 0..18.
- With O2 = copy, discriminated problems can get stuck; the spec does not say
  whether that is intended.

## Files read

Only files I wrote myself in this directory: `mdsim.py` (via a small
in-place edit script), `example.json`, `selftest.py`, and the `log.jsonl` I
generated (since deleted). No other files were read.
