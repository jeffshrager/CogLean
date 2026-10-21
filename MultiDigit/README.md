# Multi-digit addition in CogLean

The third instance in CogLean (`../README.md`) combines the first two. EPAM's discrimination-net recognition is joined to the distributions-of-associations model's retrieval (`../StrategyChoice/`), to cover 3-digit addition. A familiar problem is recognized and its answer retrieved. Otherwise, or if retrieval fails, the answer is computed column by column. When the net hasn't learned to tell two problems apart, it confuses them, and retrieval runs on the wrong problem's associations.

The predictions are **deduced**, not simulated. Every postulate is a parameter: the encoding, the net, the strengths, the criterion, the search length and the backup. Every prediction holds for all of them, and is proved by composing EPAM and DOA results already in CogLib.

```sh
cd MultiDigit && lake build    # builds CogLib too; core Lean only
```

- `MultiDigit/Postulates.lean`: the postulates M1–M4 and the trial.
- `MultiDigit/Phenomena.lean`: the predictions, among them:
  - confident errors, which confusion produces and DOA alone cannot: a retrieved, wrong answer with no extra backup use;
  - a confused problem gets its neighbour's answer;
  - same-sum and commuted confusions are harmless;
  - near misses within 200 or 20, set by which digits the net examines;
  - no interference with practiced problems.
- `MultiDigit/Example.lean`: one worked case, a check that the theorems apply.
- [`docs/PREDICTIONS.md`](docs/PREDICTIONS.md): every prediction with its full proof, the test it suggests and what it rests on.

Next: the column backup built from single-digit DOA trials with carries, and learning.
