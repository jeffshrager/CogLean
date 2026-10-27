# A blind simulation of the multi-digit model

The Lean theorems show that the predictions follow from the Lean definitions. They don't show that those definitions say what the prose model says. This directory checks that link with a second, independent implementation.

1. **`SPEC.md`**: the model in prose, with no Lean names, theorems or predictions.
2. **`PREREG.md`**: what each theorem predicts for the simulator's logs, and how each check is judged. It was committed before the simulator existed.
3. **`mdsim.py`**: written by a fresh agent that was given `SPEC.md` and nothing else. It worked in an empty directory, and its tool calls were audited: it read only files it had written. It is committed unmodified, with its `IMPLEMENTATION_NOTES.md` (its choices on the open points) and `selftest.py`.
4. **`../Export.lean`**: Lean's exact trial distributions for four instances (`instances/lean_exact.json`). Run it with `lake env lean --tstack=4000000 Export.lean`; it takes about 3 minutes.
5. **`compare.py`**: generates random instances, runs the simulator, applies the preregistered checks, and writes `RESULTS.md`. Run it with `python3 compare.py`; it takes about 2 minutes. `--quick` is a smaller run.

## Findings

**1. Agreement.** Every check whose hypothesis was met passed:
- Lean's exact distributions on 4 instances: 243 outcome frequencies;
- Predictions 1–5, 9 and 10 on 30 random instances;
- Predictions 13 and 15 on the rich encoding;
- Predictions 7, 11 and 12 under learning.

The prose spec and the Lean formalization agree on recognition, EPAM learning, DOA retrieval, the fingers and counting backups, and the carrying algorithm. The one exception is finding 3.

**2. Five predictions were never tested.** Predictions 6a, 6b, 14, 17 and 18 were vacuous: their hypotheses never held in any learned net. Each needs the path to test *every* feature of a digit or a column: 4 bits, 9 thresholds, or 100 fact features. EPAM grows one test per confusion, so paths are short. The theorems are true, but they say little about the nets EPAM actually learns. They need versions about the features that *are* tested. For example: "the tested bits of a digit restrict it to a set D, so the error is bounded by the spread of D", or "a tested fact feature that reads 1 fixes the fact".

**3. Zero total strength.** In Lean, sampling from associations with total strength 0 divides by 0. The trial then has probability mass 0: no outcome at all. The theorems avoid this case by assuming total ≠ 0. The simulator reads it as retrieval exhausted, going on to the columns. That is also the natural reading of the model, and it is what makes the most natural choice of O2 (a newly discriminated problem starts with no associations) work. That case lies outside every Lean theorem. This is a gap in the formalization, not a simulator bug.

**4. Learning depends on a choice the model leaves open.** The table in `RESULTS.md` breaks down the 153 discriminated problems by O2, the initial associations of a newly discriminated problem:
- **No associations:** 40 of 48 follow the predicted sequence: a confident error, then column work, then fluent, correct retrieval.
- **Only the correct answer:** the problem goes straight to fluent, correct retrieval.
- **A copy of the neighbour's associations:** the confusion's error is perpetuated. It is stated, strengthened, and stated again (7 of 44 trapped, 35 mixed).

The sequence predicted from Predictions 4, 11 and 12 holds only under some readings of the model. Which one is right is a substantive question about the theory.

**5. The implementer's other readings matched Lean's.** Single-digit associations belong to ordered pairs, as `SC.Problem` does. Whole-route strengthening uses the associations that were retrieved from. These ambiguities were found blind and resolved the same way.
