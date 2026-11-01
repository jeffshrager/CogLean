# Device learning: retrieved views and theory revision

A learner figures out a microwave without instructions, after Shrager (1987). The current theory predicts what the keys do. When a prediction fails, a cue retrieves a view and view application merges it into the theory. The cue is a key's label or the display, and any memory can do the retrieving.

Shrager, J. (1987). Theory change via view application in instructionless learning. *Machine Learning*, 2, 247–276.

```sh
cd DeviceLearning && lake build    # builds CogLib, then this package; core Lean only
```

## What is general (CogLib)

- **`Process/TheoryExecution`:** predictions are read off a theory. Each pressed key's function slot is a term, and its denotation, which is task data, acts on a device state. A prediction depends only on the pressed keys' function slots (`predict_congr`).
- **`Process/ViewRetrieval`:** recognize a cue, retrieve a view, apply it, with any memory.
  - `confusion_gives_neighbours_view`: a confused cue brings in its neighbour's view.
  - `view_of_determinate`: a determinate memory brings in one view per cue.
  - `view_confusion_pattern`: the confusion-error pattern stated for multi-digit addition (`Phenomena/ConfusionErrors`) holds here, for a different mechanism, under the conditions named.
- **`Process/TheoryRevision`:** the learning loop is an instance of the decision cycle with impasses and repairs (`Process/ProblemSolving`), not a new control structure.
  - A failed prediction is an impasse (`impasse_iff_fails`).
  - A repair retrieves a view by a cue and applies it.
  - A correct theory is never revised (`correct_theory_stable`).
  - With a determinate memory, every revision by a cue adopts the same retrieval (`revise_same_of_determinate`).
- **`Phenomena/DeviceLearning`:** `gardenPath` and `perseverates`, defined over the sequence of interpretations a learner adopts.

## The microwave (this package; all of it illustrative)

- **The device:** TIME COOK, CLOCK, 9, 0, START. After TIME COOK, 9 0 START cooks for 90 seconds. After CLOCK, 90 is an invalid time.
- **The theory:** the digits and START are understood. TIME COOK and CLOCK share an operation type whose function is unknown.
- **The views:** SET-A-TIME (the key sets a time of day) and DURATION (the key sets a cooking time).
- **Prior knowledge:** a VCR's SET TIME key, stored with SET-A-TIME, and a kitchen timer, stored with DURATION.
- **The two memories:**
  - EPAM's net notices the countdown first, so it takes both key labels for SET TIME (`net_facts`).
  - ACT-R's memory retrieves gradedly (`act_graded`).

**Sessions** (four decision cycles; exact, by `decide`):

| | Garden path | Solved | Perseverates |
|---|---|---|---|
| EPAM, consults the label and the display | 1/2 | 1 | 0 |
| ACT-R, the same | 125/1219 ≈ .10 | 1050/1219 ≈ .86 | 25/1219 ≈ .02 |
| EPAM, consults only the label | 0 | 0 | 1 |
| ACT-R, the same | ≈ .24 | ≈ .90 | ≈ .10 |

The EPAM label-only learner perseverates for certain because EPAM's memory is determinate (`epam_revisions_same`, an instance of the general theorem). ACT-R's memory is not determinate, and its graded retrieval escapes.

**Confident misinterpretation** (`epam_confusion_pattern`): with EPAM's net, both labels bring in SET-A-TIME. CLOCK's episode is then always predicted correctly, and TIME COOK's always wrongly, with no exploration. This is `ConfusionErrorPattern`, the phenomenon first stated for arithmetic.

Not yet modelled (OPEN_ISSUES #26):
- learning in memory (revisions do not study);
- the full 1987 mechanisms;
- splitting an operation type when its keys behave differently;
- retrieval as use.
