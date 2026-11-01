# Device learning: retrieved views and theory revision

A learner figures out a microwave without instructions, after Shrager (1987). The current theory predicts what the keys do. When a prediction fails, a cue retrieves a view and view application merges it into the theory. The cue is a key's label or the display, and any memory can do the retrieving.

Shrager, J. (1987). Theory change via view application in instructionless learning. *Machine Learning*, 2, 247–276.

```sh
cd DeviceLearning && lake build    # builds CogLib, then this package; core Lean only
```

## What is general (CogLib), in layers

1. **`Process/TheoryRevision`: learning by revision, over any theories, actions and responses.** It is an instance of the decision cycle with impasses and repairs (`Process/ProblemSolving`), not a new control structure. A `Reviser` supplies three things:
   - how a theory predicts the response to a sequence of actions;
   - how a cue revises a theory (any process, with any memory);
   - which cues an episode offers.

   Episodes are actions plus observed responses. Proved here, for any reviser:
   - a failed prediction is an impasse (`impasse_iff_fails`);
   - a correct theory is never revised (`correct_theory_stable`).
2. **`Process/ViewRevision`: one reviser, view application with retrieved views** (`viewReviser`, built on `Process/ViewRetrieval`). With a determinate memory, every revision by a cue brings in the same retrieval (`revise_same_of_determinate`).
3. **`Process/TheoryExecution`: one way a knowledge-net theory predicts.** Each action is a frame whose function slot's denotation acts on a state, in sequence.

Also general:
- **`Process/ViewRetrieval`:**
  - `confusion_gives_neighbours_view`;
  - `view_of_determinate`;
  - `view_confusion_pattern`, the confusion-error pattern of `Phenomena/ConfusionErrors`, here for view retrieval.
- **`Phenomena/TheoryChange`:** `gardenPath` and `perseverates`.

Nothing in CogLib mentions keys, devices or microwaves. Other revisers, such as rule induction or Bayesian updating over hypotheses, can plug into layer 1 and inherit its results.

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

## Decomposed views and differentiation (`Differentiation.lean`)

SET-A-TIME and DURATION are broken into parts. SET-A-NUMBER says the key enters a number. NUMBER-IS-A-TIME and NUMBER-IS-A-DURATION say what the number means. Each part is one slot of the keys' type, and interpreting a key takes two of them.

- **Composition:**
  - one view is not enough (`one_view_not_enough`);
  - two compose, in either order (`two_views_compose`);
  - replacing the meaning keeps "enters a number" (`revision_keeps_number`, an instance of `merge_keeps_unmentioned`).
- **Why splitting is needed** (`never_both_shared`, for every theory): if TIME COOK and CLOCK have one type and both enter a number, the theory predicts them alike. So no such theory predicts both cooking for 90 seconds and an invalid clock time.
- **Splitting (CogLib `Process/TypeSplit`):**
  - copying an action's type changes no prediction (`split_conservative`);
  - it separates the action from the type's other instances (`split_separates`).

  The learner splits when re-interpreting a shared type would break an episode it has already explained (conflict-driven differentiation, `viewSplitReviser`).
- **Sessions** (EPAM's net; episodes TIME COOK, CLOCK, TIME COOK; 12 cycles):

  | Learner | Knows both | Finishes | Oscillates |
  |---|---|---|---|
  | never splits | 0 | 5/6 | 5/6 (every one that finishes) |
  | splits on conflict | 5/6 (every one that finishes) | 5/6 | 0 |

These results concern representation, so the sessions use EPAM's net only. The EPAM/ACT-R contrast remains in `Session.lean`.

