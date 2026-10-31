# Multi-digit addition in CogLean

The third instance in CogLean (`../README.md`) combines the first two. It requires CogLib and `../StrategyChoice/`. EPAM's discrimination-net recognition is joined to the distributions-of-associations model's retrieval (`../StrategyChoice/`), to cover 3-digit addition. A familiar problem is recognized and its answer retrieved. Otherwise, or if retrieval fails, the answer is computed column by column. When the net hasn't learned to tell two problems apart, it confuses them, and retrieval runs on the wrong problem's associations.

The predictions are **deduced**, not simulated. Every postulate is a parameter: the encoding, the net, the strengths, the criterion, the search length and the backup. Every prediction holds for all of them, and is proved by composing EPAM and DOA results already in CogLib.

```sh
cd MultiDigit && lake build    # builds CogLib too; core Lean only
```

- `MultiDigit/Postulates.lean`: the postulates M1–M4 and the trial. `trialWith` is the trial with any memory in place of the net (M2 left open: `retrieve` says what a code calls up, with probabilities). The EPAM trial is `trialWith` with the net's retrieval (`trial_eq_trialWith`).
- `MultiDigit/AnyMemory.lean`: the predictions for any memory, each with the law of memory it needs, if any. The trial is an instance of CogLib's general composition `Cog.recognizeRetrieve` (recognize, then retrieve, else back up), and the predictions that don't mention digits are proved there, for any problems and answers, and carried here by `prob_trialWith`:
  - none: column use and whole-problem answers are retrieval-weighted mixtures (`columns_prob`, `whole_prob`); confident errors, neighbour's answer and harmless confusions, for a code that calls up a stored problem for certain;
  - `AgreesOn` (what a code calls up agrees with it on the digit's features): near misses;
  - `StableRetrieval` (studying one problem leaves another's retrieval unchanged): practiced problems stay practiced.

  A memory that lacks a law, such as ACT-R's declarative memory with noise, partial matching and decay, need not have the prediction. These are the predictions that can tell memory theories apart.
- `MultiDigit/Phenomena.lean`: the predictions with EPAM's net, each derived from `AnyMemory.lean` (the net supplies `AgreesOn` by `net_agreesOn` and `StableRetrieval` by `netRetriever_stableRetrieval`), among them:
  - confident errors, which confusion produces and DOA alone cannot: a retrieved, wrong answer with no extra backup use;
  - a confused problem gets its neighbour's answer;
  - same-sum and commuted confusions are harmless;
  - near misses within 200 or 20, set by which digits the net examines;
  - no interference with practiced problems.
- `MultiDigit/Columns.lean`: the column backup, built from single-digit facts with carries, which can be DOA trials. Carrying adds no error, and a column error is a single-digit error moved to its place.
- `MultiDigit/Solver.lean`: **the column backup as problem solving** (CogLib `Process/ProblemSolving`).
  - **The problem space:** states are partly worked problems. The operators are:
    - add a column, with its single-digit fact from any process, e.g. a DOA trial;
    - write the sum;
    - write the units digit and carry;
    - finish;
    - repairs: skip, quit, write the units digit only, write both digits.
  - **`bridge`:** the full procedure answers exactly as `columns`, for every problem and every single-digit process. The solver *is* the backup, and every theorem above holds for it.
  - **Without the carry rule** (repair theory, Brown & VanLehn 1980):
    - a column summing to 10 or more is an impasse;
    - `noCarry_exact`: problems needing no carry are still exact;
    - `noCarry_bug`: with critics against blanks, quitting and two-digit cells, every problem is answered by adding columns without carrying;
    - `bugs_15_17`: with all four repairs, 15 + 17 gives 20, 0, 22 or 212, each with probability 1/4, one bug per repair.
  - **Means-ends analysis (GPS)** (`MultiDigit/SolverGPS.lean`), for every problem:
    - **`gps_every_problem`, `gps_exact`:** GPS works units first and answers exactly. Its goal is only to be finished; the order comes from subgoaling on preconditions.
    - **`gps_noCarry`:** without the carry operator, GPS gives up, with no answer, on exactly the problems that need a carry, and is exact on the rest.
    - **`regimes_diverge`:** the same knowledge deficit under two control regimes. The decision cycle with repair gives the confident no-carry bug; GPS gives no answer. Both are exact when no carry is needed.
- `MultiDigit/Learning.lean`: discrimination after a confusion removes it, and only it, and the problem is then worked out by the columns until its own associations are strengthened. The near-miss predictions hold for every net EPAM learns.
- `MultiDigit/Features.lean`, `MultiDigit/FeaturePhenomena.lean`: further features a code may carry (zeros, magnitude as thresholds, column facts), and what confusions then keep: no confusion with a round problem once its zeros are tested; confused digits between the same tested thresholds; harmless confusions, or errors in multiples of 100, once column facts are tested.
- `MultiDigit/Example.lean`, `MultiDigit/Example2.lean`: worked cases, a check that the theorems apply.
- `MultiDigit/Integrated.lean`: **the integrated model**, with no answer given. EPAM recognition, DOA whole-problem retrieval, and on failure the column solver (CogLib's decision cycle), with each column a single-digit DOA trial. The general results (the solver is the column backup, confident errors survive it, two sources of error) are separated from the conditional ones and from the illustrative setting. In that setting, 150 + 100 is answered 200 with probability about .978, and 250 only by the solver.
- `MultiDigit/ExampleACTR.lean`: the first worked case with ACT-R's declarative memory (`Cog.actRetriever`) in place of the net. Confusion is graded; no problem, not even a practiced one, is retrieved for certain; `AgreesOn` fails; and studying a new problem raises the errors on a practiced one. See the table in `../notes/MultiDigit_PREDICTIONS.md`.
- [`sim/`](sim/README.md): a blind Python simulation of the model, written from a prose spec alone, and checked against preregistered predictions and Lean's exact distributions (`Export.lean`).
- [`../notes/MultiDigit_PREDICTIONS.md`](../notes/MultiDigit_PREDICTIONS.md): every prediction with its full proof, the test it suggests and what it rests on.

Next: ACT-R with general decay and temperature, and a check against PyACTUp (`../notes/OPEN_ISSUES.md` #16); a learning sequence over many trials (discrimination and strengthening together); errors in carrying.
