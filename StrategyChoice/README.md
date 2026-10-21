# Strategy choice in CogLean

The distributions-of-associations model of strategy choice (Siegler & Shrager 1984) is the second theory in CogLean (`../README.md`). Children solving simple addition problems use several strategies: retrieving an answer, putting up their fingers, counting their fingers. On each problem, how often they use overt strategies, how often they err, and how long they take are closely related. The model explains all three by one variable, the **distribution of associations** between each problem and its possible answers. No separate judgment of the problem's difficulty is needed.

Siegler, R. S., & Shrager, J. (1984). Strategy choices in addition and subtraction: How do children know what to do? In C. Sophian (Ed.), *Origins of cognitive skills* (pp. 229-293). Hillsdale, NJ: Erlbaum.

```sh
cd StrategyChoice
lake build        # builds CogLib too; core Lean only
python3 analysis/closed_form.py
```

## Postulates

`StrategyChoice/Postulates.lean` quotes each postulate and names the CogLib construct that realizes it.

| Postulate (chapter page) | CogLib / this package |
|---|---|
| A1 Associations of varying strength between a problem and its possible answers (p. 238) | strengths `Answer → Rat` |
| A2 A confidence criterion and a search length, set on each trial (p. 239) | the `cc` and `n` of `Cog.search` |
| A3 Retrieval in proportion to strength; an answer is stated if its strength exceeds the criterion; up to the search length (p. 240) | `Cog.sample`, `Cog.above`, `Cog.search` (`Process/SampledRetrieval`) |
| A4 Elaboration: fingers add strength to the answer equal to the number of objects, renormalized (p. 242, fn. 4) | `SC.elaborate` |
| A5 Counting, with chances of skipping and of double-counting an object (p. 273) | `SC.count` |
| A6 Learning: stated answers are strengthened, correct ones twice as much (p. 273) | not yet stated |

A trial (`SC.trial`, Fig. 9.2B) is retrieval, then if nothing is stated the backup strategies (`SC.backup`): fingers, then counting fingers. Its result is a distribution over (strategy, answer).

## What is proved

General results about sampled retrieval are proved once in CogLib (`Process/SampledRetrieval`), for any answers, strengths, criterion and search length. With `R` the chance that one search finds an answer above the criterion:

| Result | Theorem |
|---|---|
| Retrieval is exhausted with probability `(1-R)^n` | `Cog.prob_exhausted` |
| The share of stated answers with any property is `Q/R`, whatever the search length | `Cog.stated_share` |
| Shifting strength to one answer never raises the others' share of stated answers, at any criterion | `Cog.stated_share_shift`, `Cog.aboveShare_shift` |

The model's phenomena (`StrategyChoice/Phenomena.lean`):

| Phenomenon (chapter) | Theorem |
|---|---|
| Overt strategies with probability `(1-R)^N` (p. 250) | `retrieval_prob` |
| The error share on retrieval trials depends only on the distribution and the criterion, not the search length (p. 250) | `retrieval_error_share` |
| Retrieval (its use and its errors) is unaffected by the backup strategies | `retrieval_independent_of_backup` |
| Errors on counting trials are unaffected by the distribution of associations (p. 245, the "nonintuitive prediction") | `counting_error_share` |
| A more peaked distribution gives fewer errors (p. 245) | `peaking_lowers_retrieval_errors`, when strength moves to the correct answer |
| A more peaked distribution gives less overt strategy use (p. 245) | **not in general**: `peaking_can_raise_overt_use` |

The last is a finding. Moving .01 of strength to the correct answer, already the strongest, can raise predicted overt strategy use. In the example, (.38, .31, .31) becomes (.39, .30, .31), and the mean over the chapter's twelve criteria rises from 7/12 to 73/120 with search length 1. The cause is that a wrong answer falls to a criterion and so below it. In a Python check of random distributions, no such case appeared when the criterion was spread uniformly; there, the conjecture is monotonicity in the majorization order (`../OPEN_ISSUES.md`).

## Data and predictions

`StrategyChoice/Data.lean` holds six rows of Fig. 9.2A (p. 241): 1+1, 1+2, 1+3, 2+2, 2+3, 3+3. These are the 4-year-olds' answer distributions when overt strategies were forbidden, which the chapter uses as associative strengths. The rows are as reproduced in the ACT-R tutorial (unit 5, `siegler.lisp`). From them, over the chapter's twelve criteria and search lengths 1 to 6:

- `predicted_overt_order`: predicted overt strategy use is least on 1+1, then 2+2, 1+2, 1+3, 3+3, and most on 2+3. The two flattest distributions send the child to her fingers most often.
- `predicted_overt_values`: the exact values, equal to those `analysis/closed_form.py` computes.
- `retrieval_never_errs_2_2`: on 2+2, retrieval never states a wrong answer, at any criterion.

## Not yet done

See `../OPEN_ISSUES.md`:

- learning (A6) and the learning simulation;
- the full 25-problem matrix;
- solution times;
- the comparison with ACT-R's account of the same data.
