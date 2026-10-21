# Multi-digit addition: predictions deduced from EPAM and DOA

Jeff Shrager, 2026-10-21

## Introduction

Combining EPAM's recognition with the distributions-of-associations (DOA) model of retrieval yields predictions about 3-digit addition that neither theory makes alone. The best of them: a child can be **confidently wrong**, retrieving a wrong answer quickly and without falling back on a backup strategy. In DOA alone, errors and backup use always come together.

None of the predictions comes from simulation or fitting. There is no table of associations for a million problems. Every postulate is a parameter:

- the encoding of problems;
- the discrimination net;
- the associative strengths;
- the confidence criterion and search length;
- the backup procedure.

Each prediction is a theorem that holds for every choice of these. Each is proved by composing results already proved for EPAM's discrimination nets and for DOA retrieval. Only one new general lemma was needed (Lemma A below). All proofs are checked in Lean (`MultiDigit/`).

## The model

Children don't add everything column by column. A familiar problem such as 100 + 100 is recognized, and its answer is simply known. The model nests DOA's own architecture one level up.

1. **Problem code (M1).** A problem a + b is coded as features, with some features for each digit of each addend. Agreeing on all of a digit's features means having the same digit.
2. **Recognition (M2).** An EPAM discrimination net stores the codes of familiar problems. A problem's code is sorted down the net to a stored code, or to nothing.
3. **Whole-problem retrieval (M3).** If the problem is recognized as the stored problem q, DOA retrieval runs on q's associations. Each search draws an answer in proportion to strength, and states it if its strength exceeds the criterion c, for up to n searches.
4. **Column backup (M4).** If the problem is not recognized, or retrieval is exhausted, the answer is computed column by column. Here that procedure is left as an arbitrary distribution of answers.

Write R_q for the chance that one search of q's associations clears the criterion. Call q's associations **sharp** if no answer but q's sum clears the criterion.

## Two results used throughout

The predictions rest on results proved earlier.

- **From EPAM:** recognition depends only on the features the net examines along the path, and learning one item never disturbs the recognition of another.
- **From DOA** (see `StrategyChoice/docs/THEOREMS.md`): retrieval is exhausted with probability (1 − R)ⁿ (Theorem 1), and it states an answer with property P with probability Q_P · Gₙ (Theorem 2).

One new lemma about nets was needed.

**Lemma A (a confusion is with a code that looks the same).** Suppose each image is stored once in the net, the net recognizes y as itself, and it recognizes x as y. Then x and y agree on every feature examined along x's path.

*Proof.* By induction on the net. At a leaf the path is empty. At a test of feature f, suppose x and y go down different branches. Then y would be stored in both branches: x's branch returns y, and so contains it, and so does y's own branch. That contradicts each image being stored once. So they go down the same branch, which means they agree on f, and the induction hypothesis covers the rest of the path. ∎

## Predictions

**Prediction 1 (strategy nesting).** The column backup is used with probability 1 if the problem is not recognized, and with probability (1 − R_q)ⁿ if it is recognized as q.

*Proof.* If nothing is recognized, the trial is the backup, of mass 1. If it is recognized as q, retrieval runs on q's associations. A stated answer ends the trial by the whole-problem route, and exhaustion leads to the backup, which is certain to be a column outcome. Lemma 2 of the DOA document, with Theorem 1, gives (1 − R_q)ⁿ · 1. ∎

**Prediction 2 (whole-problem retrieval depends only on the route).** If x is recognized as q, then for every property P, whole-problem retrieval gives x an answer with P exactly as often as retrieval on q's associations does. So two problems recognized as the same stored problem are answered alike by whole-problem retrieval.

*Proof.* Stated answers end the trial with whole-problem outcomes, and exhaustion leads only to column outcomes, which have probability 0 for the event. Lemma 2 then gives the probability that retrieval on q's associations states an answer with P. ∎

**Prediction 3 (a confused problem gets its neighbour's answer).** If x is recognized as q, and q's associations are sharp, then every answer whole-problem retrieval gives x is q's sum.

*Proof.* By Prediction 2 and Theorem 2, the probability of stating an answer other than q's sum is Q · Gₙ. Here Q is the chance that a search clears the criterion with an answer other than q's sum. Since q is sharp, that event is impossible, so Q = 0. ∎

**Prediction 4 (confident errors).** Let q be recognized as itself, with sharp associations, and let x, with a different sum, be recognized as q. Then:

1. on q, whole-problem retrieval never errs;
2. on x, every whole-problem retrieval is an error;
3. x falls back on the columns exactly as rarely as q does, with probability (1 − R_q)ⁿ.

*Proof.* Part 1 is Prediction 3 for q itself. For part 2, an answer clears the criterion only if it is q's sum, which is not x's sum. So "clears the criterion with a wrong answer for x" and "clears the criterion" are the same event, and by Prediction 2 the error and retrieval probabilities are equal. Part 3 is Prediction 1 for both problems, since both are routed to q. ∎

*Why it matters.* In DOA, a problem's retrieval errors and its backup use come from the same distribution, a flat one, so they rise and fall together (`StrategyChoice/docs/THEOREMS.md`, Theorems 6 and 7). Confusion gives x another problem's distribution: q's low backup use, with all its retrieval trials wrong. So multi-digit performance should contain errors that are fast, retrieved, and not accompanied by any extra backup use. Single-digit DOA performance contains none.

**Prediction 5 (confusion with the same sum is harmless).** If x is recognized as q, q is recognized as itself, and the two have the same sum, then whole-problem retrieval errs on x exactly as often as on q. In particular, confusing a + b with b + a costs nothing.

*Proof.* By Prediction 2, both error probabilities are those of retrieval on q's associations stating an answer other than the common sum. For the commuted problem, the sums agree by commutativity. ∎

**Prediction 6 (near misses).** Suppose each image is stored once, x is recognized as q (which is recognized as itself), and all addends are below 1000.

- If x's path examines all the hundreds-digit features of both addends, then x's answer by confusion, q's sum, is within 200 of x's sum.
- If the path examines the tens-digit features too, the answer is within 20.

*Proof.* By Lemma A, x agrees with q on every feature its path examines. That includes all of the hundreds digits' features, so by M1 the two problems have the same hundreds digits in both addends. Then each addend of x differs from q's by less than 100, so the sums differ by less than 200. With the tens digits too, each addend differs by less than 10, and the sums by less than 20. ∎

*What it says.* How far off a confusion is depends on which digits the net has had to examine. That in turn depends on what the familiar problems differ in, as EPAM learning grows a test only at a point of confusion. If all familiar problems shared their hundreds digits, the net would never examine them, and confusions could be off by hundreds.

**Prediction 7 (practiced problems stay practiced).** If the net recognizes q, learning any other problem leaves q's whole trial, with every probability in it, unchanged.

*Proof.* EPAM's discrimination learning preserves the recognition of every other stored code (`learn_preserves`). A trial depends on the net only through what the problem's code is recognized as. ∎

**Prediction 8 (similar problems take longer to recognize).** Problems whose codes agree on the first k features of the noticing order cost at least k scanning steps to tell apart.

*Proof.* This is EPAM's `scanCost_ge_of_agree`, applied to problem codes. ∎

## What can be tested

| Prediction | Dissociation | Test |
|---|---|---|
| 4 | errors without backup use | Look for fast, retrieved errors on unfamiliar problems that resemble a familiar one. They should not be accompanied by more finger use or written column work than on the familiar problem. |
| 3, 6 | which errors | Errors on such problems should be the familiar problem's answer, off in the digits the familiar set never varies on. |
| 5 | harmless confusions | Confusions between commuted problems (and others with the same sum) should produce no errors. |
| 7 | no interference | Learning new familiar problems should not change performance on already-familiar ones. |
| 8 | time | Problems sharing their leading digits with a familiar problem should be slower to recognize, when the order scans leading digits first. |

## What the predictions rest on

- Each familiar problem is stored once in the net. That is how EPAM builds nets, but the property is not yet proved for `learn`; it is a hypothesis of Lemma A and Prediction 6.
- The criterion and search length do not depend on the route. Prediction 4 needs this.
- The backup is any distribution of answers. Predictions about the columns themselves need it built from single-digit DOA trials with carries, which is the next stage.
- Associations belong to stored problems. An unfamiliar problem has none of its own, so it can only borrow those of what it is recognized as.

## Lean

`cd MultiDigit && lake build`. There is no `sorry`, and only the standard axioms are used.

| Here | Lean name | File |
|---|---|---|
| Lemma A | `Cog.Net.confusion_agrees_on_path`, `select_mem_images` | `CogLib/CogLib/Memory/DiscriminationNet.lean` |
| Prediction 1 | `MD.columns_prob` | `MultiDigit/MultiDigit/Phenomena.lean` |
| Prediction 2 | `MD.whole_depends_only_on_route`, `same_route_same_retrieval` | same |
| Prediction 3 | `MD.confusion_gives_neighbours_answer` | same |
| Prediction 4 | `MD.confident_errors`, `wrong_eq_whole_of_sharp` | same |
| Prediction 5 | `MD.same_sum_confusion_harmless`, `commuted_confusion_harmless` | same |
| Prediction 6 | `MD.near_miss_200`, `near_miss_20`, `confused_digit` | same |
| Prediction 7 | `MD.learning_preserves_trial` | same |
| Prediction 8 | `MD.similar_problems_cost_time` | same |
| A worked case | `MD.Example.*` | `MultiDigit/MultiDigit/Example.lean` |

The worked case is a check that the theorems apply, not evidence. A net learns 100 + 100 and 100 + 200. It then examines only the second addend's hundreds digit, and recognizes the unfamiliar 150 + 100 as 100 + 100. Whole-problem retrieval answers 200, and never 250. With search length 1, the problem is answered 200 with probability 45/46, and correctly by the columns with probability 1/46.
