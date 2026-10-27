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

Each prediction is a theorem that holds for every choice of these. Each is proved by composing results already proved for EPAM's discrimination nets and for DOA retrieval. Only two new general lemmas were needed (Lemmas A and B below). All proofs are checked in Lean (`MultiDigit/`).

## The model

Children don't add everything column by column. A familiar problem such as 100 + 100 is recognized, and its answer is simply known. The model nests DOA's own architecture one level up.

1. **Problem code (M1).** A problem a + b is coded as features, with some features for each digit of each addend. Agreeing on all of a digit's features means having the same digit.
   A code may carry more (M1a–M1c, below): whether each digit is 0, each digit's size as nine thresholds, and each column's single-digit fact.
2. **Recognition (M2).** An EPAM discrimination net stores the codes of familiar problems. A problem's code is sorted down the net to a stored code, or to nothing.
3. **Whole-problem retrieval (M3).** If the problem is recognized as the stored problem q, DOA retrieval runs on q's associations. Each search draws an answer in proportion to strength, and states it if its strength exceeds the criterion c, for up to n searches.
4. **Column backup (M4).** If the problem is not recognized, or retrieval is exhausted, the answer is computed column by column: units, tens, then hundreds. Each column's digits are added by a single-digit process, which can be the DOA trial itself, and the tens of each column's result are carried. Predictions 1–8 hold for any backup; Predictions 9–10 are about this one.
5. **Learning (M5).** EPAM's discrimination learning grows the net when a problem is confused. DOA's postulate A6 strengthens every stated answer, correct answers twice as much.

Write R_q for the chance that one search of q's associations clears the criterion. Call q's associations **sharp** if no answer but q's sum clears the criterion.

## Two results used throughout

The predictions rest on results proved earlier.

- **From EPAM:** recognition depends only on the features the net examines along the path, and learning one item never disturbs the recognition of another.
- **From DOA** (see `StrategyChoice/docs/THEOREMS.md`): retrieval is exhausted with probability (1 − R)ⁿ (Theorem 1), and it states an answer with property P with probability Q_P · Gₙ (Theorem 2).

Two new lemmas about nets were needed.

**Lemma A (a confusion is with a code that looks the same).** Suppose each image is stored once in the net, the net recognizes y as itself, and it recognizes x as y. Then x and y agree on every feature examined along x's path.

*Proof.* By induction on the net. At a leaf the path is empty. At a test of feature f, suppose x and y go down different branches. Then y would be stored in both branches: x's branch returns y, and so contains it, and so does y's own branch. That contradicts each image being stored once. So they go down the same branch, which means they agree on f, and the induction hypothesis covers the rest of the path. ∎

**Lemma B (EPAM's nets satisfy Lemma A's hypothesis).** Call a net *clean* if each image is stored once and every stored image is recognized as itself. The empty net is clean, and learning keeps a net clean. So every net EPAM learns from an empty one is clean.

*Proof.* By induction on the net, following the definition of learning.

- An empty terminal receives the new image, and is clean.
- A terminal holding the same image is unchanged.
- A terminal holding a different image becomes a test on their first noticed difference, with each image on its own side. Both are recognized, and they are distinct. If no difference can be noticed, the terminal is unchanged.
- At a test, learning changes only the branch the new code takes. In a clean net, every image below a branch takes that branch. The images of the changed branch are its old images plus perhaps the new code, all of which take that branch. So they cannot also appear in the other branch, and each is recognized through its own branch. ∎

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

**Prediction 6 (near misses).** Suppose each image is stored once, x is recognized as q (which is recognized as itself), and all addends are below 1000. By Lemma B, the first two conditions hold automatically for any net EPAM has learned, so only "x is recognized as q" needs to be assumed.

- If x's path examines all the hundreds-digit features of both addends, then x's answer by confusion, q's sum, is within 200 of x's sum.
- If the path examines the tens-digit features too, the answer is within 20.

*Proof.* By Lemma A, x agrees with q on every feature its path examines. That includes all of the hundreds digits' features, so by M1 the two problems have the same hundreds digits in both addends. Then each addend of x differs from q's by less than 100, so the sums differ by less than 200. With the tens digits too, each addend differs by less than 10, and the sums by less than 20. ∎

*What it says.* How far off a confusion is depends on which digits the net has had to examine. That in turn depends on what the familiar problems differ in, as EPAM learning grows a test only at a point of confusion. If all familiar problems shared their hundreds digits, the net would never examine them, and confusions could be off by hundreds.

**Prediction 7 (practiced problems stay practiced).** If the net recognizes q, learning any other problem leaves q's whole trial, with every probability in it, unchanged.

*Proof.* EPAM's discrimination learning preserves the recognition of every other stored code (`learn_preserves`). A trial depends on the net only through what the problem's code is recognized as. ∎

**Prediction 8 (similar problems take longer to recognize).** Problems whose codes agree on the first k features of the noticing order cost at least k scanning steps to tell apart.

*Proof.* This is EPAM's `scanCost_ge_of_agree`, applied to problem codes. ∎

**Prediction 9 (carrying adds no error).** With correct carrying, the column backup's answer is exactly r₀ + 10 r₁ + 100 r₂, where r₀, r₁, r₂ are the single-digit results for the units, tens and hundreds columns. So if every column is added correctly, the problem is answered correctly.

*Proof.* Write s₀ = r₀ and s₁ = r₁ + ⌊s₀/10⌋. The algorithm writes s₀ mod 10, then s₁ mod 10, then r₂ + ⌊s₁/10⌋ in the hundreds. Its value is 100(r₂ + ⌊s₁/10⌋) + 10(s₁ mod 10) + (s₀ mod 10). Since 10⌊s₁/10⌋ + (s₁ mod 10) = s₁, this equals 100 r₂ + 10 s₁ + (s₀ mod 10). Substituting s₁ and using 10⌊s₀/10⌋ + (s₀ mod 10) = s₀ gives 100 r₂ + 10 r₁ + r₀. With correct columns, rᵢ is the sum of the column's digits, and the place-value sum is a + b. ∎

**Prediction 10 (a column error is a single-digit error, moved to its place).** If two columns are certain to be added correctly, the problem is wrong exactly when the third column is, and an error of δ in the column at place 10ʲ makes the answer off by exactly δ · 10ʲ. When DOA adds the columns, the problem's error rate is that single-digit DOA trial's error rate, whatever strategy the trial uses.

*Proof.* By Prediction 9, the answer is the correct sum plus 10ʲ times the column's error, and that is the correct sum exactly when the error is 0. With DOA as the single-digit process, the column's answer is the DOA trial's answer, so its error rate is the trial's. ∎

*What it says.* Column-route errors are copies of single-digit errors, scaled by place. A child whose 2 + 3 sometimes gives 4 (the counting-string error) will sometimes get 120 + 130 = 240: off by exactly 10.

**Prediction 11 (discrimination removes a confusion, and only that).** Suppose x is confused with q in a clean net, and x's code is noticeably different from every stored image. After EPAM learns x:

- x is recognized as itself, and whole-problem retrieval on it uses its own associations;
- q's trial is exactly what it was;
- the net is still clean.

*Proof.* EPAM learning makes x recognized (`learn_recognizes`). Prediction 2 then puts whole-problem retrieval on x's own associations. By Lemma B, q is recognized as itself in the clean net, so Prediction 7 leaves its trial unchanged. Lemma B keeps the net clean. ∎

**Prediction 12 (after discrimination, the columns).** A problem recognized as itself, none of whose own associations yet clears the criterion, is worked out by the columns on every trial.

*Proof.* No answer clears the criterion, so R = 0, and by Prediction 1 the columns are used with probability (1 − 0)ⁿ = 1. ∎

*What it says.* Together with Predictions 4 and 11, this gives a sequence that can be looked for. First comes a fast, confident error from confusion. Once the error is noticed and the problem discriminated, slow column work follows, because a newly discriminated problem has only weak associations of its own. Then, as correct answers are stated and strengthened, fluent and correct retrieval follows. By DOA's A6, strengthening a correct answer never raises retrieval errors, whichever strategy produced it (`SC.correct_strengthening_lowers_errors`).

## Further features (M1a–M1c)

The net can test only the features a problem's code carries. Three further kinds are stated as laws that an encoding may satisfy:

- **Zeros (M1a).** For each digit, a feature that says whether it is 0.
- **Magnitude (M1b).** For each digit d, nine thresholds: the k-th (k < 9) says whether d > k. Close digits share most of these features.
- **Column facts (M1c).** For each column, features that identify its single-digit fact, and so determine the column's sum. The fact is unordered: 3 + 4 and 4 + 3 are the same fact.

One general lemma covers all three.

**Lemma C (a confusion keeps what its path determines).** Say features F *determine* a property P of problems when two problems whose codes agree on F agree on P. If each image is stored once, x is recognized as q (which is recognized as itself), and every feature in F is on x's path, then x and q agree on P.

*Proof.* By Lemma A, x and q agree on every feature on x's path, so on F. ∎

Lemma A with M1 gave Prediction 6, since a digit's features determine the digit. Predictions 13–18 come from Lemma C in the same way. Each also holds for every net EPAM learns, with no hypothesis on the net (Lemma B).

**Prediction 13 (confusions keep zeros).** If x's path tests whether a digit is 0, x has a 0 there exactly when q does.

**Prediction 14 (confusion with a round problem is exact).** Let q be round: 0 in the tens and units of both addends, such as 100 + 200. If x's path tests the zeros of the tens and units and the hundreds digits, a problem confused with q is q. So the confusion is harmless.

*Proof.* By Prediction 13, x has the same zeros in the tens and units, so it is round too. By Prediction 6, it has q's hundreds digits. A 3-digit problem is fixed by its digits. ∎

*What it says.* Under binary-coded digits, 150 + 100 was confused with 100 + 100. Once the net has had to test the tens' zero flag, it can't be: it goes to some non-round problem instead.

**Prediction 15 (errors within the gap).** If x's path tests the threshold k of a digit, x's digit is on the same side of k as q's. If it tests thresholds lo and hi, and q's digit is above lo and at most hi, so is x's, and the two differ by less than hi − lo.

**Prediction 16 (close digits share features).** Two digits d and e differ on exactly |d − e| of the nine thresholds.

*What it says.* With Prediction 8, problems whose digits are close agree on more features, so they are harder to tell apart, and are the ones confused. Under thresholds, confusions are with numerical neighbours. Under binary-coded digits they are not: 7 = 0111 and 8 = 1000 differ in every bit.

**Prediction 17 (tested column facts make confusions harmless).** If x's path tests all three column facts, x and q have the same column sums, so the same sum, and whole-problem retrieval errs on x exactly as often as on q.

*Proof.* Lemma C gives equal column sums. The sum is units + 10 · tens + 100 · hundreds column sums (as in Prediction 9). Prediction 5 does the rest. ∎

**Prediction 18 (tested low columns fix the low digits).** If x's path tests the tens' and units' facts, the error of a confusion is a multiple of 100. With only the units' fact, it is a multiple of 10.

*Proof.* A sum mod 100 depends only on 10 · tens + units column sums, and mod 10 only on the units column sum. ∎

*What it says.* Column facts tie whole-problem recognition to the single-digit facts. A net that has learned to tell problems apart by their column facts makes confusions only between problems that the column backup would answer the same way, in the columns it tests.

## What can be tested

| Prediction | Dissociation | Test |
|---|---|---|
| 4 | errors without backup use | Look for fast, retrieved errors on unfamiliar problems that resemble a familiar one. They should not be accompanied by more finger use or written column work than on the familiar problem. |
| 3, 6 | which errors | Errors on such problems should be the familiar problem's answer, off in the digits the familiar set never varies on. |
| 5 | harmless confusions | Confusions between commuted problems (and others with the same sum) should produce no errors. |
| 7 | no interference | Learning new familiar problems should not change performance on already-familiar ones. |
| 10 | column errors | Column-route errors should be single-digit errors moved to their place: off by exactly 10 × (a single-digit error) when the tens column errs. |
| 4, 11, 12 | a learning sequence | On a problem first answered confidently and wrongly, look for fast errors, then slow column work after feedback, then fluent correct retrieval. |
| 13, 14 | zeros | Unfamiliar problems should not be confused with round ones once the familiar set has forced the net to test zeros. |
| 15, 16 | which neighbours | Under a magnitude code, confusions should be with problems whose digits are numerically close. |
| 17, 18 | column facts | Confusions between problems with the same column facts (e.g. 120 + 340 and 140 + 320) should cost nothing. With the low columns tested, errors should be multiples of 100. |
| 8 | time | Problems sharing their leading digits with a familiar problem should be slower to recognize, when the order scans leading digits first. |

## Which predictions need EPAM

M2 can be any memory: `trialWith` takes a `retrieve`, which says what a code calls up, with probabilities (`MultiDigit/MultiDigit/AnyMemory.lean`). Each prediction is proved there with the law of memory it needs, and the EPAM version follows by supplying the law from the net.

| Prediction | Law of memory | EPAM | ACT-R declarative memory (`Cog.actRetriever`) |
|---|---|---|---|
| 1, and whole-problem answers | none: retrieval-weighted mixtures (`AnyMemory.columns_prob`, `whole_prob`) | holds | holds (`ExampleACTR.act_columns`) |
| 2–5 | a code retrieves a stored problem for certain | holds: retrieval is deterministic | never applies: nothing is retrieved for certain (`Act.retrieve_not_certain`). Confusion is graded (`act_values`), and a practiced problem errs (`act_practiced_not_certain`) |
| 6 (near misses), 13–18 | `AgreesOn`: what a code retrieves agrees with it on the digit's (or fact's) features | holds: `net_agreesOn` (Lemma A) | fails: partial matching retrieves problems differing on any feature (`act_not_agreesOn`) |
| 7 (practiced problems stay practiced) | `StableRetrieval` | holds: `netRetriever_stableRetrieval` (learning is local) | the law holds only vacuously (`actRetriever_stableRetrieval`), and the prediction fails: studying 100 + 300 raises the errors on 100 + 100 (`act_interference`) |

The predictions in the last three rows are the ones that tell the memory theories apart. The ACT-R entries are for decay 1 and temperature 1, where its retrieval probabilities are rational. The failures are shown on the worked case in `MultiDigit/MultiDigit/ExampleACTR.lean`, the same problems as `Example.lean`:

| | EPAM | ACT-R |
|---|---|---|
| 150 + 100 answered 200 (the neighbour's sum) | 45/46 | 225/529 |
| 150 + 100 answered 300 | 0 | 225/1058 |
| 150 + 100 answered correctly | 1/46 | 383/1058 |
| errors on the practiced 100 + 100 | 0 | 225/782 |
| the same, after also studying 100 + 300 | 0 | 3375/5842 |

## What the predictions rest on

- The criterion and search length do not depend on the route. Prediction 4 needs this.
- Predictions 1–8 hold for any backup. Predictions 9–10 assume error-free carrying, and columns added independently of one another.
- Predictions 11 and 12 assume the confused problem is noticeably different from every stored image, so that EPAM can learn it.
- Associations belong to stored problems. An unfamiliar problem has none of its own, so it can only borrow those of what it is recognized as.

## Lean

`cd MultiDigit && lake build`. There is no `sorry`, and only the standard axioms are used.

| Here | Lean name | File |
|---|---|---|
| Lemma A | `Cog.Net.confusion_agrees_on_path`, `select_mem_images` | `CogLib/CogLib/Memory/DiscriminationNet.lean` |
| Lemma B | `Cog.Net.Clean`, `learn_clean`, `learnAll_clean`, `clean_empty` | `CogLib/CogLib/Process/DiscriminationLearning.lean` |
| Prediction 1 | `MD.columns_prob` | `MultiDigit/MultiDigit/Phenomena.lean` |
| Prediction 2 | `MD.whole_depends_only_on_route`, `same_route_same_retrieval` | same |
| Prediction 3 | `MD.confusion_gives_neighbours_answer` | same |
| Prediction 4 | `MD.confident_errors`, `wrong_eq_whole_of_sharp` | same |
| Prediction 5 | `MD.same_sum_confusion_harmless`, `commuted_confusion_harmless` | same |
| Prediction 6 | `MD.near_miss_200`, `near_miss_20`, `confused_digit`; for learned nets `near_miss_200_learned`, `near_miss_20_learned` | same; `MultiDigit/MultiDigit/Learning.lean` |
| Prediction 7 | `MD.learning_preserves_trial` | same |
| Prediction 8 | `MD.similar_problems_cost_time` | same |
| Prediction 9 | `MD.columns_place_value`, `columns_exact` | `MultiDigit/MultiDigit/Columns.lean` |
| Prediction 10 | `MD.one_column_errs`, `doaFact_wrong`, `column_error_is_doa_error` | same |
| Prediction 11 | `MD.discrimination_removes_confusion` | `MultiDigit/MultiDigit/Learning.lean` |
| Prediction 12 | `MD.discrimination_then_columns` | same |
| Laws of memory | `Cog.Retriever`, `Phenomena.StableRetrieval`, `Phenomena.AgreesOn`, `Phenomena.confusion_preserves_of`; EPAM: `Net.retrieve`, `netRetriever_stableRetrieval`, `net_agreesOn` | `CogLib/CogLib/Phenomena/Retriever.lean`, `Process/DiscriminationLearning.lean` |
| Any memory | `MD.trialWith`, `MD.trial_eq_trialWith`; `MD.AnyMemory.*` | `MultiDigit/MultiDigit/Postulates.lean`, `AnyMemory.lean` |
| Lemma C | `Cog.Determines`, `Cog.Net.confusion_preserves` | `CogLib/CogLib/Rep/Features.lean`, `Memory/DiscriminationNet.lean` |
| M1a–M1c | `MD.Zeros`, `MD.Magnitude`, `MD.ColumnFacts` | `MultiDigit/MultiDigit/Features.lean` |
| Prediction 13 | `MD.confusion_keeps_zeros` | `MultiDigit/MultiDigit/FeaturePhenomena.lean` |
| Prediction 14 | `MD.round_confusion_exact`, `round_confusion_harmless`, `round_confusion_exact_learned` | same |
| Prediction 15 | `MD.confusion_same_side`, `confusion_within_gap` | same |
| Prediction 16 | `MD.threshold_diffs`, `Magnitude.diffs` | `MultiDigit/MultiDigit/Features.lean` |
| Prediction 17 | `MD.facts_same_sum`, `facts_tested_harmless`, `facts_same_sum_learned` | `MultiDigit/MultiDigit/FeaturePhenomena.lean` |
| Prediction 18 | `MD.facts_mod_100`, `facts_mod_10` | same |
| DOA A6 | `SC.strengthen`, `SC.correct_strengthening_lowers_errors` | `StrategyChoice/StrategyChoice/` |
| A worked case | `MD.Example.*` | `MultiDigit/MultiDigit/Example.lean` |
| A worked case, further features | `MD.Example2.*` | `MultiDigit/MultiDigit/Example2.lean` |
| The worked case with ACT-R's memory | `Cog.actRetriever`, `Act.retrieve_not_certain`; `MD.ExampleACTR.*` | `CogLib/CogLib/Memory/Activation.lean`, `MultiDigit/MultiDigit/ExampleACTR.lean` |

The worked case is a check that the theorems apply, not evidence. A net learns 100 + 100 and 100 + 200. It then examines only the second addend's hundreds digit, and recognizes the unfamiliar 150 + 100 as 100 + 100. Whole-problem retrieval answers 200, and never 250. With search length 1, the problem is answered 200 with probability 45/46, and correctly by the columns with probability 1/46. A second check runs the column algorithm, with carries, on 234 + 578 = 812.

The second worked case uses an encoding with zero flags, thresholds and column facts (360 features), and satisfies all three laws. A net learned from 100 + 100 and 120 + 100 tests the first addend's tens zero flag, and takes 150 + 100 for 120 + 100, not for 100 + 100. A net learned from 700 + 100 and 800 + 100 takes 600 + 100 for its neighbour 700 + 100 (off by 100); the binary-coded net learned from the same problems takes it for 800 + 100 (off by 200).
	