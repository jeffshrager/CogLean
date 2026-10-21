# Strategy Choice: Theorems Without Numbers

Jeff Shrager, 2026-10-21

## Introduction

The distributions-of-associations model of strategy choice (Siegler & Shrager, 1984) entails eleven results that hold for **every** set of associative strengths, confidence criterion, search length, elaboration strength and counting-error rate. This document states each one and proves it in full. Every proof here has also been checked by the Lean 4 proof assistant, in the CogLean library.

The chapter derives its predictions by putting the strengths of Fig. 9.2A into equations (p. 250). The theorems below need no numbers. They say what follows from the *form* of the model: sampling in proportion to strength, a criterion that a retrieved answer must exceed, a limit on searches, and backup strategies that run only when retrieval fails. They are of four kinds:

- **Laws of retrieval**: how often a search of length n succeeds, and what it states.
- **Laws of the trial**: how often retrieval is used, and how its errors and the errors of counting are determined.
- **Independence**: which parts of performance do *not* depend on which parameters. This includes the chapter's "nonintuitive prediction" (p. 245).
- **Peakedness**: moving strength to the correct answer never raises the error rate on retrieval trials. The corresponding claim for overt strategy use is false in general, and the last section shows why.

The proofs use only finite sums and the algebra of fractions. No result assumes that strengths sum to 1, or that any parameter takes a particular value. Where a hypothesis is needed (for example, that strengths are not negative), the theorem states it.

Citations by page are to: Siegler, R. S., & Shrager, J. (1984). Strategy choices in addition and subtraction: How do children know what to do? In C. Sophian (Ed.), *Origins of cognitive skills* (pp. 229–293). Hillsdale, NJ: Erlbaum.

## The model

A problem p = a + b has a correct answer, its sum, written σ = a + b. The model has five postulates (Fig. 9.2B, pp. 238–243, 273).

1. **Associations (A1).** A finite list of possible answers A, and a strength s(x) ≥ 0 for each answer x. The total strength is T = Σ s(x), over x in A, and we assume T ≠ 0.
2. **Parameters (A2).** On each trial a confidence criterion c and a search length n.
3. **Retrieval (A3).** A search draws answer x with probability s(x)/T. If s(x) > c, x is stated. Otherwise search again, up to n searches in all. If none is stated, retrieval is *exhausted*.
4. **Elaboration (A4).** If retrieval is exhausted, the child puts up fingers. This adds strength e to the answer σ, and every strength is divided by 1 + e. One more search is made with these elaborated strengths s′. If the answer drawn has s′(x) > c, it is stated (the *fingers* strategy).
5. **Counting (A5).** Otherwise the child counts the fingers. Each object is skipped with probability qₛ, counted twice with probability q\_d, and counted once otherwise. The last number counted is stated (the *counting-fingers* strategy).

A **trial** is this whole process. Its outcome is a pair: the strategy used (retrieval, fingers or counting fingers) and the answer stated.

Two quantities recur. The chance that a single search **reaches** the criterion is:

```math
R = \frac{1}{T} \sum_{x \in A,\; s(x) > c} s(x)
```

For any property P of answers (such as "is wrong"), the chance that one search reaches the criterion with an answer having P is:

```math
Q_P = \frac{1}{T} \sum_{x \in A,\; s(x) > c,\; P(x)} s(x)
```

We also write Gₙ for the geometric sum 1 + (1 − R) + … + (1 − R)ⁿ⁻¹, with G₀ = 0. Equivalently, Gₙ₊₁ = 1 + (1 − R)Gₙ.

## Foundations

Every proof below is built from six lemmas about finite distributions. A **distribution** is a finite list of outcomes with probabilities (p₁, x₁), …, (pₖ, xₖ). The probability of an event E is the sum of the pᵢ whose xᵢ is in E, and its **mass** is the sum of all pᵢ. A **two-stage process** d » f draws xᵢ from d, then draws from the distribution f(xᵢ). Its outcomes are the pairs' second-stage outcomes, with probabilities pᵢ times the second-stage probabilities.

**Lemma 1 (two stages).** Pr\[d » f ∈ E\] = Σᵢ pᵢ · Pr\[f(xᵢ) ∈ E\].

*Proof.* The outcomes of d » f are the outcomes of f(x₁) with probabilities scaled by p₁, followed by those of f(x₂) scaled by p₂, and so on. The probability of E in a list joined end to end is the sum of its probabilities in the parts. Scaling every probability in a list by p scales the probability of E by p. ∎

**Lemma 2 (a two-part second stage).** Suppose that, for every first-stage outcome x, Pr\[f(x) ∈ E\] = \[x ∈ g₁\] + k·\[x ∈ g₂\], where \[·\] is 1 if the condition holds and 0 if not. Then Pr\[d » f ∈ E\] = Pr\[d ∈ g₁\] + k · Pr\[d ∈ g₂\].

*Proof.* By Lemma 1, the probability is Σᵢ pᵢ(\[xᵢ ∈ g₁\] + k\[xᵢ ∈ g₂\]) = Σᵢ pᵢ\[xᵢ ∈ g₁\] + k Σᵢ pᵢ\[xᵢ ∈ g₂\], and the two sums are Pr\[d ∈ g₁\] and Pr\[d ∈ g₂\]. ∎

Lemma 2 is the workhorse. Each step of the model either ends the trial (probability 1 or 0 for the event in question), or passes on to a later step whose probability for the event is already known (the constant k).

**Lemma 3 (complement).** Pr\[d ∈ E\] + Pr\[d ∉ E\] = mass(d).

*Proof.* Each pᵢ is counted in exactly one of the two sums. ∎

**Lemma 4 (sampling).** Let d sample answers from A in proportion to strength: answer x with probability s(x)/T. Then Pr\[d ∈ E\] = (Σ over x ∈ E of s(x))/T. In particular, if T ≠ 0 the sample has mass 1, the chance that one search reaches the criterion is R, and the chance that it does not is 1 − R.

*Proof.* Sum s(x)/T over x ∈ E, and take the common factor 1/T out. With E the whole of A this gives T/T = 1. The last claim follows from Lemma 3. ∎

The last two lemmas compare sums of strengths. Write S(s, E) for the sum of s(x) over the answers x in A that lie in E.

**Lemma 5 (splitting).** For any events E and F, S(s, E) = S(s, E ∩ F) + S(s, E ∖ F).

*Proof.* Each answer in E is in exactly one of E ∩ F and E ∖ F. ∎

**Lemma 6 (monotonicity).** Let s ≥ 0. Suppose every answer in E′ is also in E, and has s′(x) ≤ s(x). Then S(s′, E′) ≤ S(s, E).

*Proof.* Compare the two sums term by term. An answer in E′ contributes s′(x) ≤ s(x) on the left, and s(x) on the right. An answer in E but not in E′ contributes 0 on the left and s(x) ≥ 0 on the right. Any other answer contributes 0 to both. ∎

## Theorems about retrieval

The retrieval phase alone (A3) already fixes how often retrieval fails, and what share of its answers have any given property, as functions of R, Q\_P and n. Throughout, T ≠ 0.

**Theorem 1 (exhaustion).** With search length n, retrieval is exhausted with probability (1 − R)ⁿ.

*Proof.* By induction on n. With n = 0 no search is made, so retrieval is exhausted with probability 1 = (1 − R)⁰. For n + 1, consider the first draw x. If s(x) > c, x is stated, and the probability of exhaustion is 0. Otherwise a search of length n follows, which by the induction hypothesis is exhausted with probability (1 − R)ⁿ. Lemma 2, with g₁ empty, g₂ = "x does not reach the criterion" and k = (1 − R)ⁿ, gives probability (1 − R)ⁿ · Pr\[a search does not reach\]. By Lemma 4 that is (1 − R)ⁿ(1 − R) = (1 − R)ⁿ⁺¹. ∎

**Theorem 2 (stating).** With search length n, an answer with property P is stated with probability Q\_P · Gₙ.

*Proof.* By induction on n. With n = 0 nothing is stated, and Q\_P · G₀ = 0. For n + 1, consider the first draw x. If s(x) > c, x is stated, so the event holds with probability 1 if P(x) and 0 if not. Otherwise a search of length n follows, which by hypothesis states an answer with P with probability Q\_P Gₙ. Apply Lemma 2 with g₁ = "x reaches the criterion and P(x)", g₂ = "x does not reach" and k = Q\_P Gₙ. Then by Lemma 4 the probability is Q\_P + Q\_P Gₙ(1 − R) = Q\_P(1 + (1 − R)Gₙ) = Q\_P Gₙ₊₁. ∎

**Lemma 7 (stated or exhausted).** R · Gₙ = 1 − (1 − R)ⁿ. So retrieval states some answer with probability 1 − (1 − R)ⁿ, the complement of Theorem 1.

*Proof.* By induction on n. For n = 0 both sides are 0. Then R·Gₙ₊₁ = R + (1 − R)(R·Gₙ) = R + (1 − R)(1 − (1 − R)ⁿ) = 1 − (1 − R)ⁿ⁺¹. The second claim is Theorem 2 with P true of every answer, which makes Q\_P = R. ∎

**Theorem 3 (the share of stated answers does not depend on the search length).** For every n:

```math
\Pr[\text{an answer with } P \text{ is stated}] \cdot R \;=\; \Pr[\text{an answer is stated}] \cdot Q_P
```

So whenever R > 0, a fraction Q\_P / R of stated answers have P, whatever n is. That fraction equals S(s, reach ∩ P) / S(s, reach), the share of P-answers in the strength above the criterion.

*Proof.* By Theorem 2, the left side is Q\_P Gₙ R, and the right side is (R Gₙ) Q\_P. Since T cancels from the numerator and denominator of Q\_P / R, the fraction is the share of strength. ∎

The chapter's formula for the probability of an error on retrieval trials (p. 250) indeed has no N in it. Theorem 3 says why: every search is an independent draw from the same distribution, so persisting longer changes how often an answer is stated, not which.

**Lemma 8 (R is a probability).** If every s(x) ≥ 0, then 0 ≤ R ≤ 1.

*Proof.* R and 1 − R are Pr\[reach\] and Pr\[not reach\] for the sample (Lemma 4), each a sum of non-negative s(x) divided by T > 0. They are therefore non-negative, and they sum to 1 (Lemma 3). ∎

**Theorem 4 (reaching the criterion more often, retrieval is exhausted less often).** If R ≤ R′ ≤ 1, then (1 − R′)ⁿ ≤ (1 − R)ⁿ.

*Proof.* Let x = 1 − R′ and y = 1 − R, so 0 ≤ x ≤ y. We show xⁿ ≤ yⁿ by induction on n. For n = 0, 1 ≤ 1. Then xⁿ⁺¹ = xⁿ·x ≤ yⁿ·x, since x ≥ 0, and yⁿ·x ≤ yⁿ·y, since yⁿ ≥ 0. ∎

**Theorem 5 (searching longer, retrieval is exhausted less often).** If 0 ≤ R ≤ 1, then (1 − R)ⁿ⁺¹ ≤ (1 − R)ⁿ.

*Proof.* (1 − R)ⁿ⁺¹ = (1 − R)ⁿ(1 − R) ≤ (1 − R)ⁿ · 1, since (1 − R)ⁿ ≥ 0 and 1 − R ≤ 1. ∎

## Theorems about the whole trial

On a whole trial, how often retrieval is used and how often it errs are fixed by the associations, the criterion and the search length alone. The error rate on counting trials is fixed by the counting process alone. Throughout, T ≠ 0.

**Lemma 9 (backup strategies never retrieve).** Let E be any event that contains no fingers outcome and no counting-fingers outcome. Then the backup phase (A4 and A5) gives E probability 0.

*Proof.* The backup phase draws x from the elaborated strengths. If s′(x) > c it ends with a fingers outcome, which has probability 0 for E. Otherwise it runs the counting process and ends with a counting-fingers outcome. By Lemma 2 (g₁ and g₂ empty, k = 0), that also has probability 0 for E. Lemma 2 applied again to the draw of x gives 0. ∎

**Theorem 6 (how often retrieval is used).** On a trial, retrieval is the strategy used with probability 1 − (1 − R)ⁿ.

*Proof.* The trial first runs retrieval. If it states x, the outcome is (retrieval, x), so the event holds with probability 1. If retrieval is exhausted, the backup phase follows, which by Lemma 9 has probability 0 for the event. Lemma 2 gives Pr\[retrieval states some answer\], which is 1 − (1 − R)ⁿ by Lemma 7. ∎

The chapter gives the probability of overt strategy use as (1 − R)^N (p. 250). That is the complement of Theorem 6, since overt strategies are used on exactly the trials where retrieval is exhausted (Theorem 1).

**Theorem 7 (errors on retrieval trials).** On a trial, retrieval states a wrong answer with probability Q\_wrong · Gₙ, where "wrong" means x ≠ σ. If some answer has strength above c:

```math
\Pr[\text{retrieval},\ \text{wrong}] \;=\; \Pr[\text{retrieval}] \cdot \frac{S(s,\ \text{reach} \cap \text{wrong})}{S(s,\ \text{reach})}
```

So the error rate on retrieval trials is the wrong answers' share of the strength above the criterion.

*Proof.* As in Theorem 6, with the event "retrieval, and the answer is wrong": by Lemmas 2 and 9 its probability is that of retrieval stating a wrong answer, which is Q\_wrong Gₙ by Theorem 2. For the second form, Theorem 6 and Lemma 7 give Pr\[retrieval\] = R Gₙ. So Pr\[retrieval, wrong\] = Pr\[retrieval\] · Q\_wrong / R, and Q\_wrong / R is the share of strength (Theorem 3). The hypothesis makes S(s, reach) and hence R nonzero. ∎

**Theorem 8 (retrieval does not depend on the backup strategies).** For any two settings of the backup parameters (e, qₛ, q\_d) and (e′, qₛ′, q\_d′), the probability that retrieval is used, and the probability that retrieval states a wrong answer, are the same.

*Proof.* The formulas of Theorems 6 and 7, 1 − (1 − R)ⁿ and Q\_wrong Gₙ, mention only A, s, c and n. ∎

**Lemma 10 (counting always gives an answer).** For any qₛ and q\_d, counting k objects is a distribution of mass 1.

*Proof.* By induction on k. Counting 0 objects gives 0 with probability 1. Counting k + 1 objects counts k, giving some r, and then gives r, r + 1 or r + 2 with probabilities qₛ, 1 − qₛ − q\_d and q\_d. These sum to 1 for every r. So by Lemma 2 (g₁ everything, g₂ empty) the mass is that of counting k objects, which is 1 by hypothesis. ∎

**Theorem 9 (errors on counting trials do not depend on the associations).** Let C\_wrong be the probability that counting σ objects does not give σ. Then:

```math
\Pr[\text{counting fingers},\ \text{wrong}] \;=\; \Pr[\text{counting fingers}] \cdot C_{\text{wrong}}
```

So the error rate on counting trials is C\_wrong. It depends only on qₛ, q\_d and the sum, not on the strengths s, the criterion c or the search length n. This is the chapter's "nonintuitive prediction" (p. 245): retrieval errors and overt strategy use both depend on the distribution of associations, while errors on counting trials depend on other factors.

*Proof.* Let P be any property of answers. The event "counting fingers, with an answer having P" goes through three stages, and we apply Lemma 2 at each one.

1. *Counting.* Counting σ objects and stating the result gives the event probability Pr\[count ∈ P\], with g₁ = P.
2. *Elaborated retrieval.* After the draw x, counting follows only if s′(x) ≤ c. Otherwise the outcome is a fingers outcome, with probability 0 for the event. So the backup phase gives Pr′\[not reach\] · Pr\[count ∈ P\], with g₂ = "x does not reach" and k from stage 1.
3. *Retrieval.* If retrieval states an answer, the outcome is a retrieval outcome, with probability 0. If it is exhausted, stage 2 follows. With g₂ = "exhausted" and Theorem 1, the trial gives (1 − R)ⁿ · Pr′\[not reach\] · Pr\[count ∈ P\].

With P = "wrong", this is (1 − R)ⁿ · Pr′\[not reach\] · C\_wrong. With P true of every answer, Lemma 10 makes the last factor 1, so Pr\[counting fingers\] = (1 − R)ⁿ · Pr′\[not reach\]. Substituting the second into the first proves the theorem. ∎

Theorem 9 holds even though *how often* counting happens does depend on the associations. The associations decide whether counting is reached, not what counting does once reached.

## Peakedness

Moving strength toward the correct answer never raises the error rate on retrieval trials, at any criterion and any search length. The corresponding claim for overt strategy use (p. 245) does not hold in general.

Fix the problem's sum σ, and compare two sets of strengths s and s′, both non-negative, with:

- s′(σ) ≥ s(σ): the correct answer gains (or keeps) strength;
- s′(x) ≤ s(x) for every x ≠ σ: no wrong answer gains.

The totals need not be equal. At a criterion c, write W = S(s, reach ∩ wrong) and C = S(s, reach ∩ right) for the wrong and correct strength above c under s. Write W′ and C′ for the same under s′, where "reach" now means s′(x) > c.

**Theorem 10 (shifting strength to the correct answer).** W′ · (W + C) ≤ W · (W′ + C′).

*Proof.* There are three steps.

1. *W′ ≤ W.* Take a wrong answer x that reaches the criterion under s′. Then s(x) ≥ s′(x) > c, so it also reaches the criterion under s, and its strength there is at least as large. Lemma 6 gives W′ ≤ W.
2. *C ≤ C′.* The only correct answer is σ. If it reaches the criterion under s, then s′(σ) ≥ s(σ) > c, so it reaches under s′ too, with at least as much strength. Lemma 6, with the roles of s and s′ exchanged (it needs s′ ≥ 0), gives C ≤ C′.
3. *Combining.* Expanding, the claim is W′W + W′C ≤ WW′ + WC′, that is, W′C ≤ WC′. Since C ≥ 0 and W′ ≤ W, we have W′C ≤ WC. Since W ≥ 0 and C ≤ C′, we have WC ≤ WC′. ∎

**Theorem 11 (peaking lowers retrieval errors).** If some answer reaches the criterion under s, and some answer reaches it under s′, then at that criterion:

```math
\frac{W'}{W' + C'} \;\le\; \frac{W}{W + C}
```

By Theorem 7, the two sides are the error rates on retrieval trials under s′ and under s, for every search length.

*Proof.* By Lemma 5, W + C = S(s, reach) and W′ + C′ = S(s′, reach), and both are positive by hypothesis. For positive b and d, a·d ≤ c·b implies a/b ≤ c/d. Apply this to Theorem 10 with a = W′, b = W′ + C′, c = W and d = W + C. ∎

### Why overt strategy use is different

No theorem of the same form holds for overt strategy use. The trouble is that a wrong answer losing strength can drop out of the reach of the criterion altogether, taking all its strength out of R.

**Proposition.** Keep the total T fixed, and move strength d > 0 from a wrong answer x to σ. Suppose σ is already above c, and the move takes x from above c to at or below it: s(x) > c ≥ s(x) − d. Then R falls by (s(x) − d)/T. So, by Theorem 1, overt strategy use at that criterion rises whenever s(x) > d.

*Proof.* Before the move, the strength above c includes s(x) and s(σ). After it, it includes s(σ) + d but not x, and no other answer changes. The change in T·R is d − s(x). Overt strategy use is (1 − R)ⁿ, which rises strictly as R falls when n ≥ 1. ∎

The proposition is proved here and not yet in Lean. In Lean, a worked case (`peaking_can_raise_overt_use`) uses specific strengths to show that the rise can survive averaging over the chapter's twelve criteria. That case is numerical, so it is outside this document. Whether peakedness lowers overt use when the criterion is spread uniformly, rather than over a grid, is an open question (the conjecture is that it does, in the majorization order).

## Lean source

Every lemma and theorem above, except the Proposition, is proved in Lean 4.35 in the [CogLean repository](https://github.com/jeffshrager/CogLean). There is no `sorry`, and `#print axioms` shows only `propext`, `Quot.sound` and `Classical.choice`. Probabilities are exact rationals, and only core Lean is used. General results are in CogLib, the library shared by all theories, and the model's own are in the strategy-choice package. To check them: `cd StrategyChoice && lake build`.

| Here | Lean name | File |
| --- | --- | --- |
| Lemma 1 | `Dist.prob_bind_cons` | `CogLib/CogLib/Rep/Distribution.lean` |
| Lemma 2 | `Dist.prob_bind_split` | `CogLib/CogLib/Rep/Distribution.lean` |
| Lemma 3 | `Dist.prob_add_not` | `CogLib/CogLib/Rep/Distribution.lean` |
| Lemma 4 | `Dist.prob_sample`, `Dist.mass_sample`, `prob_not_above` | `CogLib/CogLib/Rep/Distribution.lean`, `CogLib/CogLib/Process/SampledRetrieval.lean` |
| Lemma 5 | `Dist.strengthIn_split` | `CogLib/CogLib/Rep/Distribution.lean` |
| Lemma 6 | `Dist.strengthIn_mono` | `CogLib/CogLib/Rep/Distribution.lean` |
| Theorem 1 | `prob_exhausted` | `CogLib/CogLib/Process/SampledRetrieval.lean` |
| Theorem 2 | `prob_stated` | `CogLib/CogLib/Process/SampledRetrieval.lean` |
| Lemma 7 | `reach_mul_geom` | `CogLib/CogLib/Process/SampledRetrieval.lean` |
| Theorem 3 | `stated_share`, `reachSuch_div_reach` | `CogLib/CogLib/Process/SampledRetrieval.lean` |
| Lemma 8 | `reach_nonneg`, `reach_le_one` | `CogLib/CogLib/Process/SampledRetrieval.lean` |
| Theorem 4 | `exhausted_antitone_reach` | `CogLib/CogLib/Process/SampledRetrieval.lean` |
| Theorem 5 | `exhausted_antitone_length` | `CogLib/CogLib/Process/SampledRetrieval.lean` |
| Lemma 9 | `SC.prob_backup_zero` | `StrategyChoice/StrategyChoice/Phenomena.lean` |
| Theorem 6 | `SC.retrieval_prob` | `StrategyChoice/StrategyChoice/Phenomena.lean` |
| Theorem 7 | `SC.retrievalWrong_prob`, `SC.retrieval_error_share` | `StrategyChoice/StrategyChoice/Phenomena.lean` |
| Theorem 8 | `SC.retrieval_independent_of_backup` | `StrategyChoice/StrategyChoice/Phenomena.lean` |
| Lemma 10 | `SC.mass_count` | `StrategyChoice/StrategyChoice/Phenomena.lean` |
| Theorem 9 | `SC.prob_trial_counting`, `SC.counting_error_share` | `StrategyChoice/StrategyChoice/Phenomena.lean` |
| Theorem 10 | `stated_share_shift` | `CogLib/CogLib/Process/SampledRetrieval.lean` |
| Theorem 11 | `aboveShare_shift`, `SC.peaking_lowers_retrieval_errors` | `CogLib/CogLib/Process/SampledRetrieval.lean`, `StrategyChoice/StrategyChoice/Phenomena.lean` |

The postulates themselves, with page citations, are in `StrategyChoice/StrategyChoice/Postulates.lean`. Names without a prefix are in the namespace `Cog`. Lean states Lemma 1 one list element at a time, and derives the sum form by induction inside Lemma 2.
