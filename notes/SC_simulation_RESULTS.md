# Siegler & Shrager's learning simulation, run from the Lean model

`Sims/` (`lake exe sc-learning`) runs the learning phase of the 1984 chapter's simulation (pp. 272–275). Every trial is drawn from the model's own definitions (`SC.trial`'s stages, `Cog.sample`, `SC.elaborate`, `SC.strengthen`). `lake exe sc-check` confirmed the sampler against the exact `SC.trial`: on three small cases, every outcome's frequency was within 1.6 standard errors of its exact probability (40,000 draws each).

## What the chapter specifies, and what it does not

**Specified:**
- answers 1–12, each initially .01;
- 2000 learning trials, with problems presented by Table 9.5's parental input plus a constant;
- the criterion drawn from .05–.99 and the search length from 1–3, on every trial;
- elaboration adds .05;
- a counting-string prime on ascending and tie problems;
- the increment for correct answers is twice that for incorrect ones.

**Not specified, so treated as parameters:**
- the size of the prime;
- the increment;
- the counting error rates;
- the constant added to presentation percentages. `c = 12` reproduces the stated 5.4% for 4 + 1 and the 2% floor.

## Results

**A coarse sweep, at 10 runs each.** The increment was swept over {1/400, 1/250, 1/200, 1/150, 1/100} and the prime over {.01, .02, .05, .1, .2}. The best region is an increment near .005 (1/200) with a large prime: there, the mean absolute difference from Fig. 9.8's peaks and shares is .06. Increments of 1/150 and above overshoot: strength accumulates too fast.

**At increment 1/200, prime .2 and counting errors .05 each,** means over 20 runs of 2000 trials:

| Problems (effect) | Peak | Chapter | Share of total | Chapter |
|---|---|---|---|---|
| 1+4 vs 2+3 (counting string) | .54 vs .40 | .67 vs .37 | .75 vs .61 | .77 vs .46 |
| 4+1 vs 3+2 (frequency) | .85 vs .55 | .80 vs .51 | .78 vs .71 | .76 vs .69 |
| 3+4 vs 4+5 (sum) | .31 vs .32 | .39 vs .32 | .55 vs .52 | .50 vs .43 |

**What this shows:**
- **The frequency effect is reproduced closely,** at every setting tried.
- **The counting-string effect is reproduced in direction, but only with a large prime,** .2, four times the elaboration's .05. With the default .05 it nearly vanishes: 1+4 at .48 against 2+3 at .46. The chapter does not give the prime's size; on this evidence it was large.
- **The sum effect is not reproduced at any setting tried.** That includes primes .2 and .4 and counting errors .02, .05 and .1: 4+5's peak is never below 3+4's. Three possible reasons:
  1. **Table 9.5 as read here gives 4+5 slightly more input** than 3+4 (1 parent against 0). The text says the two are identical in frequency. The scan's faint "1"s are uncertain, so this reading should be checked against a clean copy of the table.
  2. **The chapter's numbers come from one simulated run,** while these are means over 20, so a single run's sampling noise could account for a difference this small.
  3. **Unspecified details may matter:**
     - whether the criterion is continuous, rather than drawn in hundredths as here;
     - whether the prime also acts during elaboration (here it does);
     - the form of counting errors.

## Next

- Report run-to-run variability (the spread over runs), not only means, to judge point 2.
- Recheck Table 9.5 against a clean copy.
- The test phase: learning off, all problems equally often, compared with Fig. 9.2A's answer distributions.
- The multi-digit simulation, on the same sampler and driver, once its open choices are settled (OPEN_ISSUES #15, #18).
