# Sims: simulations that run the library's own definitions

CogLean's models are computable Lean definitions, so the code the theorems are about can also be run. This package runs them as simulations: many trials, with learning between them, drawing one outcome at a time from the models' exact distributions.

**Dependencies run one way.** `Sims/` requires CogLib and the theory packages it simulates. Nothing in the library or the theories imports it, so the proofs, the matrix and the catalog never depend on simulation code.

```sh
cd Sims
lake build
lake exe sc-check                    # the sampler against the exact model
lake exe sc-learning --runs=20       # Siegler & Shrager's learning phase
lake exe sc-learning --sweep         # increment × prime-size sweep
```

## Sampling (`Sims/Sampling.lean`)

- **The generator** is Lean core's seeded `StdGen`, so a run is reproducible from its seed.
- **Draws are exact rationals.** A uniform `k / 10^9` is compared with a distribution's cumulative probabilities. There is no floating point in the draw. Floats appear only in reported summaries.

## Strategy choice with learning (`Sims/StrategyChoice.lean`)

This is the learning phase of Siegler & Shrager's (1984) simulation, pp. 272–275.

**Each trial is drawn stage by stage, following `SC.trial`:**
- retrieval up to the search length, each answer drawn from `Cog.sample` and stated if `Cog.above` the criterion;
- otherwise the backup, using `SC.elaborate`;
- otherwise counting, object by object, as in `SC.count`.

Learning is `SC.strengthen`. The stages are followed rather than `SC.trial` being expanded in full, because building `SC.count`'s complete distribution unmerged is exponential in the sum.

**`sc-check` confirms the sampler against the exact `SC.trial`.** On small cases, every outcome's frequency lies within 4 standard errors of its exact probability.

**From the chapter:**
- answers 1–12, every association initially .01;
- the 25 problems presented by Table 9.5's parental input plus a constant (fn. 13);
- the criterion uniform on .05–.99 (here in hundredths) and the search length on 1–3, for each trial;
- elaboration adds .05;
- on ascending and tie problems, a momentary association to the second addend plus one (the counting-string prime).

**Not given in the chapter, so parameters:**
- the size of the prime;
- the increment;
- the counting error rates;
- the constant added to the presentation percentages. `c = 12` reproduces the chapter's 5.4% for 4 + 1 and its 2% floor.

**Targets:** the peaks and shares of Fig. 9.8 after 2000 trials. Results: `../notes/SC_simulation_RESULTS.md`.
