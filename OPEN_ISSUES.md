# Open issues

## Library

1. ~~Theory-neutral oscillation and retroactive interference.~~ Done: `Phenomena/Responder.lean` (`Responder`, `ProbResponder`, `Oscillation`, `RetroactiveInterference`); EPAM's `oscillation_phenomenon`, `retroactive_inhibition_phenomenon`.
2. **Experiments as a layer.** Begun in `Experiments/`: study-test experiments, written once against `Retriever` and run with any memory family (`PrototypeDemo.lean`: EPAM, ACT-R, strength and MINERVA on one experiment, every number a theorem; `curve_flat`, an experiment property from laws). To do:
   - feedback-driven learning (respond, feedback, update), with exact runs for short sequences, sampled runs for long ones, and statements over all runs; multi-digit addition as the target (#12);
   - lift EPAM's serial-anticipation machinery (`EPAM/Epam/Fig41.lean`) into the layer;
   - a recognition decision on familiarity, which needs a richer interface than `Retriever`.

## EPAM

3. **Fig. 4.2, paired associates** (RIL → LUK, ROM → LUK).
4. **Phenomena not yet stated:** response generalization; error types and their distribution (P-1817 §4.1.1.3.5); serial anticipation vs paired associates (§4.1.1.3.6).
5. **Cue codes sized by trial and error** (the model uses the minimal sufficient cue).
6. **M2, immediate memory**, unused so far.
7. **Tie to the running IPL-V program** in ExecutableArchaeology (`EPAM/IPL`): run List A with the same codes there. Blocked on the experiment driver and the missing J16/J135 in that project's interpreter (its OPEN_ISSUES #17-18).

## Next theories

8. **Strategy choice** (Siegler & Shrager 1984), in `StrategyChoice/`. Done: postulates A1-A5, the trial, the closed-form phenomena, six rows of Fig. 9.2A with exact predictions. To do:
   - The learning simulation (A6 itself is now stated: `SC.strengthen`, `correct_strengthening_lowers_errors`) (Python prototype, checked against the chapter: after 2000 trials 1+4 has 77% of its strength at 5 vs 46% for 2+3; 4+1 peaks at .80 vs .51 for 3+2). Needs the original simulation code for what the chapter leaves open: the size of the counting-string prime, the increment, the skip and double-count probabilities, how the criterion and search length are drawn.
   - The full 25-problem Fig. 9.2A (the OCR of the scan is garbled; transcribe and check, or take from the code).
   - Solution times (expected searches) and the strategies' time ordering.
   - A theory-neutral statement of strategy-choice phenomena in `CogLib/Phenomena/` (a strategy-chooser interface), so ACT-R can be tested against the same statements.
9. **"More peaked" needs a definition.** Moving strength to the correct answer never raises retrieval errors, at any criterion (`peaking_lowers_retrieval_errors`). But concentrating strength can *raise* overt-strategy use: pointwise in the confidence criterion, and even averaged over the chapter's 12 criteria (`peaking_can_raise_overt_use`). A Python check (3000 random cases) found no case under a uniform criterion; the conjecture there is that mean overt use is monotone in the majorization order. Proving it needs an integral over the criterion, or a fine uniform grid with a limit argument.
10. **ACT-R declarative memory**, after strategy choice, as a rival theory of the same data: its tutorial `siegler-model.lisp` fits the 4-year-olds' answer distributions by partial matching, with no backup strategy, criterion or learning. Needs Mathlib (`Real.log`, `Real.exp`) in an `ACTR/` package only.
11. Other candidates: Yngve's depth hypothesis (bounded-memory sentence production); a production-system theory; SCADS (Shrager & Siegler 1998), strategy discovery.
12. **Multi-digit addition** (`MultiDigit/`, EPAM + DOA). Done:
    - postulates M1-M5 and predictions 1-12 (`docs/PREDICTIONS.md`);
    - the column backup from single-digit DOA trials;
    - discrimination after confusion;
    - nets learned by EPAM are clean (`learnAll_clean`);
    - further features (M1a–M1c: zeros, magnitude, column facts) and Predictions 13–18 (`FeaturePhenomena.lean`).

    - a blind Python simulation (`MultiDigit/sim/`), checked against preregistered predictions and Lean's exact distributions: no failures (`sim/README.md`).

    To do: learning sequences over many trials; carrying with errors; columns that are not independent.
13. **Coverage hypotheses are too strong for learned nets** (found by `MultiDigit/sim`). Predictions 6, 14, 17 and 18 need the path to test every feature of a digit or column, and no EPAM-learned net in the simulation ever did. Restate them in terms of the features that are tested: the tested bits of a digit restrict it to a set; a tested fact feature that reads 1 fixes the fact.
14. **Zero total strength** (found by `MultiDigit/sim`). `Cog.sample` divides by the total, so with total 0 a trial has mass 0. The theorems assume total ≠ 0. The model's natural reading is "retrieval exhausted". Define search with total 0 as exhausted, so that a newly discriminated problem with no associations is covered.
15. **Initial associations of a discriminated problem** (O2 in `MultiDigit/sim/SPEC.md`). The predicted sequence (confident error, then columns, then fluent retrieval) holds when they are empty, is skipped when they hold the correct answer, and fails when they copy the neighbour's associations. The model must say which, and the sequence should then be proved.
16. **ACT-R declarative memory as a second memory for `MultiDigit`** (cf. #10). Done:
    - `CogLib/Memory/Activation.lean`: `actRetriever`, ACT-R retrieval for decay 1 and temperature 1 (rational: base level `Σ 1/(t - t_k)`, times `μ^mismatches`, with failure weight `θ`). `Act.retrieve_not_certain`.
    - `MultiDigit/ExampleACTR.lean`: the worked case with ACT-R. The differences are proved there: graded confusion, no certain retrieval, `¬ AgreesOn`, interference with a practiced problem (`docs/PREDICTIONS.md`, "Which predictions need EPAM").

    To do:
    - General results, not just the worked case. Frequency and recency raise retrieval probability; each mismatch lowers it; `¬ AgreesOn` whenever μ > 0 and a stored chunk differs on a feature.
    - **`StableRetrieval` holds for ACT-R only vacuously**, since nothing is retrieved for certain. A law of memory that separates the theories should be graded. For example: "studying z never changes the probability of retrieving y", which EPAM has and ACT-R lacks. Likewise a graded `AgreesOn`: "anything retrieved with positive probability agrees on fs".
    - General decay d and temperature s, in an `ACTR/` package with Mathlib (`Real.rpow`, `exp`). Prove that the rational case is its special case.
    - Check against PyACTUp itself (https://cmu-psych-fms.github.io/fms/pyactup/) on shared instances. `blend` uses the Boltzmann weights, so it can match exactly. `retrieve` takes the argmax under logistic noise, which softmax only approximates, so check it within 4σ, as `MultiDigit/sim/compare.py` does.
    - ACT-R for M3 too: the answer associations, as in Lebiere's model of arithmetic.
17. **The theory matrix** (`CogMatrix/`, `PROSPECTUS.md`). Done: 5 laws × 4 families (discrimination, activation, strength, global matching), all 20 cells proved, and every family with its own row. Global matching tested the first four laws and matched strength memory on all of them; the fifth law, stored-only retrieval, separates the two. To do:
    - Further families as further tests: ACT-R with blended retrieval (closest to the evidence: activation conflicts only on stored-only retrieval), REM, a distributed or connectionist memory, CHREST, and EPAM's paired-associate memory with cue codes (which would lack stability).
    - The evidence row (`CogMatrix/evidence.json`) is a judgment. Have it checked by someone who knows the literature, and add laws' settings (recall vs recognition, immediate vs delayed test).
    - Map the parameter regions of the "lacks" cells. Each is one counterexample; e.g. strength memory with `μ = 0` may have certainty, and global matching with few traces may.
    - Certainty and stability have the same row (only discrimination has them). Find what separates them, or merge them.
    - Graded versions of the MultiDigit laws (`StableRetrieval`, `AgreesOn`; #16). Then move MultiDigit's predictions onto these laws, so that `MultiDigit/docs/PREDICTIONS.md`'s table is read off the matrix.
    - More interfaces: strategy choice (#8), then production systems.
