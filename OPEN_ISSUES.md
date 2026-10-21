# Open issues

## Library

1. ~~Theory-neutral oscillation and retroactive interference.~~ Done: `Phenomena/Responder.lean` (`Responder`, `ProbResponder`, `Oscillation`, `RetroactiveInterference`); EPAM's `oscillation_phenomenon`, `retroactive_inhibition_phenomenon`.
2. **Experiments as a layer.** Lift the serial-anticipation machinery (learning schedule, possible responses per trial) out of `EPAM/Epam/Fig41.lean` into `CogLib/Experiments/`.

## EPAM

3. **Fig. 4.2, paired associates** (RIL → LUK, ROM → LUK).
4. **Phenomena not yet stated:** response generalization; error types and their distribution (P-1817 §4.1.1.3.5); serial anticipation vs paired associates (§4.1.1.3.6).
5. **Cue codes sized by trial and error** (the model uses the minimal sufficient cue).
6. **M2, immediate memory**, unused so far.
7. **Tie to the running IPL-V program** in ExecutableArchaeology (`EPAM/IPL`): run List A with the same codes there. Blocked on the experiment driver and the missing J16/J135 in that project's interpreter (its OPEN_ISSUES #17-18).

## Next theories

8. **Strategy choice** (Siegler & Shrager 1984), in `StrategyChoice/`. Done: postulates A1-A5, the trial, the closed-form phenomena, six rows of Fig. 9.2A with exact predictions. To do:
   - A6 learning, and the learning simulation (Python prototype, checked against the chapter: after 2000 trials 1+4 has 77% of its strength at 5 vs 46% for 2+3; 4+1 peaks at .80 vs .51 for 3+2). Needs the original simulation code for what the chapter leaves open: the size of the counting-string prime, the increment, the skip and double-count probabilities, how the criterion and search length are drawn.
   - The full 25-problem Fig. 9.2A (the OCR of the scan is garbled; transcribe and check, or take from the code).
   - Solution times (expected searches) and the strategies' time ordering.
   - A theory-neutral statement of strategy-choice phenomena in `CogLib/Phenomena/` (a strategy-chooser interface), so ACT-R can be tested against the same statements.
9. **"More peaked" needs a definition.** Moving strength to the correct answer never raises retrieval errors, at any criterion (`peaking_lowers_retrieval_errors`). But concentrating strength can *raise* overt-strategy use: pointwise in the confidence criterion, and even averaged over the chapter's 12 criteria (`peaking_can_raise_overt_use`). A Python check (3000 random cases) found no case under a uniform criterion; the conjecture there is that mean overt use is monotone in the majorization order. Proving it needs an integral over the criterion, or a fine uniform grid with a limit argument.
10. **ACT-R declarative memory**, after strategy choice, as a rival theory of the same data: its tutorial `siegler-model.lisp` fits the 4-year-olds' answer distributions by partial matching, with no backup strategy, criterion or learning. Needs Mathlib (`Real.log`, `Real.exp`) in an `ACTR/` package only.
11. Other candidates: Yngve's depth hypothesis (bounded-memory sentence production); a production-system theory; SCADS (Shrager & Siegler 1998), strategy discovery.
