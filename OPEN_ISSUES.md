# Open issues

## Library

1. **Theory-neutral oscillation and retroactive interference.** CogLib states these only at the mechanism level (`cue_can_fail_after_growth`, `learning_can_capture_old_cue`). A phenomenon-level statement needs a *responder* interface (a learner that can give a response to a stimulus, possibly nondeterministically), alongside `IncrementalLearner`.
2. **Experiments as a layer.** Lift the serial-anticipation machinery (learning schedule, possible responses per trial) out of `EPAM/Epam/Fig41.lean` into `CogLib/Experiments/`.

## EPAM

3. **Fig. 4.2, paired associates** (RIL → LUK, ROM → LUK).
4. **Phenomena not yet stated:** response generalization; error types and their distribution (P-1817 §4.1.1.3.5); serial anticipation vs paired associates (§4.1.1.3.6).
5. **Cue codes sized by trial and error** (the model uses the minimal sufficient cue).
6. **M2, immediate memory**, unused so far.
7. **Tie to the running IPL-V program** in ExecutableArchaeology (`EPAM/IPL`): run List A with the same codes there. Blocked on the experiment driver and the missing J16/J135 in that project's interpreter (its OPEN_ISSUES #17-18).

## Next theories

8. **ACT-R**: the main next target. Real-valued activation and the fan effect; contrast with EPAM, which puts interference in cues (retrieval), not storage (`EPAM/phenomena_learning-to-criteria_narrative.md`, lesson 2). Likely needs Mathlib (`Real.log`) or an abstract ordered field.
9. Other candidates: Yngve's depth hypothesis (bounded-memory sentence production); a production-system theory.
