# Open issues

## Library

1. **Lift the general constructs out of `EPAM/`** into theory-neutral modules (`Cog/Rep`, `Cog/Memory/DiscriminationNet`, `Cog/Memory/Cue`, `Cog/Control/Attention`, `Cog/Phenomena`, `Cog/Theories/EPAM`, `Cog/Experiments/SerialAnticipation`). Phenomena become predicates on learners; EPAM proves them about its learner. See the "Contribution to the library" table in `EPAM/README.md`.
2. **A single Lake project for the library**, once modules are shared across theories (today `EPAM/` is its own project).

## EPAM

3. **Fig. 4.2, paired associates** (RIL → LUK, ROM → LUK).
4. **Phenomena not yet stated:** response generalization; error types and their distribution (P-1817 §4.1.1.3.5); serial anticipation vs paired associates (§4.1.1.3.6).
5. **Cue codes sized by trial and error** (the model uses the minimal sufficient cue).
6. **M2, immediate memory**, unused so far.
7. **Tie to the running IPL-V program** in ExecutableArchaeology (`EPAM/IPL`): run List A with the same codes there. Blocked on the experiment driver and the missing J16/J135 in that project's interpreter (its OPEN_ISSUES #17-18).

## Next theories

8. **ACT-R**: the main next target. Real-valued activation and the fan effect; contrast with EPAM, which puts interference in cues (retrieval), not storage (`EPAM/phenomena_learning-to-criteria_narrative.md`, lesson 2). Likely needs Mathlib (`Real.log`) or an abstract ordered field.
9. Other candidates: Yngve's depth hypothesis (bounded-memory sentence production); a production-system theory.
