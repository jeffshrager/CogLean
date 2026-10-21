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

8. **Strategy choice** (Siegler & Shrager 1984, the distributions-of-associations model): the next theory, in `StrategyChoice/`. Retrieval by sampling with a confidence criterion and search length is in CogLib (`Process/SampledRetrieval.lean`). Still to do: the full trial (elaboration, counting with errors), learning, the Fig. 9.2A data, and the Python prototype of the learning simulation. Needs the original simulation code (for parameters the chapter leaves open) and a checked transcription of Fig. 9.2A.
9. **"More peaked" needs a definition.** Moving strength to the correct answer never raises retrieval errors, at any criterion (`stated_share_shift`). But concentrating strength can *raise* overt-strategy use: pointwise in the confidence criterion, and even averaged over the chapter's 12 criteria (.05, .10, .15, .20, .30, ..., 1.00). A Python check found no case under a uniform criterion; the conjecture there is monotonicity in the majorization order.
10. **ACT-R declarative memory**, after strategy choice, as a rival theory of the same data: its tutorial `siegler-model.lisp` fits the 4-year-olds' answer distributions by partial matching, with no backup strategy, criterion or learning. Needs Mathlib (`Real.log`, `Real.exp`) in an `ACTR/` package only.
11. Other candidates: Yngve's depth hypothesis (bounded-memory sentence production); a production-system theory; SCADS (Shrager & Siegler 1998), strategy discovery.
