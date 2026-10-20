# EPAM in CogLean

EPAM (Feigenbaum, RAND P-1817, 1959; Feigenbaum & Simon 1962) is the first theory in CogLean (`../README.md`), a library of cognitive theory in Lean 4. EPAM's postulates (P-1817 §2.4) are choices from the general constructs of **CogLib** (`../CogLib/`): feature codes, discrimination nets, discrimination learning with a noticing order, cue codes, serial attention to anchor points. This directory records those choices, proves the phenomena EPAM was built to explain (most of them through CogLib's theory-neutral statements of the phenomena), and computes a full serial-anticipation experiment.

The proofs are **qualitative**. They show that a phenomenon *follows from* (or *is possible under*) the postulates, not that it matches human data in size. Everything is machine-checked: `lake build` succeeds, there is no `sorry`, and `#print axioms` shows only Lean's standard `propext`, `Quot.sound` and `Classical.choice`. EPAM has 30 theorems of its own; the 27 general ones it uses are in CogLib.

```sh
cd EPAM
lake build          # builds CogLib too; Lean 4.35.0 via elan (~/.elan), core Lean only
```

## What is modelled

The model is deliberately abstract. It formalizes the *propositions*, not the 1959 IPL-V code, which is reconstructed and run in the ExecutableArchaeology project ([EPAM/IPL](https://github.com/jeffshrager/ExecutableArchaeology/tree/main/EPAM/IPL)).

| Concept (P-1817) | CogLib |
|---|---|
| Stimulus code, a string of bits (§3.3.2) | `Cog.Item := List Bool`, `Item.feat` (`Rep/Features`) |
| Discrimination net: testing points and terminals holding an image or the null image (§3.4.1) | `Cog.Net` (`leaf`, `test`) (`Memory/DiscriminationNet`) |
| Noticing order (F1b; the listing's P0/P1) | `Cog.NoticingOrder` (`Control/Attention`) |
| Cue code: partial information about a response (F2) | `Cog.Cue`, `cueOf` (`Memory/Cue`) |
| A test with missing information branches at random (§3.5.1.2) | `Net.CueSelects`, a relation with `guess0`/`guess1` (`Memory/Cue`) |

`Epam/Postulates.lean` quotes each postulate and names the CogLib construct that realizes it. `Epam.learner order` is EPAM as a `Cog.IncrementalLearner`, the interface CogLib's phenomena are stated about.

## Postulates and what is proved

The mechanism-level results are proved once, in CogLib, for any net, code and noticing order. EPAM inherits them.

**Microprocesses**

| Postulate (§2.4) | CogLib definition | Proved properties (CogLib) |
|---|---|---|
| D2 Selection: codes select images in a discrimination net | `Net.select`, `Net.path` | `select_depends_only_on_noticed_features`: what a stimulus is recognized as depends only on the features examined on its path. `discrimination_needs_a_difference`: a net that tells two stimuli apart must have tested a feature on which they differ. |
| F1 Discrimination learning: find a unique terminal, or grow the net at a point of confusion | `Net.learn` | `learn_recognizes`: after learning, the stimulus is recognized. `learn_preserves`: learning never disturbs another stimulus's recognition. `learnAll_recognizes`: a list of noticeably different stimuli is learned with one F1 cycle each. |
| F1a Redundancy (P2 > 1) | `Net.learnK`, `Net.chain` | (used by the experiment) |
| F1b Noticing order | `firstDiff`, `diffs`, `scanCost` | `learned_test_is_first_noticed_difference`: the test grown is the first difference in the noticing order. `scanCost_ge_of_agree`: stimuli that agree on the first *k* noticed features cost at least *k* scanning steps. |
| F2 Association by cue code ("enough of the code for Y") | `cueOf`, `cueFor`, `Net.CueSelects` | `cue_from_path_selects`: the cue holding the response's path features selects it, and nothing else. `cue_can_fail_after_growth`, `learning_can_capture_old_cue`: as the net grows, a cue can become insufficient. |
| R Responder (D2 applied to the cue) | `Net.CueSelects`, `Net.cueResults` | (used by the results below) |
| D8 Restoration: add information to the cue after a failure | `cueOf y (N.path y)` on the grown net | `restoration`: the rebuilt cue re-establishes the link. |

**Macroprocesses** (Feigenbaum & Simon 1962)

| Postulate | CogLib definition | Proved properties (CogLib) |
|---|---|---|
| M0 Serial mechanism + M1 Unit processing time | one learning cycle per trial | `trials_at_least_items`: *n* items need at least *n* trials. |
| M3 Anchor points: attend first to the ends, then inward | `learnedOnTrial`, `errorsAt` | `anchorAttention_serialPosition`: the serial position effect. `first_position_fewest_errors`, `errors_rise_toward_middle`, `errors_fall_toward_end`: the error curve is bowed. |

M2 (immediate memory) is not used yet.

## The phenomena, and the claims they formalize

All in `Epam/Phenomena.lean`. Where CogLib states the phenomenon theory-neutrally (`Cog.Phenomena`), EPAM's theorem is about that statement, for EPAM's learner.

| Phenomenon (P-1817 §4.1.1.3, unless noted) | Theorem | Reading |
|---|---|---|
| **Stimulus generalization** (4.1.1.3.2; e.g. Fig. 4.1, trial 4, "PEM is confused with ROM") | `stimulus_generalization` (`Cog.Phenomena.StimulusGeneralization`), `stimulus_generalization_List_A` | An untrained stimulus that agrees with a learned one on the features its path examines is recognized *as* that one. |
| **Intralist similarity** (4.1.1.3.3) | `intralist_similarity_needs_differences`, `intralist_similarity_costs_scanning` | Similar items can only be told apart on their few differing features, and finding those costs more scanning. |
| **Oscillation** (4.1.1.3.4: a response is right, then wrong, then right) | `oscillation` | A cue that was enough when formed may not be after the net grows. The same stimulus can then give a wrong response, or still the right one. |
| **Recovery** (D8) | `recovery` | Adding the new path's features to the cue makes the response correct again. |
| **Retroactive inhibition** (4.1.2) | `retroactive_inhibition` | Learning new material can undo a correct old response, by the same mechanism as oscillation. |
| **Non-interference of learning** | `non_interference` (`Cog.Phenomena.NonInterference`) | Learning one item never undoes the recognition of another. |
| **Learning to criterion** | `learning_to_criterion` (`Cog.Phenomena.ReachesCriterion`) | From an empty memory, any list of mutually noticeable items is learned with one cycle per item. Proved in CogLib from non-interference, by a theorem that holds for every learner. |
| **Total time ~ amount to be learned** (M0/M1) | `total_time` | |
| **Serial position effect** (Feigenbaum & Simon 1962) | `serial_position_effect` (`Cog.Phenomena.SerialPositionEffect`) | A bowed error curve, from anchor-point attention. |

## Simplifications (for honesty)

- **F1 adds one test per confusion.** That corresponds to the listing's P2 = 1. The §4.1 hand simulation allowed up to three. F1a (redundant tests) is not modelled.
- **Cues are built exactly from the response's path** at learning time, the minimal sufficient cue. P-1817 says the amount is set "by trial and error"; this model takes the end state of that process.
- **The macro model is the simplest anchor-point schedule.** Attention works inward from both ends, one association per trial, front first at equal distances. It gives the qualitative bow, not the McCrary-Hunter percentages that the 1962 paper fits quantitatively.
- **No timing, no probabilities.** "Random" branching is modelled as possibility (either branch can happen), so `oscillation` says a wrong response *can* occur, not how often.
- **Not yet stated:** response generalization, error types and their distribution (4.1.1.3.5), and serial anticipation vs paired associates (4.1.1.3.6).

## Files

| File | Contents |
|---|---|
| `Epam/Postulates.lean` | EPAM's postulates, quoted, each mapped to the CogLib construct that realizes it; `Epam.learner` |
| `Epam/Phenomena.lean` | The phenomena under their psychological names, proved from the postulates |
| `Epam/ListA.lean` | The List A instance (generated by `gen_lista.py`): Fig. 4.1's trial-4 confusion of PEM with ROM, computed by the kernel |
| `Epam/Experiment.lean` | EPAM's learner state (net plus a cue per image), the learning events of its F0 cycle, and all possible responses (R) |
| `Epam/Fig41.lean` | Fig. 4.1, checked: the figure's learning schedule, and its 34 recorded responses compared with what the postulates make possible |
| `Epam/Fig41Alt.lean` | Fig. 4.1 under other U1-consistent codes, which reproduce all 34 (generated by `analysis/gen_alt.py`) |
| `phenomena_learning-to-criteria_narrative.md` | A walk through one multi-level theorem (`learning_to_criterion`) and the lemmas it rests on |
| `analysis/` | `robustness.py` and `RESULTS.md`, testing Feigenbaum's robustness footnote (p. 87) |
| `data/` | The letter codes reconstructed from EPAM II's letter net U1 |

## A concrete case: List A and Fig. 4.1

`Epam/ListA.lean` codes List A (KAG LUK RIL PEM ROM TIL, §4.1.1.1.1) letter by letter.
- **The codes.** A's code is the listing's Q1. The other letters' codes are reconstructed from EPAM II's own letter net U1 (`data/letter_codes.py`, `data/letter_codes.txt`, copied from ExecutableArchaeology's [EPAM/IPL](https://github.com/jeffshrager/ExecutableArchaeology/tree/main/EPAM/IPL)): the bits U1 tests on a letter's path are fixed by U1, and untested bits are 0. All 26 reconstructed codes sort back to their own letter through U1.
- **The setup.** The noticing order is first letter, third, second (§4.1.1.1.2, the listing's P0). The net starts empty, and the syllables are learned in Fig. 4.1's order.

The kernel then checks (`decide`):

- `trial4_PEM_confused_with_ROM`: after KAG, LUK, RIL, ROM and TIL have been learned (trials 1-3), **the unlearned PEM is recognized as ROM**. This is Fig. 4.1, trial 4: "PEM is confused with ROM and response to ROM is made".
- `PEM_agrees_with_ROM_on_ROMs_path`, `PEM_ROM_first_noticed_difference`: why. P and R differ only in bit 8 of the first letter, the third letters are both M, and the net has never needed to test that bit.
- `scan_costs`: PEM/ROM is the most similar pair. Its scan costs 8 steps; KAG/LUK costs 5.
- `trial5_all_recognized`: once PEM is learned (trial 5), all six are recognized.

`Phenomena.stimulus_generalization_List_A` derives the trial-4 confusion from the general theorem `stimulus_generalization`. The confusion was *predicted* from the postulates and the reconstructed codes; it was not built in. Feigenbaum's hand simulation used idealized codes.

## Fig. 4.1, the whole experiment (`Fig41.lean`)

The experiment machinery (`Experiment.lean`) adds what the hand simulation used:
- F1 notices up to P2 = 3 differences and adds redundant tests with null images (F1a); those are where "none" responses come from;
- each image stores a cue code for its response (F2);
- responding sorts the cue, and either branch is possible where it is silent.

The learning schedule (which F1, F2 and D8 happens on which trial and row) is transcribed from the figure, because timing and attention are left to the experimenter. The responses are computed from the postulates. The kernel checks:

- **33 of the figure's 34 recorded responses are possible** (`fig41_agreement`);
- note 7, trial 4: PEM *can only* give TIL, ROM's response (`trial4_PEM_gives_ROMs_response`);
- note 6, trial 4: LUK's cue is insufficient, so RIL, ROM or none are possible (oscillation);
- note 10: once D8 restores it, LUK gives RIL;
- criterion on trial 7, and not on trial 6;
- the one disagreement, KAG on trial 6, depends on the codes (`fig41_disagreement`). Under other U1-consistent codes all 34 are possible (`Fig41Alt.alt_agreement`). There KAG's trial-7 success is possible but not certain (`alt_trial7_KAG_by_chance`), which is what note 12 says ("by chance").

## Robustness (`analysis/RESULTS.md`)

Feigenbaum claimed that the qualitative behavior does not depend sensitively on the codes, the noticing order or P2 (p. 87). Sampling U1-consistent codes, all six letter orders and P2 = 1-3, the claim is **partly right**:
- the phenomena (generalization errors, oscillation, learning in about seven trials) are robust;
- the particular errors are not;
- oscillation by omission needs P2 ≥ 2 (F1a);
- the PEM/ROM confusion needs the third letter noticed before the vowel;
- vowel-first noticing fits the figure worst.

## Next

1. State the rest of Fig. 4.2 (paired associates: RIL → LUK, ROM → LUK).
2. The phenomena not yet stated: response generalization, error types (4.1.1.3.5), serial anticipation vs paired associates (4.1.1.3.6). Oscillation and retroactive inhibition still need theory-neutral statements in `Cog.Phenomena` (they need a responder interface, not just recognition).
3. Tie the model to the running IPL-V program ([ExecutableArchaeology EPAM/IPL](https://github.com/jeffshrager/ExecutableArchaeology/tree/main/EPAM/IPL)): run List A with the same codes and check for the same confusions (needs the experiment driver; ExecutableArchaeology OPEN_ISSUES #17-18).
