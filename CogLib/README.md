# CogLib

The general part of CogLean: constructs of cognitive theory, and phenomena stated without reference to any theory. Theories (EPAM in `../EPAM/`, strategy choice in `../StrategyChoice/`, multi-digit addition in `../MultiDigit/`) import CogLib, choose among its constructs, and prove which phenomena they have.

CogLib must never import a theory. It is a separate Lake package so that this is enforced: a theory requires CogLib by path (see `../EPAM/lakefile.toml`), and CogLib requires nothing.

```sh
cd CogLib && lake build      # or build a theory, which builds CogLib first
```

No `sorry`; only Lean's standard axioms. Core Lean only (probabilities are core `Rat`).

## Layers

| Module | Contents | Main results |
|---|---|---|
| `Rep/Features` | feature codes: `Feature`, `Item`, `Item.feat` | |
| `Rep/Frames` | attribute-value frames: `Schema`, `Proto` (diagnosticity, votes), `Inst`, `Inst.pure`; similarity by the contrast rule, attribute by attribute: `Contrast`, `attrContrast`, `sim` | `attrContrast_pure`, `votesOn_pure`, `le_votesOn` |
| `Rep/SemanticNet` | semantic nets: `SemNet` (labelled links, a hierarchy label), `targets`, `level` (nodes *k* hierarchy links up), `valsAt`, `lookup` (property lookup with inheritance; the nearest level storing the property wins, so nearer values override), `findVal` (verify one value: climb until it is found; for a single-valued property a conflicting value found first answers false), `isaDist` | `lookup_local` (a property stored at a node is found there and overrides inherited ones), `lookup_inherits` (otherwise it comes from the nearest level that stores it: cognitive economy), `findVal_spec`, `mem_valsAt`, `isaDist_spec` (distance is the least level containing the target) |
| `Rep/Distribution` | finite distributions with exact rational probabilities: `Dist`, `pure`, `bind`, `prob`, `Possible`; mixtures: `prob_bind_sum`; sampling in proportion to strength: `sample`, `strengthIn`, `total` | `prob_bind_ite`, `prob_bind_split`, `prob_bind_pure`, `bind_pure_left`, `prob_sample`, `mass_sample`, `strengthIn_mono` |
| `Memory/DiscriminationNet` | discrimination nets: `Net`, `select`, `path`, `Recognizes`, `images` | `select_depends_only_on_noticed_features`, `discrimination_needs_a_difference`, `confusion_agrees_on_path` (with each image stored once, a confusion is with a code that agrees on every feature tested) |
| `Memory/Cue` | cue codes and retrieval from partial information: `Cue`, `cueOf`, `cueFor`, `CueSelects` (nondeterministic where the cue is silent), `cueResults` | `cue_from_path_selects`, `restoration` |
| `Memory/Activation` | declarative memory with activation (ACT-R, decay 1 and temperature 1, where all quantities are rational): `Chunk`, `ActState`, `ActParams`, `Act.retrieve` (base level times `μ^mismatches`, with a failure weight), `Act.study`, `actRetriever` | `Act.prob_retrieve`, `Act.retrieve_not_certain`, `actRetriever_stableRetrieval` (vacuous, by `stableRetrieval_of_neverCertain`) |
| `Control/Attention` | noticing orders: `NoticingOrder`, `firstDiff`, `Noticeable`, `diffs`, `scanCost` | `firstDiff_differs`, `scanCost_ge_of_agree` |
| `Control/Serial` | a serial mechanism with unit processing time; anchor-point attention: `learnedOnTrial`, `errorsAt` | `trials_at_least_items`, `anchorAttention_serialPosition`, and the shape of the bow |
| `Process/DiscriminationLearning` | learning in a net: `learn` (one test per confusion), `learnK` (up to *k*, with redundant tests), `learnAll`; `netLearner`; `Clean` (each image stored once and recognized) | `learn_recognizes`, `learn_preserves`, `learnAll_recognizes`, `learned_test_is_first_noticed_difference`, `learn_clean`, `learnAll_clean`; and as phenomena, `netLearner_nonInterference`, `netLearner_reachesCriterion`, `netLearner_generalizes`; as a retriever (`Net.retrieve`, `netRetriever`), `netRetriever_stableRetrieval`, `netRetriever_deterministic`, `net_agreesOn` |
| `Process/Association` | associations by cue codes as the net grows; `netResponder` | `cue_can_fail_after_growth`, `learning_can_capture_old_cue`; as phenomena, `netResponder_oscillation`, `netResponder_retroactiveInterference` |
| `Process/SampledRetrieval` | retrieval by sampling answers in proportion to strength, with a confidence criterion and a search length: `search`, `Retrieval`, `reach`, `reachSuch` | `prob_exhausted` (exhausted with probability `(1-R)^n`), `prob_stated`, `stated_share` (the share of stated answers with a property does not depend on search length), `exhausted_antitone_reach`, `exhausted_antitone_length`, `reach_mul_geom`, `stated_share_shift` and `aboveShare_shift` (shifting strength to an answer never raises the others' share of stated answers, at any criterion) |
| `Process/RecognizeRetrieve` | a composition of two mechanisms, over any problems and answers: recognition by any memory, then associative retrieval on the recognized code's associations (criterion, search length), else a backup: `recognizeRetrieve`, `Route`, `RR.afterRecognition`, events `isBackup`, `isWhole`, `wholeSuch`, `wholeWrong`; `Sharp` | `RR.backup_prob`, `RR.whole_prob` (averages over what the code calls up), `RR.confident_errors` (a problem confused with a familiar one with sharp associations errs on every whole answer, with no more backup use), `RR.same_correct_confusion_harmless`; `RR.confident_errors_of_laws` (the same from laws: determinacy, certainty, stability). Multi-digit addition is an instance (`MultiDigit/AnyMemory.lean`) |
| `Process/Combination` | selective modification of a prototype by one value of one attribute: `modify` | `sim_modify` (modification changes similarity only on the selected attribute) |
| `Phenomena/Combination` | conceptual combination, for any similarity: `ConjunctionEffect`, `ReverseConjunctionEffect`, `thresholdM` (Hampton 2007, Eq. 8), `OverExtends`, `OverExtendsBinary` | `overExtends_of_conjunctionEffect`, `overExtends_binary_of_conjunctionEffect`, `member_mono_of_conjunctionEffect` |
| `Phenomena/Verification` | verifying category statements, for any verifier: `Verifier` (answer and ordinal cost); laws against a hierarchy: `DistanceEffect`, `TypicalityEffect`, `Reversal` | `not_distanceEffect_of_reversal` |
| `Phenomena/Learner` | the interface phenomena are stated about: `IncrementalLearner` (study, recognize) | |
| `Phenomena/Responder` | responding to a cue: `Responder` (possible responses), `ProbResponder` (their probabilities); `RetroactiveInterference`, `Oscillation` | |
| `Phenomena/Retriever` | retrieval, the probabilistic form of recognition: `Retriever` (study, retrieve a distribution of stored stimuli), `IncrementalLearner.toRetriever`; laws `StableRetrieval`, `AgreesOn` | `stableRetrieval_of_nonInterference`, `confusion_preserves_of` |
| `Phenomena/RetrievalLaws` | probabilistic laws of retrieval, theory-neutral: `pRet`, `Reachable`, `Certainty`, `Stability`, `OrderFree`, `Recency`, `StoredOnly`; `Deterministic`, `StableRetrievalOn`, `Determinate` | `studied_selfRetrieval` (certainty + stability: studied items retrieve themselves with probability 1), `retrieve_of_pRet_pos`, `not_determinate_of_two`, `stableRetrievalOn_of_stability` (for a deterministic retriever, stability gives stable retrieval), `stableRetrieval_of_neverCertain` (stable retrieval is vacuous when nothing is certain), `not_recency_of_orderFree` (no memory is both order-free and recent, wherever recency can be tested). Which memory families have which law: `../CogMatrix/` |
| `Phenomena/Learning` | `NonInterference`, `ReachesCriterion`, `StimulusGeneralization` | `criterion_of_nonInterference`: any learner with non-interference reaches criterion, given an invariant under which study succeeds |
| `Phenomena/SerialPosition` | `SerialPositionEffect`, `distFromEnds` | |

The `Phenomena` modules import no mechanism from CogLib (only the representation `Rep/Distribution`): a phenomenon is stated independently of every mechanism. Mechanism modules then prove that a mechanism has a phenomenon (e.g. `netLearner_reachesCriterion`, `anchorAttention_serialPosition`), and theories inherit those proofs by choosing the mechanism.

## Adding to CogLib

- Put a construct here when it is not specific to one theory. Cite the theory it came from in the theory's directory, not here.
- State a phenomenon in `Phenomena/` as a property of an interface (`IncrementalLearner`, `Retriever`, or a new one), never of a mechanism.
- Keep general results general: a theorem about all learners belongs in `Phenomena/`; one about all discrimination nets belongs with the nets.
