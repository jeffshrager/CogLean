# CogLib

The general part of CogLean: constructs of cognitive theory, and phenomena stated without reference to any theory. Theories (EPAM in `../EPAM/`, strategy choice in `../StrategyChoice/`) import CogLib, choose among its constructs, and prove which phenomena they have.

CogLib must never import a theory. It is a separate Lake package so that this is enforced: a theory requires CogLib by path (see `../EPAM/lakefile.toml`), and CogLib requires nothing.

```sh
cd CogLib && lake build      # or build a theory, which builds CogLib first
```

No `sorry`; only Lean's standard axioms. Core Lean only (probabilities are core `Rat`).

## Layers

| Module | Contents | Main results |
|---|---|---|
| `Rep/Features` | feature codes: `Feature`, `Item`, `Item.feat` | |
| `Rep/Distribution` | finite distributions with exact rational probabilities: `Dist`, `pure`, `bind`, `prob`, `Possible`; sampling in proportion to strength: `sample`, `strengthIn`, `total` | `prob_bind_ite`, `prob_bind_split`, `prob_sample`, `mass_sample`, `strengthIn_mono` |
| `Memory/DiscriminationNet` | discrimination nets: `Net`, `select`, `path`, `Recognizes`, `images` | `select_depends_only_on_noticed_features`, `discrimination_needs_a_difference` |
| `Memory/Cue` | cue codes and retrieval from partial information: `Cue`, `cueOf`, `cueFor`, `CueSelects` (nondeterministic where the cue is silent), `cueResults` | `cue_from_path_selects`, `restoration` |
| `Control/Attention` | noticing orders: `NoticingOrder`, `firstDiff`, `Noticeable`, `diffs`, `scanCost` | `firstDiff_differs`, `scanCost_ge_of_agree` |
| `Control/Serial` | a serial mechanism with unit processing time; anchor-point attention: `learnedOnTrial`, `errorsAt` | `trials_at_least_items`, `anchorAttention_serialPosition`, and the shape of the bow |
| `Process/DiscriminationLearning` | learning in a net: `learn` (one test per confusion), `learnK` (up to *k*, with redundant tests), `learnAll`; `netLearner` | `learn_recognizes`, `learn_preserves`, `learnAll_recognizes`, `learned_test_is_first_noticed_difference`; and as phenomena, `netLearner_nonInterference`, `netLearner_reachesCriterion`, `netLearner_generalizes` |
| `Process/Association` | associations by cue codes as the net grows; `netResponder` | `cue_can_fail_after_growth`, `learning_can_capture_old_cue`; as phenomena, `netResponder_oscillation`, `netResponder_retroactiveInterference` |
| `Process/SampledRetrieval` | retrieval by sampling answers in proportion to strength, with a confidence criterion and a search length: `search`, `Retrieval`, `reach`, `reachSuch` | `prob_exhausted` (exhausted with probability `(1-R)^n`), `prob_stated`, `stated_share` (the share of stated answers with a property does not depend on search length), `exhausted_antitone_reach`, `exhausted_antitone_length`, `reach_mul_geom`, `stated_share_shift` and `aboveShare_shift` (shifting strength to an answer never raises the others' share of stated answers, at any criterion) |
| `Phenomena/Learner` | the interface phenomena are stated about: `IncrementalLearner` (study, recognize) | |
| `Phenomena/Responder` | responding to a cue: `Responder` (possible responses), `ProbResponder` (their probabilities); `RetroactiveInterference`, `Oscillation` | |
| `Phenomena/Learning` | `NonInterference`, `ReachesCriterion`, `StimulusGeneralization` | `criterion_of_nonInterference`: any learner with non-interference reaches criterion, given an invariant under which study succeeds |
| `Phenomena/SerialPosition` | `SerialPositionEffect`, `distFromEnds` | |

The `Phenomena` modules import no mechanism from CogLib (only the representation `Rep/Distribution`): a phenomenon is stated independently of every mechanism. Mechanism modules then prove that a mechanism has a phenomenon (e.g. `netLearner_reachesCriterion`, `anchorAttention_serialPosition`), and theories inherit those proofs by choosing the mechanism.

## Adding to CogLib

- Put a construct here when it is not specific to one theory. Cite the theory it came from in the theory's directory, not here.
- State a phenomenon in `Phenomena/` as a property of an interface (`IncrementalLearner`, or a new one), never of a mechanism.
- Keep general results general: a theorem about all learners belongs in `Phenomena/`; one about all discrimination nets belongs with the nets.
