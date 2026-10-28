# Experiments: written once, run with any memory

The experiment layer (`../notes/OPEN_ISSUES.md` #2), begun with the simplest case. An experiment is written against CogLib's `Retriever` interface, and any memory family plugs in: discrimination (EPAM), activation (ACT-R), strength (DOA) or global matching (MINERVA 2). Properties of an experiment can be proved from the laws of `../CogMatrix/`, and then hold for every family with those laws.

```sh
cd Experiments && lake build    # builds CogLib and CogMatrix too; core Lean only
```

- `Experiments/StudyTest.lean`: the layer.
  - A study-test experiment: a study list, studied once each in order with no feedback, then probes; testing doesn't change memory.
  - Measures: accuracy by serial position (`curve`), the chance a probe retrieves some studied item (`claimsOld`), and the chance a probe retrieves itself (`retrievesItself`).
  - `curve_flat`: any memory with certainty and stability gives a flat serial-position curve at 1.
- `Experiments/PrototypeDemo.lean`: one experiment, four memories. Study 110, 101 and 011. Test each, then the lure 111 (their prototype, never studied) and the lure 000 (unlike all three).

| Memory | Serial-position curve | 111 called old | 111 retrieves itself | 000 called old |
|---|---|---|---|---|
| Discrimination (EPAM) | 1, 1, 1 | 1 | 0 | 1 |
| Activation (ACT-R) | 40/97, 15/28, 120/157 | 55/61 | 0 | 55/67 |
| Strength (DOA) | 8/17, 8/17, 8/17 | 1 | 0 | 1 |
| Global matching (MINERVA 2) | 1, 1, 1 | 0 | 1 | 0 |

Every number is a theorem, but of two different kinds, which should not be conflated:
- **Derived from laws.** EPAM's flat curve follows from certainty and stability alone (`epam_curve_flat`, by `curve_flat`). It holds for any memory with those laws.
- **Computed from a mechanism.** Every other entry is computed exactly from the family's full definition and these parameters (`decide +kernel`). The laws do not predict it:
  - ACT-R's curve rises here, but the recency law concerns a probe equally similar to two items, not self-retrieval. It does not imply a rising curve.
  - Strength memory's curve is flat here because the three items are symmetric. Order-freedom as stated (swapping the last two study events) does not imply that position can't matter.
  - MINERVA's return of the prototype is a witness that it lacks stored-only retrieval. Its perfect curve shows that lacking certainty in general doesn't mean failing it here.

"Called old" is a report, and stored-only is about what memory returns. EPAM and strength memory satisfy stored-only and still call the prototype old with probability 1, because they return a studied item. MINERVA returns the prototype itself and so, by this crude rule, does not call it old. Connecting reports to retrievals needs an explicit decision model.

## Limits, and next

- **Representation artifact.** With `±1` features, a trace opposite to the probe gets activation −1 in MINERVA, enough to drive the echo's intensity negative and make retrieval fail. That is why the study list leaves out 000. Hintzman's features also take the value 0.
- **"Called old" is a crude report rule** (retrieved something studied). A recognition decision on familiarity (MINERVA's intensity, ACT-R's activation) needs a richer interface than `Retriever`.
- **Next:** feedback-driven learning (respond, feedback, update), with exact runs for short sequences, sampled runs for long ones, and statements over all runs. Multi-digit addition is the target (`../notes/OPEN_ISSUES.md` #12).
