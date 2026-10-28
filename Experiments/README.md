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

## An experiment derived from laws (`Counterbalanced.lean`, `OrderEffect.lean`)

The usual workflow is reversed: start from two laws that disagree and derive the experiment that separates them. Recency and order-freedom disagree. Take two new items `a`, `b` and a probe `x` equally similar to both. Condition AB studies `a` then `b`, condition BA studies `b` then `a` (after the same prior list), and both probe with `x`. The order effect is `Δ = D_AB − D_BA`, where `D = P(retrieve b) − P(retrieve a)`.

- **From laws alone,** for any memory:
  - order-freedom gives `Δ = 0` (`orderFree_delta_zero`);
  - recency gives `Δ > 0` (`recency_delta_pos`);
  - so no memory has both (`orderFree_recency_inconsistent`).
- **From retrieval to report.** Under forced choice (report the retrieved item if it is `a` or `b`, otherwise guess B with probability `γ`), the reported effect is `Δ + (2γ − 1)(o_AB − o_BA)`, where `o` is the chance of retrieving neither (`delta_report`). So:
  - order-freedom predicts a reported effect of 0 for every `γ` (`forcedChoice_orderFree`);
  - recency predicts a positive one only with unbiased guessing, or when "neither" is equally likely in both orders (`forcedChoice_recency`).

  A biased guesser can mask or reverse the recency prediction. The bridge's condition is part of the theorem.

| Memory | Δ, no prior list (000, 110; probe 010) | Δ, prior list [000] (100, 010; probe 110) | Why |
|---|---|---|---|
| Activation (ACT-R) | 10/17 | | recency, so Δ > 0 from laws; reported 10/17 for every `γ` |
| Strength (DOA) | 0 | 0 | order-free, so Δ = 0 from laws |
| Global matching (MINERVA 2) | 0 | 0 | order-free, so Δ = 0 from laws |
| Discrimination (EPAM) | 0 | −2 | neither law: computed |

EPAM's order effects come from the shape of the net, not from time. From an empty net, both orders grow the same test. After 000, whichever item is learned first is discriminated from 000, and the probe then always retrieves it: Δ = −2, the most extreme primacy possible. So the same counterbalanced experiment gives recency (ACT-R), no effect (strength, MINERVA), and primacy (EPAM, with a suitable prior list).

## A second task through the same composition (`FaceNaming.lean`)

The composition extracted from multi-digit addition (`Cog.recognizeRetrieve`: recognize, then retrieve, else back up) is used for a task with no arithmetic. A face is recognized as a familiar person's, that person's name associations are searched, and the backup is "don't know". Ann (000) and Bob (110) are familiar; the stranger Carl (100) is one feature from each.

- **EPAM.** The net recognizes Carl as Bob, and `Cog.RR.confident_errors` gives *confident misnaming*, for every search length (`epam_confident_misnaming`):
  - Bob is never misnamed;
  - every name Carl is given is wrong;
  - Carl says "don't know" exactly as rarely as Bob.

  The theorem is inherited, not reproved.
- **ACT-R.** Misnaming is graded (`act_values`): Carl is named Bob 225/391 of the time and Ann 225/782. He says "don't know" more often than Bob (107/782 vs 229/2254, `act_more_dont_know`), and Bob himself is sometimes called Ann.

| | EPAM | ACT-R |
|---|---|---|
| Carl named Bob | 45/46 | 225/391 |
| Carl named Ann | 0 | 225/782 |
| Carl: "don't know" | 1/46 | 107/782 |
| Bob: "don't know" | 1/46 | 229/2254 |
| Bob named Ann | 0 | 225/2254 |

## Limits, and next

- **Representation artifact.** With `±1` features, a trace opposite to the probe gets activation −1 in MINERVA, enough to drive the echo's intensity negative and make retrieval fail. That is why the study list leaves out 000. Hintzman's features also take the value 0.
- **"Called old" is a crude report rule** (retrieved something studied). A recognition decision on familiarity (MINERVA's intensity, ACT-R's activation) needs a richer interface than `Retriever`.
- **Next:** feedback-driven learning (respond, feedback, update), with exact runs for short sequences, sampled runs for long ones, and statements over all runs. Multi-digit addition is the target (`../notes/OPEN_ISSUES.md` #12).
