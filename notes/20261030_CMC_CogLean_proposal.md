# Proposal: CogLean's mechanisms as fillers of the Common Model's slots

**For discussion with John Laird before any work is done.** Status: proposal only; nothing in the repository has been changed. A port of the CMC files was tested in a scratch copy.

## The idea

The Lean specification of the Common Model of Cognition (`CMC.lean`, the 2017 model; `CMC_Meta.lean`, the metacognition extension) defines what a conforming architecture is.

- An `Arch` structure leaves the mechanisms as parameters: `select`, `retrieve`, `perceive`, `motor`, and the learning functions (`compose`, `rlTune`, `declCreate`, `declTune`, decay, forgetting).
- It states proof obligations every architecture must discharge: results are written only by retrieval, reinforcement learning changes only utility, declarative creation is incremental and bounded, tuning changes only metadata.

CogLean is a library of cognitive mechanisms, laws and theories, each proved from its postulates, including:
- discrimination nets (EPAM);
- distributions of associations (Siegler & Shrager);
- ACT-R's activation memory;
- strength and global-matching memories;
- a decision cycle with impasses and repairs;
- means-ends analysis.

**The proposed relationship: the CMC is *above* CogLean.** CogLean's mechanisms are candidate fillers for the CMC's slots, and each fit is a theorem: the mechanism discharges that slot's obligations. An architecture assembled from conforming fillers then inherits every result the CMC proves, such as seriality, provenance, and the derived prediction that declarative knowledge reaches behaviour only through retrieval.

Three things stay separate:
- the CMC remains John's artifact, unchanged apart from a mechanical port;
- CogLean's general library stays architecture-neutral, and much of CogLean (concept combination, semantic memory, the theory matrix) is not about architectures;
- the connection lives in a bridge package that imports both.

## What has been checked

The two files were written for Lean 4.15; CogLean uses 4.35. In a scratch copy, a mechanical port compiles:
- `meta` is now a keyword, so the `Elem` and `Rule` field `meta` becomes `«meta»`;
- `List.mem_map_of_mem` and `List.mem_cons_self` now take implicit arguments (3 call sites);
- one `simpa [List.map_map] using h` becomes `simp only [List.map_map] at h; exact h`.

No statement changed. All 292 theorems in the two files then check: the 29 and 25 headline results, plus utility lemmas. All use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and none uses `sorry`.

## How CogLean's mechanisms would fill the slots

| CMC slot | CogLean filler | Obligation, and the existing CogLean fact that discharges it |
|---|---|---|
| `retrieve` (declarative) | EPAM discrimination-net retrieval (deterministic) | results only from retrieval (structural) |
| `declCreate` | EPAM learning: one test per confusion, image stored | `declCreate_incremental`, from `learn_preserves`; `declCreate_bounded`, one image and one test per event |
| `declTune` | DOA strengthening (`SC.strengthen`); ACT-R's frequency and recency updates | `declTune_symbolic`: strengths and activation are metadata, so tuning leaves relations unchanged |
| `select` | CogLean's decision cycle (a procedure proposes one operator; impasse at a violated precondition) | `select_respects_results`: operators act on working memory, never on result areas |
| `Meta` extension: selection outcomes (no candidates, tie, conflict, no progress) | CogLean's impasses, with Brown & VanLehn repairs | the outcome is reported in the procedural process area |
| required metadata kinds (utility, frequency, recency) | ACT-R activation: frequency and recency are its base-level terms | — |

## What CogLean would have to change (moving toward the CMC)

1. **A relational vocabulary in CogLib** (moderate). CogLean currently speaks of feature codes, strengths and per-mechanism state records. A thin layer, `Rep/Relational`, would view a mechanism's long-term state as **symbolic relations plus numeric metadata**, which is the CMC's distinction. It would restate in that vocabulary properties CogLib already proves: EPAM's learning keeps every relation and adds a bounded number; DOA's and ACT-R's updates change only metadata. CogLib would still not import the CMC.
2. **States as working memory** (small). CogLean's problem solver is already generic over its state type, so a CMC working memory can be that type.

## The one real mismatch: determinism

The CMC's `select` and `retrieve` are plain functions. Most of CogLean's mechanisms return exact probability distributions: ACT-R retrieval, DOA sampling, strength memory. Exactness is central to CogLean, since every predicted probability is a theorem.

- **Deterministic fillers fit as is:** EPAM nets, and the decision cycle with exact facts.
- **Stochastic architectures (ACT-R) cannot be instances of the CMC as written.**

**Proposal:** a distribution-valued generalization, `CMC/Prob.lean`, as a new file that imports John's and changes nothing in it.
- `select` and `retrieve` return distributions.
- Every deterministic `Arch` embeds, as the certain distribution.
- The 2017 results (seriality, locality, provenance, retrieval-only influence) are re-proved for every possible outcome.

This would let ACT-R-style architectures conform. It is offered back to the CMC group as a proposal, not as a change to the specification.

## Staged plan

1. **`CMC/` package:** John's files ported to 4.35. The originals are kept unchanged alongside, with the port's differences listed.
2. **The relational vocabulary in CogLib,** with the obligation-shaped theorems for EPAM, DOA and activation memory.
3. **`CMCBridge/` package:** EPAM retrieval and learning as the declarative slot; the decision cycle as the selection slot. An assembled toy architecture proved to be an `Arch`, so it inherits the CMC's theorems.
4. **The distribution-valued CMC,** and then ACT-R and DOA as declarative fillers.
5. **A task model on an assembled architecture:** multi-digit addition as rules and knowledge, with a theorem that its answers equal CogLean's existing model (`MD.trial`).

Stages 1–3 are moderate and need no change to the CMC. Stage 4 is substantial but mechanical. Stage 5 is the largest, and the payoff.

## Questions for John

1. **Placement.** Is the CMC as an imported package, with CogLean mechanisms as fillers, the relationship he wants? Should the ported files live in CogLean's repository, or should CogLean depend on a CMC repository of his?
2. **The port.** Would he take the three 4.35 changes upstream, so there is one version?
3. **Probabilistic selection and retrieval.** Is a distribution-valued CMC acceptable as the way stochastic architectures conform? Or would he prefer randomness modelled differently, for example as an explicit noise input?
4. **Decision-cycle mapping.** Does mapping CogLean's impasses (a violated precondition, repaired by heuristics and critics) onto the metacognition extension's selection outcomes read correctly to him? In particular, is repair theory's "local problem solver" an instance of the CMC's "complex behaviour from sequences of cycles", or a departure from it?
5. **EPAM as declarative memory.** A discrimination net is a learned index over stored images. Is it fair to treat its tests as declarative relations (symbolic content) for `declCreate`, or are they closer to procedural knowledge?
6. **Priority.** Which matters more to the CMC group: conformance of existing mechanisms (stages 2–3), the probabilistic generalization (stage 4), or a task model running on an assembled architecture (stage 5)?

## What each side gets

- **The CMC:** concrete, proved instances of its slots drawn from established cognitive theories (EPAM, distributions of associations, ACT-R memory, repair theory). Also a test of the specification against real mechanisms, and a route for stochastic architectures to conform.
- **CogLean:** an architecture-level framework above its mechanisms, so its theories compose into a whole mind under shared, community-agreed commitments. Its task models gain an architecture to run on.
