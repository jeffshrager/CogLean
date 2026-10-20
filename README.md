# CogLean: a library of cognitive theory in Lean

## The goal

Mathlib is a single, shared, machine-checked library of mathematics. Definitions are made once and reused everywhere, and every theorem is proved from them. CogLean aims at the same thing for **cognitive theory**: one library in which the constructs of cognitive science are defined once, the theories built from them are stated precisely, and the phenomena those theories claim to explain are proved from their assumptions.

- **Constructs:** representations, memories, learning and selection processes, attention, architectures.
- **Theories:** discrimination-net learning, production systems, search, activation-based memory, connectionist and Bayesian models, and others.
- **Phenomena:** generalization, interference, forgetting, the serial position effect, capacity limits, practice effects, and others.

Cognitive theories are usually stated in prose, in simulation code, or as systems of equations fitted to data. What follows from their core assumptions, as distinct from their parameter settings or implementation details, is rarely checked. In CogLean that is what a proof does. A proof shows *which* assumptions a phenomenon depends on. A failed proof shows that a theory needs an assumption it never stated. And because the constructs are shared, theories can be compared on common ground: two theories explain a phenomenon *in the same way* if their proofs use the same lemmas.

## Why do it this way

### Three kinds of evidence a theory can give

Most modelling evidence in psychology is of the first kind below. CogLean is built around the third, and keeps the other two in the same language.

| Kind of evidence | What it shows | In CogLean's EPAM |
|---|---|---|
| **One run** of one model, with one set of parameters and stimuli | the theory *can* produce a behavior | `Fig41.lean`: one simulated experiment, compared response by response with a published one, computed by the Lean kernel (`decide`) |
| **Every run** of one model (exhaustive search, model checking, or sampling) | the behavior holds for *that* model in all its executions, or how often | `analysis/robustness.py`: the same experiment over thousands of stimulus codes, attention orders and parameters |
| **Every model satisfying the postulates** | the postulates *entail* the behavior, under stated conditions | `learning_to_criterion`, `stimulus_generalization`, `oscillation`, `serial_position_effect`, ... |

A model fitted to a point experiment shows that the theory, as implemented and parameterized, is *consistent* with that result. It doesn't show which assumptions produced it. It doesn't show whether the result survives a change of parameters, or whether a rival theory would produce it just as well. A theorem quantified over every model that satisfies the postulates answers all three, for the phenomena it covers:

- **Which assumptions matter.** A proof uses some postulates and not others, and its hypotheses spell out the conditions it needs. EPAM's learning-to-criterion theorem, for example, holds only for items that differ on features the learner actually attends to. That is a substantive claim about learnability, and nothing in a single simulation run would have surfaced it. A failed proof is informative as well: it shows that a theory needs an assumption it never stated.
- **What is robust and what is accidental.** The robustness analysis of EPAM found that its published phenomena survive changes to the arbitrary stimulus codes, but particular errors do not. It also found that one kind of oscillation needs the redundancy postulate. So did a phenomenon come from the theory, or from a choice made when implementing it? That becomes a question with an answer.
- **Possibility versus necessity.** "Can produce" and "must produce" are different claims, and both differ from "produces at the rate people do". Stating each theorem precisely forces the choice. Some EPAM results (oscillation, retroactive inhibition) say a behavior is *possible*. Others (learning to criterion, the serial position effect) say it is *necessary*. Frequencies are left for later.

The tradeoff is abstraction. Proving things in general means stating theories at the level of their postulates, and that can lose the quantitative detail that matters when fitting data. CogLean treats the kinds of evidence as complementary:

- simulation explores and suggests conjectures;
- proof settles which conjectures follow from which assumptions;
- experiments with people decide whether the assumptions are right.

### Why Lean

Lean is both a programming language and a proof assistant. The same definition of, say, a discrimination net can be *run* on an experiment's stimuli and *proved about* for all stimuli. The simulation and the theory therefore can't drift apart, as they can when a theory is stated in prose and implemented separately in code. Lean also brings:

- **Machine-checked proofs.** Every step is checked by a small trusted kernel. A proof can't silently depend on a mistake, and `#print axioms` shows exactly what each theorem rests on.
- **Unbounded generality.** A theorem can quantify over all nets, all lists, all noticing orders. Model checkers explore a finite (or finitely abstracted) state space, and logic programs derive what follows from the facts and rules they are given.
- **A cumulative library.** Mathlib shows that a community can build one consistent body of definitions and theorems that later work imports rather than re-derives. Cognitive science has nothing like it. Shared definitions are what make theories comparable. If two theories prove the same phenomenon through the same lemma, they explain it the same way. If one can prove a phenomenon the other provably lacks, that's a test that discriminates between them.

The guarantee is relative. Lean checks that a theorem follows from the definitions. It does not check that the definitions capture the theory faithfully, still less that the theory is true of people. That is why each theory's postulates are cited to their source, with its simplifications listed, and why concrete experiments are computed and compared with published results.

### General results, specific theories

The theorems about EPAM are already general in one sense. They quantify over *arbitrary* discrimination nets, stimuli, noticing orders and learning histories, not just the experiments in the paper. What is not yet general is the *code's organization*: the general mechanisms (discrimination nets, cue-based retrieval, attention schedules) are still defined inside the EPAM theory, next to EPAM-specific material. Lean doesn't require that. Definitions, executable models and proofs can live in separate modules. It is simply where the first theory started. Factoring the general mechanisms out into theory-neutral modules is the first item on the roadmap.

## What goes in the library

| Layer | Contents | Examples |
|---|---|---|
| **Representations** | the stuff of cognition | feature codes, symbols and list structures, chunks, propositions, vectors |
| **Memory structures** | how it is stored and accessed | discrimination nets, associative cue-response links, bounded short-term stores, activation, schemas |
| **Processes** | what operates on memory | selection and recognition, discrimination learning, association, retrieval with partial cues, search, rule matching |
| **Control** | how processing is organized | serial mechanisms, attention and its order, time per operation, goal stacks |
| **Phenomena** | theory-neutral statements of what is observed | "a stimulus similar to a learned one evokes its response", "responses learned earlier can be lost by later learning", "errors are bowed over serial position" |
| **Theories** | named bundles of the above, with their postulates | EPAM, and in time production-system, activation-based, connectionist and probabilistic theories |
| **Experiments** | tasks as instances | serial anticipation, paired associates, recognition, list learning, with concrete stimuli |

A *phenomenon* is stated once, independently of any theory, as a property a learner can have. A *theory* then proves that its learners have it, possibly only under stated conditions. A *theory* may also fail to have it, and that failure is itself a theorem.

## Principles

- **Define once, reuse everywhere.** A discrimination net, a cue, a bounded store or an attention schedule is defined in one place and imported by every theory that uses it.
- **Theory-neutral phenomena.** Phenomena are stated without reference to any mechanism, so that different theories can be proved to have, or lack, the same phenomenon.
- **Qualitative first.** Most cognitive claims are qualitative ("can occur", "increases with", "is bowed"), and theorems are stated at that level. Quantitative claims can come later, as refinements.
- **Possibility and necessity.** Stochastic mechanisms are stated relationally: what *can* happen, and what *must*. Probability can be added on top.
- **Assumptions are explicit.** Each theory's postulates are definitions or hypotheses, cited to their source where there is one, with simplifications listed. Robustness to the arbitrary choices (codes, orders, parameters) is itself tested, by proof or, where the space is too large, by sampling with the cases that matter certified.
- **Fully checked.** No `sorry`; `#print axioms` shows only Lean's standard axioms. Core Lean where possible, so the library stays light and builds in seconds.
- **Instances keep the theory honest.** Concrete experiments are computed by the kernel (`decide`) and compared with observed or reported behavior.

## Where it stands

The first theory in the library is **EPAM** (`EPAM/`), 48 theorems, no `sorry`:

- **Constructs it defines:**
  - feature codes;
  - discrimination nets with selection;
  - discrimination learning with a noticing order and redundancy;
  - cue codes and retrieval from partial cues with random branching;
  - restoration of cues;
  - serial attention with anchor points;
  - learner state and learning events for an experiment.
- **Phenomena it proves:**
  - stimulus generalization;
  - the cost of intralist similarity;
  - oscillation (correct responses that fail and recover);
  - retroactive inhibition;
  - learning to criterion without unlearning;
  - total time growing with the amount to be learned;
  - the serial position effect.
- **An experiment it computes:** serial anticipation of a six-syllable list. The responses the postulates make possible are compared trial by trial with a published simulation (33 or 34 of 34 agree, depending on the stimulus codes), and the result's sensitivity to codes, noticing order and parameters is measured (`EPAM/analysis/RESULTS.md`).

At present these constructs live inside the EPAM theory. The next step for the library is to lift the general ones out into shared modules.

## Roadmap

1. **Library structure.** Move the general constructs out of `EPAM/` into theory-neutral modules. Each phenomenon becomes a predicate on learners, and EPAM proves it about its learner. Proposed layout:
   - `Cog/Rep` (codes and features)
   - `Cog/Memory/DiscriminationNet`
   - `Cog/Memory/Cue`
   - `Cog/Control/Attention`
   - `Cog/Phenomena`
   - `Cog/Theories/EPAM`
   - `Cog/Experiments/SerialAnticipation`
2. **Finish EPAM:**
   - paired associates;
   - response generalization;
   - the distribution of error types;
   - cue codes sized by trial and error;
   - immediate memory.
3. **A second, different theory, to test that the constructs really are shared.** Candidates:
   - a bounded-memory account of sentence production (Yngve's depth hypothesis);
   - a production-system theory;
   - an activation-based retrieval theory, above all **ACT-R** (the main next target; its real-valued activation will likely bring in Mathlib).
4. **Comparisons:** for each phenomenon, which theories have it, under what conditions, and through which shared lemmas.

## Related approaches

Formal methods have been applied to psychological theories before. What CogLean adds is the combination: a general-purpose proof assistant, theorems quantified over whole classes of models, phenomena as the targets of proof, and a single cumulative library in which theories share definitions.

| Approach | Formalism | What is established | Relation to CogLean |
|---|---|---|---|
| **Theory representation by logic programming** [1] | first-order logic programs (Prolog) | conclusions entailed by a verbal theory's premises, with the derivations that explain them | the closest in aim: deriving what a psychological theory entails, and why. CogLean adds machine-checked proofs over unbounded classes of models, and a shared library |
| **Automata-based formalization of verbal theories** [2] | communicating automata, built up by stepwise refinement | a precise, analyzable model of a theory stated in words (Lazarus and Folkman's theory of stress) | the same starting point (a theory in prose), with a finite-state formalism rather than a proof assistant |
| **Formal semantics of ACT-R** [3, 4] | operational semantics, Constraint Handling Rules | a translation that preserves the architecture's semantics, and a decidable test of whether a model's result is independent of rule order (confluence) | general theorems about an *architecture*, not about psychological phenomena. A foundation CogLean's ACT-R theory could build on |
| **Model checking ACT-R models** [5] | timed automata | properties of every execution of a particular model (e.g. finding defects automatically) | the "every run of one model" kind of evidence above |
| **Verification within a common model of cognition** [6, 7] | state machines checked with nuXmv | correctness and termination of small ACT-R and Soar models, translated into one representation | a common representation across architectures, one of CogLean's aims as well, used here to verify models rather than to derive phenomena |
| **Executable cognitive models** (ACT-R, Soar, EPAM) | simulation programs | that a model, with fitted parameters, reproduces observed data | CogLean keeps this, as computed experiments, and proves what the postulates entail beyond any one run |

The Common Model of Cognition [6] is the nearest relative at the scale of the whole enterprise. It looks for the architectural commitments that many theories share. CogLean pursues the same convergence at the level of *definitions and theorems*: a shared commitment is a shared module, and a shared explanation is a shared lemma.

CogLean's EPAM theory was developed alongside [ExecutableArchaeology](https://github.com/jeffshrager/ExecutableArchaeology), which reconstructs and runs the original IPL-V programs (EPAM II among them). The two projects are independent: CogLean states theories, not programs.

### References

1. Rohner, J.-C., & Kjellerstrand, H. (2021). Using logic programming for theory representation and scientific inference. *New Ideas in Psychology*, 61, 100838. https://doi.org/10.1016/j.newideapsych.2020.100838
2. Finkel, A., Fougea, G., & Le Roux, S. (2025). An automata-based method to formalize psychological theories: The case study of Lazarus and Folkman's stress theory. *MODELSWARD 2025*. https://arxiv.org/abs/2501.05185
3. Gall, D., & Frühwirth, T. (2017). An operational semantics for the cognitive architecture ACT-R and its translation to Constraint Handling Rules. arXiv:1702.01606. https://arxiv.org/abs/1702.01606
4. Gall, D., & Frühwirth, T. (2017). A decidable confluence test for cognitive models in ACT-R. arXiv:1705.08392. https://arxiv.org/abs/1705.08392
5. Langenfeld, V., Westphal, B., & Podelski, A. (2019). On formal verification of ACT-R architectures and models. *Proceedings of the 41st Annual Conference of the Cognitive Science Society*. https://escholarship.org/uc/item/1190b539
6. Laird, J. E., Lebiere, C., & Rosenbloom, P. S. (2017). A standard model of the mind: Toward a common computational framework across artificial intelligence, cognitive science, neuroscience, and robotics. *AI Magazine*, 38(4), 13-26. https://doi.org/10.1609/aimag.v38i4.2744
7. Ganeriwala, P., Matsumuro, M., Ritter, F. E., & Bhattacharyya, S. (2025). Enabling formal verification in a common model of cognition. *SBP-BRiMS 2025*. https://sbp-brims.org/2025/papers/working-papers/2025_SBP-BRiMS_paper_18.pdf

## Getting started

```sh
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh   # installs ~/.elan
cd EPAM && lake build
```
