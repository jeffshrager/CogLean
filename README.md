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

The library is split accordingly. **CogLib** (`CogLib/`) holds the general constructs and the theory-neutral phenomena. Its theorems quantify over *arbitrary* discrimination nets, stimuli, noticing orders, learning histories and, for the phenomena, arbitrary learners. Each **theory** (so far `EPAM/`, `StrategyChoice/`, and `MultiDigit/`, which combines the two) imports CogLib, records which constructs its postulates choose, and proves the phenomena for its learner. For example, "any learner whose learning is non-interfering reaches criterion" is proved once in CogLib. Discrimination nets are proved non-interfering, also in CogLib. EPAM gets learning to criterion in one line, and any later theory with non-interfering learning gets it the same way.

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

**CogLib** (`CogLib/`): feature codes; finite probability distributions (exact rationals); discrimination nets; discrimination learning with a noticing order and redundancy; cue codes and retrieval from partial cues; retrieval by sampling with a confidence criterion and a search length; serial attention with anchor points; and the phenomena of non-interference, learning to criterion, stimulus generalization, oscillation, retroactive interference and the serial position effect, stated theory-neutrally (over learners and responders), with the mechanisms that have them.

**EPAM** (`EPAM/`, 30 theorems), the first theory:

- **Phenomena it proves:**
  - stimulus generalization;
  - the cost of intralist similarity;
  - oscillation (correct responses that fail and recover);
  - retroactive inhibition;
  - non-interference, and learning to criterion;
  - total time growing with the amount to be learned;
  - the serial position effect.
- **An experiment it computes:** serial anticipation of a six-syllable list. The responses the postulates make possible are compared trial by trial with a published simulation (33 or 34 of 34 agree, depending on the stimulus codes), and the result's sensitivity to codes, noticing order and parameters is measured (`notes/EPAM_robustness_RESULTS.md`).

**Strategy choice** (`StrategyChoice/`), the second: the distributions-of-associations model (Siegler & Shrager 1984), in which children's errors, solution times and use of overt strategies on addition problems all depend on the distribution of associations between each problem and its possible answers.

- **Phenomena it proves**, for any associations, confidence criterion and search length:
  - retrieval is used with probability `1 - (1-R)^n`;
  - the error share on retrieval trials is the wrong answers' share of the strength above the criterion, whatever the search length and the backup strategies;
  - the error share on counting trials is the counting process's, whatever the associations (the chapter's "nonintuitive prediction");
  - moving strength to the correct answer never raises the error share on retrieval trials.
- **A limit it finds:** making a distribution more peaked can *raise* overt strategy use, even averaged over the chapter's twelve confidence criteria, so "peaked distributions mean fewer overt strategies" needs a condition the chapter doesn't state.
- **Predictions it computes:** exact overt-use predictions for six problems from the chapter's own associative strengths.
- **The theorems, with complete proofs:** [`notes/StrategyChoice_THEOREMS.md`](notes/StrategyChoice_THEOREMS.md) states every result that holds without reference to specific numerical values, proves each in full, and gives the Lean name of each.

**Multi-digit addition** (`MultiDigit/`), the third, combines the first two. EPAM recognition is joined to DOA retrieval to cover 3-digit addition, where similar problems can be confused. Its predictions are deduced from the postulates for every choice of parameters, not simulated. The central one is that confusion produces *confident errors*: a retrieved wrong answer with no extra backup use. DOA alone cannot produce these, because in DOA errors and backup use come from the same flat distribution. Column work is built from single-digit DOA trials: carrying adds no error, so a column error is a single-digit error moved to its place. Learning removes a confusion without disturbing anything else, and the problem is then worked out by the columns until its own associations are strengthened. The predictions, with proofs, are in [`notes/MultiDigit_PREDICTIONS.md`](notes/MultiDigit_PREDICTIONS.md).

**Conceptual combination** (`Concepts/`), the fourth: the selective modification model (Smith, Osherson, Rips & Keane 1988), with graded membership by Hampton's (2007) threshold model. It proves the conjunction effect, its reverse and over-extension for every prototype and parameter choice under stated conditions, and reproduces the paper's figures exactly. With number concepts learned from exemplars, its over-extensions are shown to be false, not only incoherent: 14 is judged an *even multiple of 3* far more than a *multiple of 3* ([`Concepts/README.md`](Concepts/README.md)).

**Semantic memory** (`SemanticMemory/`), the fifth: Collins & Quillian's (1969) hierarchical network and Smith, Shoben & Rips's (1974) feature comparison model, on CogLib's semantic nets. The hierarchical model has the distance effect for every net and can never produce a typicality effect or a reversal ("a chicken is an animal" faster than "a chicken is a bird"); the feature model produces both, and so lacks the distance effect ([`SemanticMemory/README.md`](SemanticMemory/README.md)).

**View application** (`ViewApplication/`): Shrager's (1987) view application as one generic process on CogLib's knowledge nets (semantic nets over terms). It reproduces the paper's Table 4 exactly, and, given number concepts and an ARITHMETIC view, removes over-extension (membership in *even multiple of 3* becomes exactly divisibility by 6, for every number) while leaving typicality unchanged: typicality and membership dissociate ([`ViewApplication/README.md`](ViewApplication/README.md)).

**Problem solving** (CogLib `Process/ProblemSolving`, `MultiDigit/Solver.lean`): problem spaces under means-ends analysis (GPS) and a decision cycle with impasses and repairs (repair theory; Soar). Multi-digit addition's column backup becomes problem solving, proved to answer exactly as before (`bridge`); deleting the carry rule yields impasses whose repairs are the classic addition bugs, one bug per repair; and GPS works units-first though its goal names no order.

**Memory as a parameter.** CogLib's `Retriever` interface lets a theory leave its memory open. Discrimination nets and ACT-R's declarative memory (decay 1 and temperature 1, where it is exactly rational) are two instances. The multi-digit model is stated for any memory, and run with both.

**The theory matrix** (`CogMatrix/`): 6 laws of retrieval × 4 families of memory (discrimination, activation, strength, global matching), each cell a theorem: the family has the law at every parameter setting, never has it, or lacks it at one setting (a counterexample). Every law separates some families, and every family has its own row ([`notes/MATRIX.md`](notes/MATRIX.md)). This is the direction for the library as a whole ([`notes/PROSPECTUS.md`](notes/PROSPECTUS.md)).

**Experiments** (`Experiments/`): an experiment is written once against the memory interface, and any family plugs in. The first one, a study-test experiment with a prototype lure, is run with all four families. Its serial-position curves and lure responses differ as the families' laws predict, and every number is a theorem ([`Experiments/README.md`](Experiments/README.md)).

No `sorry` anywhere; only Lean's standard axioms.

## Roadmap

The direction for making the library general, as a hierarchy of laws, model families as instances, and a theory-by-law matrix, is set out in [`notes/PROSPECTUS.md`](notes/PROSPECTUS.md). Its first matrix (5 laws × 4 memory families, every cell a theorem) is in [`CogMatrix/`](CogMatrix/README.md).

1. **Library structure.** Done in outline: `CogLib/` with `Rep`, `Memory`, `Control`, `Process` and `Phenomena` layers, imported by `EPAM/` and `StrategyChoice/`. Still to do:
   - experiments as their own layer (`Experiments/SerialAnticipation`), lifted from EPAM's Fig. 4.1 machinery.
2. **Finish EPAM:**
   - paired associates;
   - response generalization;
   - the distribution of error types;
   - cue codes sized by trial and error;
   - immediate memory.
3. **Finish strategy choice:** the learning simulation (A6 is stated), the full 25-problem matrix, and a condition under which peaking does reduce overt strategy use.
4. **Multi-digit addition:** learning sequences over many trials (discrimination and strengthening together); errors in carrying.
5. **The matrix** (`notes/PROSPECTUS.md`, Program): more families as tests of the laws; parameter regions of the "lacks" cells; sharper laws; theories' predictions read off the matrix; strategy choice and production systems as further interfaces.
   - **ACT-R as a rival theory of the same data.** ACT-R's tutorial fits the same children's answers by partial matching. Its memory is already a matrix family (the rational case). ACT-R for strategy choice, and with general parameters (Mathlib, in its own package), are still to do.
6. **Other theories:** a bounded-memory account of sentence production (Yngve's depth hypothesis); a production-system theory; strategy discovery (SCADS, Shrager & Siegler 1998).
7. **Comparisons:** for each phenomenon, which theories have it, under what conditions, and through which shared lemmas. This is what the matrix generalizes.

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
cd EPAM && lake build              # builds CogLib, then EPAM
cd StrategyChoice && lake build    # builds CogLib, then the strategy-choice model
cd MultiDigit && lake build        # builds CogLib, then the combined multi-digit model
cd Concepts && lake build          # builds CogLib, then conceptual combination
cd SemanticMemory && lake build    # builds CogLib, then semantic memory
cd ViewApplication && lake build   # builds CogLib and Concepts, then view application
```
