# Laws, families and the theory matrix: a direction for CogLean

## The problem

CogLean aims to be general (`../README.md`): one library in which the constructs of cognitive science are defined once and theories are compared on common ground. But there are a great many specific models of memory, learning and choice, and new ones keep appearing:
- discrimination nets (EPAM, CHREST);
- ACT-R's declarative memory;
- SAM, REM, MINERVA 2 and TODAM;
- the distributions-of-associations model;
- connectionist networks.

Formalizing them one at a time, each behind an adapter, does not scale. And a library of formalized models, however large, still doesn't say what any two of them disagree about.

## The proposal

Organize the general part of CogLean the way Mathlib organizes algebra. Mathlib doesn't formalize every group. It defines a hierarchy of laws (monoid, group, ring) and proves theorems once per law. A particular structure declares which laws it satisfies and inherits the theorems.

### 1. A hierarchy of cognitive laws
A *law* is a small, theory-neutral property of an interface, such as a learner or a retriever. Examples:
- learning is local;
- retrieval can fail;
- retrieval probability rises with frequency, and with recency;
- confusion falls off with similarity;
- a confusion preserves the features that were tested.

Laws are stated in `CogLib/Phenomena/` and name no mechanism. **Predictions are proved from laws, not from models.** A prediction then reads "any memory with local learning predicts no interference with practiced items", not "EPAM predicts …". Its hypotheses say exactly which laws it rests on.

### 2. Model families as instances
Models are many, but mechanisms are few:
- **Discrimination:** a net of feature tests (EPAM and its descendants).
- **Strength or activation:** associations whose strength rises with use and decays (ACT-R's declarative memory, the distributions-of-associations model, SAM).
- **Global matching:** the response depends on summed similarity to all stored traces (MINERVA 2, REM, TODAM, ACT-R blending).
- **Distributed:** connectionist networks.

Each family is formalized once, with its parameters free. For each law, the family gets either a proof that it has the law, with any conditions on the parameters, or a counterexample. A particular published model is a choice of parameters within its family.

### 3. The theory matrix
The rows are families and the columns are laws. Each cell holds a theorem: the family has the law, or it lacks it. **Differential predictions are read off the matrix.** Where two families differ on a law, every prediction resting on that law separates them, and the experiment that tests the prediction tests the law. The comparison document is generated from the matrix, not written by hand.

### 4. Every law must discriminate
A law enters the library only with a *witness on each side*: a family that has it and a family that lacks it. A law that every family satisfies, or satisfies only vacuously, tells theories apart only by accident.
- In practice this favours **graded** laws ("studying `z` never changes the probability of retrieving `y`") over all-or-none ones ("a studied item is retrieved for certain").
- An all-or-none law is vacuous for any family in which nothing is ever certain.

### 5. Relations between families
Some families are limiting cases of others. With no noise and an unbounded mismatch penalty, activation-based retrieval becomes exact-match retrieval of stored items. A theorem relating two families transfers laws between them without re-proving. The matrix then has structure: implications between laws, and refinements between families.

## What is true here

In mathematics, once something is proved it is true, and the library builds on it. Cognitive science has no such body of accepted truths: there are competing theories, and none is settled. So what can a library of cognitive theory build on?

**On conditional results, which are permanent.** "Family F has law L", "law L entails prediction P", and "with these parameters EPAM answers 200 with probability 45/46" are mathematical facts. They stay true whichever theory of memory turns out to be right, even if every family in the library is refuted. Mathlib is in this position more often than it looks. It doesn't assert that space is Euclidean. It proves facts about Euclidean and non-Euclidean geometry side by side, and leaves to physics the question of which one physical space satisfies.

That is why the library is built on laws rather than theories. A theory is a large, contested bundle of commitments. A law is small enough to be tested on its own. Three kinds of claim are kept apart:

| Claim | Example | Status |
|---|---|---|
| A law entails a prediction | stability ⇒ practiced problems stay practiced | proved, permanent |
| A family has or lacks a law | discrimination nets have stability | proved, permanent |
| People have or lack a law | people lack stability in recall (retroactive interference) | empirical, revisable, judged law by law |

Which theory is right is not a claim the library makes. It follows from the second and third rows together. **A refutation spreads.** If people lack a law, every family that has it is refuted at once, and every prediction proved from it loses its support, in every theory that uses it. Without formalization, a refuted assumption lingers in theories that never said they depended on it.

The matrix carries the third row, as a judgment kept apart from the theorems (`CogMatrix/evidence.json`, shown in `notes/MATRIX.md`). Each judgment rests on a **bridge**: an assumption connecting what an experiment measures (reports and decisions) to what a law is about (what memory retrieves). The bridges are not yet formalized, and they matter:
- People show recency in free recall, and only activation has the recency law. The bridge is that free recall reflects probe-based retrieval.
- People endorse a category prototype they never saw (Posner & Keele 1968). This does not show they *retrieved* the prototype: a memory that returns a similar studied item, as discrimination and strength memory do, also calls the prototype old. False recall of an unpresented word (Roediger & McDermott 1995) is stronger, but it could be built by a response stage working on stored material. So stored-only retrieval is judged mixed.

With the judgments as they stand, activation fits every law on which the evidence is settled. The law that would decide between it and global matching is stored-only retrieval, and its bridge is the one that is missing. The next step is not more data but **observational semantics**: decision and report components, so that a law about retrieval yields a prediction about what participants say (Program 4).

**Where this is weaker than mathematics.**
- **The definitions are contestable.** A family is one formalization of a theory. If it misrepresents the theory, its cells say nothing about the theory itself. Blind simulations and checks against community implementations (`MultiDigit/sim/`, PyACTUp) test that link. A change of definition means the results that depend on it must be proved again.
- **The laws are idealizations, and they presuppose a representation.** They are neutral about mechanism but not about representation: items are binary codes, similarity is a count of mismatching features. Mapping an experiment onto a law is a judgment that passes through a bridge (above). A law may hold in some tasks and not others: stability fails in recall but may hold in recognition, and recency holds only on an immediate test. Each law is therefore stated relative to a setting, and part of the empirical work is finding which settings matter.
- **Families are flexible.** A family may have a law in one region of its parameters and lack it in another. Then the informative, permanent fact is the region, "activation has certainty only when the failure weight is 0", not a single counterexample.
- **Evidence is never final.** The third row will change. The first two won't, and when the third changes, the matrix says at once what follows.

## Where the library stands

**The matrix exists at small scale** (`CogMatrix/`, generated table in `notes/MATRIX.md`): 5 laws × 4 families, 20 cells, every one a theorem.

| Family | Certainty | Stability | Order-freedom | Recency | Stored-only |
|---|---|---|---|---|---|
| Discrimination (EPAM) | has | has | lacks | lacks | has |
| Activation (ACT-R, decay 1, temperature 1) | lacks | lacks | lacks | has | has |
| Strength with a criterion (DOA) | lacks | lacks | has | lacks | has |
| Global matching (MINERVA 2) | lacks | lacks | has | lacks | lacks |

- The laws are in CogLib (`Phenomena/RetrievalLaws.lean`), stated over its `Retriever` interface (study a stimulus; retrieve, for a probe, a distribution over stored stimuli). Each is relative to a starting state and a set of stimuli. The older all-or-none `StableRetrieval` is related to them by theorem: stability gives it for deterministic memories, and it holds vacuously for memories in which nothing is certain.
- Every **has** cell is a general proof for every parameter choice meeting its stated conditions. Every **lacks** cell is a counterexample.
- Every law is had by some family and lacked by another, and every family has its own row. The generator checks both.

**Point 4 has already done work twice.**
- In the multi-digit model, the all-or-none law `StableRetrieval` turned out to hold for ACT-R only vacuously, because nothing in ACT-R is retrieved for certain. That is why the matrix's laws are probabilistic.
- Global matching was added as a test of the first four laws, chosen with the other three families in view. It matched strength memory on all four. The fifth law, stored-only retrieval, separates them, and it names what is distinctive about global matching: its output is a blend, which can be a prototype never studied.

**A composition is reusable.** `CogLib/Process/RecognizeRetrieve.lean` is the composition of recognition (any memory) with associative retrieval and a backup, over any problems and answers. Its theorems, among them `confident_errors`, are proved once there. Multi-digit addition is an instance and inherits them, and so is a task with no arithmetic: naming familiar people (`Experiments/FaceNaming.lean`), where the inherited theorem is confident misnaming of a stranger.

**A theory uses the laws.** `MultiDigit/` states its recognition step for any memory (`trialWith`, `AnyMemory.lean`), proving each prediction from the laws it needs. EPAM's versions follow as corollaries. `ExampleACTR.lean` runs the same problems with ACT-R's memory. There confusion is graded, practiced problems err, and new practice interferes, where EPAM predicts none of these. The multi-digit laws (`StableRetrieval`, `AgreesOn`) are not yet the matrix's laws.

## Program

1. **More families, as tests of the laws.** Each new family should either fit the existing laws or force a new one, as global matching did. Candidates:
   - REM (likelihood-based global matching);
   - a distributed or connectionist memory;
   - CHREST (discrimination with chunking).
2. **Map the "lacks" cells.** Each is one counterexample. Find the parameter regions where the family does have the law. For example, strength memory with no generalization may have certainty.
3. **Sharpen the laws.**
   - Certainty and stability have the same row: separate them or merge them.
   - Add the graded laws not yet stated: frequency monotonicity, similarity-graded confusion.
   - Add implications between laws. Some laws may entail others (does certainty plus stability imply stored-only retrieval?).
4. **Connect theories and experiments to the matrix.** First law-derived experiment done: `Experiments/Counterbalanced.lean` proves that order-freedom gives no order effect and recency a positive one, and, through a forced-choice response model, when the reported effect keeps that sign (unbiased guessing, or equal chances of retrieving neither item). Still to do:
   - Restate the multi-digit laws as matrix laws, so that a theory's differential predictions are read off the matrix.
   - Add decision and report components, so that laws about retrieval yield predictions about observable responses. Then derive experiments from incompatible laws. For example, recency and order-freedom are jointly inconsistent wherever recency's conditions can be met, and a counterbalanced AB/BA study list with a probe equally similar to A and B separates them (`notes/20261027_CogLean_Direction.md`, §4).
5. **Beyond memory.** The same treatment for strategy choice (a strategy-chooser interface, `OPEN_ISSUES.md` #8), then production systems. The Common Model of Cognition's modules are a checklist of which interfaces are needed.
6. **General parameters and reference implementations.**
   - ACT-R with arbitrary decay and temperature needs real exponentials, so it goes in a Mathlib package; the rational case stays in core.
   - Check formalized families against community implementations (PyACTUp for ACT-R) on shared instances, as `MultiDigit/sim/` does.

## Risks

- **The laws become the theory.** Choosing them is the scientific work. A badly chosen set makes different theories look alike, or alike theories look different. Point 4 is the safeguard; it is not a guarantee.
- **Abstraction loses quantitative detail.** Laws are qualitative or ordinal. Fits to data still need the concrete models, and the matrix says which fits would be informative.
- **Real-valued families.** Most of these models use `exp` and `log`. They need Mathlib, which is confined to an `ACTR/` package (or a successor), with rational special cases kept in core Lean where they exist.
