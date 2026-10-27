# Laws, families and the theory matrix: a direction for CogLean

## The problem

CogLean aims to be general (`README.md`): one library in which the constructs of cognitive science are defined once and theories are compared on common ground. But there are a great many specific models of memory, learning and choice, and new ones keep appearing:
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

## Where the library stands

The pieces exist at small scale.
- `CogLib/Phenomena/` states phenomena over interfaces:
  - `IncrementalLearner` with `NonInterference` and `ReachesCriterion`;
  - `Responder`;
  - `Retriever` with `StableRetrieval` and `AgreesOn`.
- `CogLib/Process/DiscriminationLearning.lean` proves that discrimination nets have them.
- `CogLib/Memory/Activation.lean` is a first strength-family member: ACT-R retrieval with decay 1 and temperature 1, where all of its quantities are rational.
- `MultiDigit/MultiDigit/AnyMemory.lean` proves the multi-digit predictions for *any* memory, each with the laws it needs. The EPAM versions are corollaries.
- `MultiDigit/MultiDigit/ExampleACTR.lean` shows the two memories diverging on the same problems:
  - graded rather than all-or-none confusion;
  - errors on practiced problems;
  - interference from new practice.

It also shows why point 4 is needed: `StableRetrieval` holds for ACT-R only vacuously, because nothing in ACT-R is retrieved for certain (`OPEN_ISSUES.md` #16).
- `CogMatrix/` is the first matrix: 5 laws (certainty, stability, order-freedom, recency, stored-only retrieval) × 4 families (discrimination, activation, strength, global matching), 20 cells, every one a theorem. Every law is had by some family and lacked by another, and every family has its own row. Global matching was added as a test of the first four laws. It matched strength memory on all of them, which forced the fifth. See `CogMatrix/MATRIX.md`.

## Program

1. **Graded laws for `Retriever`:**
   - frequency monotonicity;
   - recency monotonicity;
   - similarity-graded confusion;
   - graded non-interference;
   - graded feature agreement.

   Restate the existing all-or-none laws as their special cases.
2. **Two full columns.** For each law, a general proof or a counterexample for the discrimination family and for the strength family. General means not just a worked example.
3. **The matrix as an artifact.** A generated table (law × family, with theorem names), and the differential predictions it implies, each with the experiment that would test it.
4. **A third family.** Global matching (MINERVA 2 or REM) tests whether the laws chosen so far are the right ones.
5. **Beyond memory.** The same treatment for strategy choice (a strategy-chooser interface, `OPEN_ISSUES.md` #8) and for production systems.
6. **Reference implementations.** Where a community implementation exists (PyACTUp for ACT-R), check the formalized family against it on shared instances, as `MultiDigit/sim/` does for the blind simulator.

## Risks

- **The laws become the theory.** Choosing them is the scientific work. A badly chosen set makes different theories look alike, or alike theories look different. Point 4 is the safeguard; it is not a guarantee.
- **Abstraction loses quantitative detail.** Laws are qualitative or ordinal. Fits to data still need the concrete models, and the matrix says which fits would be informative.
- **Real-valued families.** Most of these models use `exp` and `log`. They need Mathlib, which is confined to an `ACTR/` package (or a successor), with rational special cases kept in core Lean where they exist.
