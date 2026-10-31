# Drafting Instructions: CogLean Paper

## Objective

Write a publication-quality paper for a cognitive science audience introducing **CogLean: a shared, mechanically checked library of cognitive theory, modeled on Mathlib**.

The paper should present CogLean as a new approach to *doing theoretical cognitive science*, not as a new theory of cognition.

**Central thesis:** Existing cognitive theories can be expressed using shared formal constructs, their consequences can be proved, and independently developed mechanisms can be composed to derive new results. This makes cognitive theories reusable, comparable, and mathematically extensible in ways that conventional computational modeling generally does not support.

The central demonstration is the composition of EPAM's discrimination-net memory and Siegler and Shrager's distributions-of-associations (DOA) strategy-choice theory into a model of multi-digit addition.

**We are emphatically NOT proposing a new theory of children's arithmetic.** Multi-digit addition is a familiar, reasonably complex cognitive task that demonstrates the methodology.

The intended audience is cognitive scientists familiar with computational modeling. Assume basic familiarity with formal methods and theorem proving; explain the relevant concepts but do not spend substantial space teaching Lean.

Target approximately 5,000–7,000 words initially. Prioritize clarity, technical precision, and scientific significance over comprehensiveness.

## 1. The Intellectual Contribution

Organize the argument around three increasingly important capabilities.

### A. Formalization

Represent existing cognitive theories as precise definitions, postulates, and theorems.

Distinguish:

- Cognitive mechanisms and their postulates.
- Theory-neutral definitions of cognitive phenomena.
- Theorems establishing that mechanisms produce those phenomena.
- Assumptions and conditions under which the theorems hold.

Lean verifies that conclusions follow from formal premises. It does not establish that those premises accurately represent human cognition.

The primary purpose is to make the logical commitments and consequences of theories explicit.

### B. Composition

Previously formalized mechanisms should be reusable in new theoretical contexts.

A theory of memory, for example, should not have to be reimplemented every time it participates in a model of arithmetic, language, or problem solving.

The library's constructs and theorems should support composition at two levels:

1. **Mechanism composition:** assembling independently defined cognitive processes.
2. **Theorem composition:** reusing existing proofs to establish properties of the assembled system.

The second is particularly important. A library of reusable cognitive algorithms alone would be useful software engineering, but the accumulation and reuse of theoretical results is what makes CogLean a contribution to theoretical science.

### C. Discovery

Formal composition can establish consequences that were not explicitly anticipated by the authors of the original theories.

It can also reveal:

- Previously unstated assumptions.
- Results that depend on specific parameters.
- Results that hold across an entire class of models.
- Conditions under which different theories make different predictions.
- Apparent predictions whose conditions cannot actually be reached by the implemented learning mechanism.
- Gaps between a theory's informal description and its formal consequences.

This is the most scientifically significant capability. Emphasize it throughout the paper.

## 2. Use Mathlib as the Organizing Analogy

Mathlib does not propose a new mathematical theory. It provides a shared formal environment in which mathematical concepts and results accumulate and can be reused.

CogLean aims to provide an analogous environment for cognitive science.

Explain the distinction between:

- Lean: the underlying formal language and proof checker.
- CogLib: reusable representations, mechanisms, interfaces, laws, and theorems about cognition.
- Individual cognitive theories: particular choices and combinations of those mechanisms.
- Applications: models of specific tasks assembled from the theories.

Make clear that the contribution is **not primarily a new programming language or Lean syntax for cognitive models**. It is the organization of cognitive theoretical knowledge into reusable, composable, mechanically checked components.

Do not claim that CogLean has already achieved Mathlib's scale or maturity. It is an initial demonstration of that approach.

## 3. Present the Multi-Digit Example as the Central Demonstration

Use the current GitHub repository:

https://github.com/jeffshrager/CogLean

In particular, examine:

- `CogLib/CogLib/Process/RecognizeRetrieve.lean`
- `CogLib/CogLib/Process/SampledRetrieval.lean`
- `CogLib/CogLib/Process/ProblemSolving.lean`
- `MultiDigit/MultiDigit/Postulates.lean`
- `MultiDigit/MultiDigit/AnyMemory.lean`
- `MultiDigit/MultiDigit/Phenomena.lean`
- `MultiDigit/MultiDigit/Columns.lean`
- `MultiDigit/MultiDigit/Solver.lean`
- `MultiDigit/MultiDigit/Integrated.lean`
- `MultiDigit/MultiDigit/ExampleACTR.lean`
- `StrategyChoice/StrategyChoice/Postulates.lean`

The existing `MultiDigit/paper/paper.tex` is a useful starting draft, but it predates the new integrated implementation. Revise it substantially rather than simply polishing its prose.

### Explain the composition

The integrated model combines:

1. An encoding of multi-digit arithmetic problems.
2. EPAM discrimination-net recognition.
3. DOA whole-problem associative retrieval.
4. A column-by-column problem solver invoked when retrieval fails.
5. DOA strategy-choice trials for individual column additions.
6. CogLib problem-solving machinery for sequencing operations and carrying.

The new `Integrated.lean` matters because the backup genuinely computes an answer. The older example supplied the correct multi-digit answer with `Dist.pure p.sum`.

Explain the distinction and why the integrated example constitutes stronger evidence of composability.

### Focus on the explanatory theorems

Select a small number of important results rather than cataloging every theorem.

In particular:

**Confident errors:** A problem confused with a familiar problem can elicit that familiar problem's answer with high confidence, even though the answer is incorrect.

Explain why this is a consequence of combining recognition and associative retrieval, rather than simply a property of DOA retrieval alone.

**Independence of the solver:** Improving the fallback solver does not change errors produced by successful whole-problem retrieval.

**Two sources of error:** The integrated system distinguishes errors originating in recognition/retrieval from errors originating in column-level computation.

**Memory substitution:** Show that replacing EPAM with ACT-R changes predictions while preserving the remaining machinery.

At least one important theorem should be explained in enough detail that a cognitive scientist can see exactly what is assumed, which intermediate results are reused, and what is deduced.

Do not reproduce long Lean proofs. Show a theorem statement and explain its structure.

## 4. Distinguish Three Kinds of Results

This distinction is essential to scientific credibility.

### General results

Properties that hold for all implementations satisfying the specified mechanisms and hypotheses.

### Conditional results

Properties that follow only when additional conditions are satisfied—for example, a particular confusion occurs or associative strengths are sufficiently concentrated.

Identify which conditions follow from the mechanisms and which remain empirical or modeling assumptions.

### Results at chosen parameter settings

Exact computations for a particular encoding, learned net, association-strength distribution, confidence criterion, and search length.

These establish concrete behavior and can demonstrate that theorem hypotheses are satisfiable. They do not establish that the numerical values describe actual children.

In the current example, `150 + 100` is recognized as `100 + 100`:

- Whole-problem retrieval answers 200 with probability 45/46.
- The column solver is invoked with probability 1/46.
- The solver itself answers correctly with probability approximately 0.656.
- The overall probability of answering 250 correctly is approximately 0.0143.

The ACT-R substitution produces a substantially different probability of a correct response under the illustrated settings.

Check all numerical values against the current Lean files before including them.

Never present these illustrative numbers as empirically fitted predictions.

## 5. Address the Scientific Status of Proofs

Explain explicitly:

**Formal validity is not empirical validity, and neither is automatically explanatory adequacy.**

A proof establishes that a conclusion follows from its premises.

For a result to be a cognitive explanation, its premises must independently characterize plausible cognitive mechanisms rather than simply restating the desired phenomenon.

For example, defining a serial-position curve directly in an attention schedule and then proving that the resulting system exhibits the serial-position effect would establish little explanatory distance.

By contrast, combining independently characterized recognition and retrieval mechanisms to derive a behavioral dissociation has greater explanatory interest.

Use the repository's `notes/EXPLANATORY_AUDIT.md` and the October 30 memo on phenomena, proofs, and composition.

Do not claim that every CogLean theorem provides a substantive psychological explanation. Some are mathematical properties of algorithms, some are conditional relations between laws, and some are genuinely compositional explanations.

Make this distinction a methodological strength of the paper.

## 6. Independent Simulation and Reachability

Describe the independent Python simulation of multi-digit addition and its comparison with the formal model.

Its role is not to validate the cognitive theory against people. It is to provide an independent check of whether the formalization behaves as its prose specification suggests.

Explain what was learned from the comparison, especially:

- The predictions that were successfully reproduced.
- Hypotheses that were not reached by learned discrimination nets.
- Assumptions about initial associative strengths that had not been fully specified.
- The distinction between logical correctness, reachable model states, and empirical adequacy.

Check the current simulation documentation and distinguish confirmed findings from issues subsequently resolved.

Avoid claiming that independent simulation proves a formalization faithful to its intended theory. It supplies valuable additional evidence, not a guarantee.

## 7. Position the Work Against Previous Research

Review and cite prior work on formal specifications and verification of cognitive architectures.

Important starting points include:

- Milnes et al. (1992), *A Specification of the Soar Cognitive Architecture in Z*.
- Gall and Frühwirth (2017), *An Operational Semantics for the Cognitive Architecture ACT-R and its Translation to Constraint Handling Rules*.
- Langenfeld and colleagues' work on formal verification of ACT-R models.
- Ganeriwala et al. (2025), *Enabling Formal Verification in a Common Model of Cognition*.
- Ganeriwala et al. (2026), *Formal Analysis of Stochastic Cognitive Models: A Translation Framework from Soar to PRISM*.

Verify bibliographic details and inspect these works rather than relying on their titles alone. Include other closely relevant precedents discovered during the literature review.

**Do not claim that CogLean is the first formalization or mechanical verification of a cognitive theory.**

Instead, investigate and explain what is distinctive about CogLean's emphasis on:

- Theory-neutral constructs and laws.
- Mechanism interchangeability.
- Reusable proofs.
- Deductive composition across independently developed cognitive theories.
- Deriving behavioral predictions from the composition.
- Identifying the assumptions on which those predictions depend.

Be precise about which of these capabilities are novel relative to earlier systems.

## 8. Recommended Paper Structure

Use approximately the following organization:

1. **Introduction:** The problem of cumulative theoretical knowledge in cognitive science. Existing computational theories are difficult to combine and reason about deductively.
2. **CogLean:** The library idea, its architecture, and the distinction between mechanisms, theories, phenomena, and proofs.
3. **Formalizing existing theories:** EPAM and DOA, briefly, emphasizing what is independently established about each.
4. **Composing theories:** Multi-digit addition as an application assembled from the existing components.
5. **Derived consequences:** Confident errors, error-source decomposition, solver independence, and memory substitution.
6. **Checking the formalization:** Independent simulation, reachability, and discovered limitations.
7. **Discussion:** Scientific value, relationship to previous formal methods, limitations, and future prospects.

Include:

- One clear architecture diagram showing CogLib, theories, and the multi-digit application.
- One diagram showing the actual composition of mechanisms within the multi-digit task.
- One table distinguishing general, conditional, and parameter-specific results.
- One comparison showing how EPAM and ACT-R produce different consequences under otherwise comparable conditions.

Avoid a sprawling survey of everything currently implemented in CogLean. The wider library demonstrates ambition and scope, but the paper needs one convincing, fully understandable example.

## 9. Limitations and Future Work

Acknowledge:

- Associative strengths in the worked example are chosen rather than derived from experience.
- Some important explanatory results depend on sharp associations or particular recognition confusions.
- Single-digit DOA assumes a representation with the correct number of objects available for elaboration and counting.
- The integrated model simplifies carrying and assumes independence among column-level operations.
- The framework does not automatically establish psychological plausibility.
- There are significant scalability questions, especially for continuous representations, large state spaces, and neural models.

Potential next steps include deriving associative distributions from learning histories, adding feedback-driven learning across complete trials, more general mechanism interfaces, and composing theories in other cognitive domains.

Present these as future work, not prerequisites for the present methodological contribution.

## 10. Style and Claims

Write for cognitive scientists, not primarily for theorem-proving specialists.

The paper should be rigorous but accessible. Explain why the results matter scientifically, rather than spending excessive space on Lean's syntax or proof tactics.

Avoid promotional language such as "revolutionary," "first-ever," or "solves cognitive modeling."

Do not imply that formal proofs make cognitive theories empirically true.

Do not describe numerical results from selected parameters as parameter-independent predictions.

Do not claim that all existing multi-digit predictions are novel consequences of composition; distinguish those that genuinely depend on interactions from simpler consequences of individual assumptions.

Most importantly, **do not frame the work as a new model of arithmetic performance**. Arithmetic is the demonstration, not the scientific objective.

## 11. Suggested Title

Working title:

**CogLean: Compositional Proof of Cognitive Predictions**

Alternative:

**Toward a Shared Formal Library of Cognitive Theory: A Demonstration in Multi-Digit Arithmetic**

The first is stronger; the second more explicit about the paper's preliminary scope.

## 12. The Question the Paper Must Answer

The paper should leave readers convinced of this:

*If independently developed cognitive theories are represented in a common formal library, can we derive scientifically meaningful consequences from their composition that would otherwise require constructing and investigating a new integrated model from scratch?*

The multi-digit case should supply a concrete, technically credible initial answer.

The final discussion should return to the larger ambition: a cumulative theoretical science in which cognitive constructs and their proven properties can be reused across models, tasks, and research traditions.

## Deliverable

Produce a complete revised LaTeX manuscript suitable for circulation to cognitive-science colleagues.

Preserve the existing paper as a reference and work in a separate draft or branch.

Include a verified bibliography and clear references to the formal definitions and theorems in the repository.

After the draft, provide a short editorial note identifying:

1. The paper's three strongest claims of scientific novelty.
2. The three most serious objections a skeptical cognitive scientist might raise.
3. Any claims in the draft that still need additional verification, empirical grounding, or literature review.

The goal is a credible, tightly argued first paper that establishes the value of CogLean's approach—not a comprehensive manifesto for the eventual library.
