# CogLean: Toward a Mathlib of Cognitive Theory

**Direction, architecture, scientific rationale, and next steps**  
**27 October 2026**  
**Working design memorandum**

## Executive summary

CogLean began by formalizing three related cognitive theories in Lean 4: EPAM's discrimination networks, Siegler and Shrager's distributions-of-associations (DOA) model of strategy choice, and a multi-digit addition model combining them. The original achievement was to prove behavioral predictions from explicit postulates, for arbitrary permitted choices of the models' parameters, rather than merely reproduce selected outputs by simulation.

The recent reorganization changes the project's ambition. CogLean is becoming a **library of reusable cognitive constructs and conditional theorems**, not merely an archive of formalized cognitive models. This is the relevant analogy to Mathlib. The long-run objective is that researchers can define independently useful cognitive mechanisms, establish their laws, compose them into complex systems, and inherit predictions without rebuilding the underlying proofs.

The current memory-centered architecture is an important step in that direction:

1. A `Retriever` interface separates the observable contract of studying and retrieving representations from particular memory implementations.
2. Theory-neutral *laws* characterize such an interface.
3. A *theory matrix* records, by proof or counterexample, how several memory families relate to those laws, with an explicitly separate empirical judgment row.
4. An *experiment layer* states a protocol once and runs or analyzes it with any implementation of the interface.

The strongest immediate opportunity is **compositional theorem inheritance**: prove a behavioral result from the laws of multiple interacting cognitive components, then change the components without changing the general theorem. Multi-digit addition is already close to being the first demonstration.

**Recommendation:** Do not undertake a wholesale reorganization. Keep CogLib, the concrete theories, CogMatrix, and Experiments. Consolidate laws with their interfaces; add a minimal, reusable composition abstraction by extracting the connection between recognition and strategy choice from MultiDigit; prove a law-level experiment discriminator; and let these concrete exercises determine the next generalization. Avoid designing a universal cognitive architecture before the use cases demand one.

## 1. What counts as knowledge in a library of cognitive theory?

The central rationale appears in the prospectus under **"What is true here."** Mathematics can develop large libraries of theorems without asking whether the mathematical objects being studied describe the world. Cognitive science, by contrast, contains competing, empirically unsettled theories.

That need not prevent cumulative formal knowledge. Three kinds of claim must be kept distinct:

| Kind of claim | Example | Epistemic status |
| --- | --- | --- |
| A law entails a prediction | Certainty and stability imply perfect self-retrieval across a no-repeat study list | A conditional mathematical theorem |
| A formalized family satisfies a law | EPAM-style discrimination retrieval satisfies stability under the specified conditions | A mathematical theorem about that implementation |
| Human cognition satisfies a law | People exhibit immediate recency under specified experimental conditions | An empirical judgment, revisable with evidence |

The first two claims can remain true even when the cognitive theory they describe is empirically rejected. The third is not proved by Lean. Its interpretation depends on experimental procedures, task conditions, measurement assumptions, and empirical evidence.

This is one of CogLean's potentially important scientific contributions: **the conditional consequences of a theoretical commitment can accumulate even when the popularity or empirical status of the containing theory changes.** A failed prediction can identify precisely which premise, combination of premises, or measurement interpretation needs revision. Theorems expose dependencies that informal theories often leave implicit.

The qualification is equally important: proof establishes the consequences of *formal definitions*, not the adequacy of those definitions as reconstructions of EPAM, ACT-R, DOA, or human cognition. Simulation checks, independent implementations, empirical comparisons, and historical/theoretical scrutiny remain essential.

## 2. The current memory architecture

### 2.1 The `Retriever` interface

CogLib's generic retrieval interface has two operations, schematically:

```lean
structure Retriever (State Stim : Type) where
  study    : State → Stim → State
  retrieve : State → Stim → Dist (Option Stim)
```

Studying a stimulus changes a memory state. Retrieval takes a state and a probe and returns a probability distribution over a retrieved stimulus or `none`. EPAM's deterministic recognition is one possible implementation; activation-based or strength-based retrieval can be probabilistic.

The crucial point is that an experiment or general theorem can depend on this interface without referring to the machinery implementing it. The interface supplies a common vocabulary; it does not imply that all memory theories are equivalent.

### 2.2 The five current laws

The matrix laws are defined relative to an initial state and a permitted universe of studied stimuli. Their exact Lean definitions are more specific than their informal names.

| Law | Formal meaning in the current library | Cognitive question |
| --- | --- | --- |
| **Certainty** | Immediately after studying `y`, a probe `y` retrieves `y` with probability 1, in any reachable permitted state | Is newly encoded material perfectly accessible? |
| **Stability** | Studying a different `z` leaves the probability that probe `y` retrieves `y` unchanged | Can new learning interfere with an old item's self-retrieval? |
| **Order-freedom** | From any reachable state, studying `a` then `b` leaves the full retrieval distribution, for every probe, the same as studying `b` then `a`. Only the last two study events are swapped, and only retrieval, not the memory state, must agree. A swap in mid-history, followed by more study, is not covered | Does study history matter apart from the accumulated content? |
| **Recency** | Of two previously unstudied items presented last, equally similar to a probe, the second has strictly higher retrieval probability | Does retrieval favor the more recent of otherwise matched traces? |
| **Stored-only** | The retriever assigns zero probability to returning any representation not actually studied | Can retrieval output a reconstructed or blended representation? |

These laws constrain different aspects of memory: success, interference, order, time, and output content. They are deliberately mechanism-neutral. They are not representation-neutral: stimuli are binary codes, recency's "equally similar" is a count of mismatching features, and stored-only compares codes for identity.

The laws are not all mutually independent, nor are they necessarily the best final vocabulary. In fact, discovering their logical relationships is itself a legitimate mathematical program. Future laws may be graded: bounded interference, frequency monotonicity, similarity-dependent confusion, and quantified recency effects rather than all-or-none constraints.

### 2.3 The theory matrix

The generated matrix currently contains four memory families and five laws:

| Formalized memory family | Certainty | Stability | Order-free | Recency | Stored-only |
| --- | --- | --- | --- | --- | --- |
| Discrimination (EPAM net) | Has | Has | Lacks | Lacks | Has |
| Activation (restricted ACT-R) | Lacks | Lacks | Lacks | Has | Has |
| Strength with criterion (DOA-style) | Lacks | Lacks | Has | Lacks | Has |
| Global matching (MINERVA 2-style) | Lacks | Lacks | Has | Lacks | Lacks |
| **Human evidence, as currently judged** | **Lacks** | **Mixed** | **Lacks** | **Has** | **Lacks** |

The first four rows are generated from Lean results; the human row comes from an evidence file and is different in kind. On the current judgments, no family agrees with every empirical entry, and the restricted activation family agrees with three of four entries that are not marked mixed.

It is useful to think of a matrix as a **generated comparison view**, not as the central ontology of the library. The objects of lasting value are the interfaces, laws, implementations, proofs, and counterexamples from which views like this can be constructed.

### 2.4 The decisive asymmetry of "has" and "lacks"

A **has** cell usually proves a universal result within the stated family and parameter restrictions. A **lacks** cell shows that the universal law fails, often by one concrete counterexample. It does **not** show that every setting of that family must exhibit the opposite behavior.

Consequently, these are distinct statements:

- A family guarantees a law.
- A family guarantees the negation of a particular behavioral condition.
- A family permits both the condition and its failure, depending on parameters or history.

MINERVA can retrieve the studied items perfectly in the present example despite lacking the universal certainty law. Similarly, a memory family that lacks global stability may nevertheless behave stably in a particular experiment. The roadmap should therefore include **parameter-region theorems** and stronger distinctions between guaranteed, impossible, and possible behaviors.

The labels of the rows also require care. The discrimination row characterizes EPAM's *recognition net*, not every part of EPAM; the paired-associate component can show interference. The ACT-R instance currently uses restricted parameters. The MINERVA formalization uses simplified binary features and deterministic echo readout. The mathematical claims are exact for these implementations, but they do not automatically characterize all variants of the named theories.

## 3. The experiment layer: present achievement and limitation

The first general experiment studies a list once, without feedback, and then probes memory without changing it. Measures include self-retrieval by serial position, probability of retrieving some studied item, and probability of retrieving the probe itself.

The theorem `curve_flat` establishes:

\[
\text{Certainty} \land \text{Stability}
\Longrightarrow
\text{all self-retrieval probabilities equal 1}
\]

for a study list with no repeated stimuli, under the theorem's other domain assumptions. This result is proved against the interface and inherited by EPAM's discrimination implementation. It is not a separately hard-coded EPAM prediction.

The demonstration studies three binary items (`110`, `101`, `011`) and probes those items plus two unstudied lures: the prototype `111` and the dissimilar `000`.

| Memory | Self-retrieval by serial position | `111` called old | `111` retrieved as itself | `000` called old |
| --- | --- | --- | --- | --- |
| EPAM | 1, 1, 1 | 1 | 0 | 1 |
| ACT-R | 40/97, 15/28, 120/157 | 55/61 | 0 | 55/67 |
| DOA-style strength | 8/17, 8/17, 8/17 | 1 | 0 | 1 |
| MINERVA-style global matching | 1, 1, 1 | 0 | 1 | 0 |

All entries are established exactly for the corresponding configurations. Some are consequences of general laws; others are computations from a complete formalized mechanism. These must not be conflated. In particular, a universal recency law, as currently defined, is not by itself a theorem that *all* self-retrieval serial-position curves rise; order-freedom alone does not require distinct study items to have identical self-retrieval probabilities.

### A serious empirical bridge problem

The formal **stored-only** law concerns the *identity of the representation returned by memory*. The behavioral observation "the participant called an unstudied probe old" concerns a *decision or report*.

Indeed, both EPAM and the DOA-style strength memory satisfy stored-only, yet both call the unstudied prototype old with probability 1 in this demonstration. They return a studied representation in response to an unstudied probe. MINERVA instead reconstructs and returns the unstudied prototype itself, but under the demonstration's crude old/new rule it does **not** call that lure old.

Thus a false recognition judgment does not, by itself, establish a violation of the formal stored-only retrieval law. False recall of an unpresented word is stronger behavioral evidence, but even that could be generated by a response-construction stage operating on retrieved stored material.

The general lesson is that **retrieval, decision, and overt report must be connected by explicit assumptions**. Similar cautions apply to using free-recall serial-position data to judge laws about probe-based retrieval. The human evidence row is a useful research hypothesis, not a mechanically established mapping from experiments to formal laws.

Eventually, the experiment layer should prove not only `law ⇒ internal model measure`, but, where possible, `laws + response/measurement assumptions ⇒ experimentally observable contrast`.

## 4. Deriving experiments from laws

An especially promising development is to reverse the usual workflow. Instead of choosing an experiment and computing each theory's predictions, **start with a formal disagreement and derive the shape of an experiment that could distinguish it**.

### 4.1 A clean example: order-freedom versus recency

Choose two distinct stimuli `A` and `B`, equally similar to a third probe `X`. Study each once. Counterbalance presentation order:

- Condition AB: study A, then B; test with X.
- Condition BA: study B, then A; test with X.

The test should record which representation was retrieved (or use a justified response rule that makes it observable). The test occurs immediately in the conditions covered by the formal recency law, with neither A nor B previously studied.

Let \(p_{AB}(A)\) be the probability of retrieving A after order AB, and define the preference for B over A:

\[
D_{AB}=p_{AB}(B)-p_{AB}(A),\qquad
D_{BA}=p_{BA}(B)-p_{BA}(A).
\]

The experiment's order effect is:

\[
\Delta=D_{AB}-D_{BA}.
\]

**Under order-freedom**, the complete retrieval distributions after AB and BA are identical. Therefore \(D_{AB}=D_{BA}\), and

\[
\boxed{\Delta=0.}
\]

**Under recency**, for the equally similar items, B must be favored after AB and A after BA. Therefore \(D_{AB}>0\), \(D_{BA}<0\), and

\[
\boxed{\Delta>0.}
\]

In fact recency and order-freedom are jointly inconsistent wherever recency's conditions can be met: two unstudied items in the stimulus set and a probe equally similar to both. The argument above is the proof. This is a genuine incompatibility derived from law-level commitments, without specifying an EPAM net, an ACT-R activation equation, a DOA strength distribution, or particular values of their parameters. It would make an excellent small Lean experiment theorem, with precise hypotheses on the available items, similarity, and initial state.

The behavioral implementation still requires a measurement bridge: a participant's A/B response must correspond sufficiently closely to the retriever's output, or the response rule must be formalized. Forced choice and no-response conventions need explicit treatment.

### 4.2 A general experiment-discovery procedure

1. **Find a formal disagreement.** Look for two laws, or two sets of law/parameter hypotheses, imposing incompatible constraints.
2. **Derive a distinguishing witness.** Find stimuli, histories, probes, and contexts in which the constraints differ.
3. **Construct a protocol.** Turn the witness into study/test conditions and an explicitly defined dependent variable.
4. **Prove separation.** Establish nonoverlapping possible outcome sets or quantitative bounds for the competing hypotheses.
5. **Validate observation.** State what response or measurement assumptions connect the formal variable to human data.

For bounded finite models, candidate witnesses can be discovered by enumeration or model checking, and then verified by Lean. For general models, the goal is stronger: prove separation for all settings in a specified parameter region. Some matrix differences will yield universal discriminators; others will yield only conditional ones. A single counterexample to a universal law does not guarantee an experiment that distinguishes every implementation of the family.

This makes CogMatrix potentially more useful as an **experiment generator** than as a scoreboard. The comparison tells researchers what it is worth measuring next.

## 5. Beyond memory: the Mathlib-scale vision

The long-term aim is not a separate hand-maintained matrix for every phenomenon. Cognitive *mechanisms*, their interfaces, their laws, and their means of composition should form the reusable core. Phenomena are generally consequences of mechanisms acting in tasks, not mechanisms themselves.

Three concepts must be distinguished:

| Category | Examples | Role |
| --- | --- | --- |
| **Capabilities and interfaces** | Retrieval, learning, attention, perception, goal management, strategy choice, action | What a subsystem can do |
| **Laws and architectural commitments** | Stability, locality, recency, competition, resource bounds, goal persistence, information-flow restrictions | What an implementation or interaction guarantees |
| **Behavioral phenomena** | Serial position, Stroop interference, confident arithmetic errors, skill acquisition, transfer | What a composed system predicts in a task |

It may be useful to generate a memory matrix, a strategy-choice matrix, and an attention matrix. But the scientifically powerful objects will often be **theorems connecting entries across components**, not the matrices themselves.

### 5.1 Composition is the critical missing abstraction

Multi-digit addition already combines recognition, associative retrieval, strategy selection, backup computation, and learning. A general system might connect a memory component to a choice component, and then to procedural execution and feedback. The components must agree on representation types, timing, state updates, and how results are passed between them.

This is not solved simply by putting every component into a giant `CognitiveSystem` record. The important question is which interaction assumptions are necessary for a behavioral theorem.

For example, suppose memory retrieval is stable. The final behavior may still change if the strategy chooser's preferences change. Conversely, memory retrieval could change while behavior remains invariant because the downstream decision rule maps different memories to the same response.

Therefore, a typical compositional theorem has the shape:

\[
L_{\rm memory} \land L_{\rm choice} \land
L_{\rm interaction} \Longrightarrow P_{\rm behavior}.
\]

The interaction law may specify which information the chooser sees, whether retrieval precedes choice, whether feedback changes either state, whether components share a clock, or whether resources are shared. These are substantive, contestable architectural commitments.

### 5.2 A non-arithmetic illustration: Stroop interference

A model of Stroop performance can combine perceptual encoding of word and ink color, attention to task-relevant features, learned word/response associations, response competition, and an instruction-maintaining control process.

A general theorem might state that **when incompatible response tendencies compete for a shared selection mechanism and such competition increases selection time, incongruent stimuli produce longer responses than appropriately matched congruent stimuli**. Different implementations—spreading activation, production conflict, neural competition—could inherit the theorem if they satisfy the required laws and interaction conditions.

The theorem should make clear what is assumed about measuring response time and controlling other differences between conditions. A cognitive phenomenon is rarely explained by one component in isolation.

### 5.3 Why not impose a comprehensive architecture now?

Mathlib succeeds through small abstractions and reusable theorems, not by requiring every mathematical object to inhabit one enormous universal structure. Similarly, a model of choice should not need to implement vision; a theorem about recognition should not require a goal stack; arithmetic should not require a motor system unless motor behavior is part of the question.

CogLean should let models declare only the interfaces they actually require. It should later support architectures such as ACT-R, Soar, and the Common Model of Cognition without privileging one of them as the foundation. The right composition abstractions should be discovered through concrete proofs and reuse, rather than invented wholesale.

## 6. The strongest present compositional theorem: confident errors

The multi-digit addition theorem `MD.confident_errors` is the best current illustration of the envisioned approach. It is cognitively rich even though its top-level Lean proof is short: the real work has been factored into general preceding results.

### 6.1 The phenomenon

A child has learned `100 + 100 = 200`. Presented with `150 + 100`, the child mistakenly recognizes it as the familiar problem and retrieves the strong association to 200. The child can consequently answer quickly and wrongly without showing the elevated backup use normally associated with uncertain associative retrieval.

The two mechanisms play different roles:

- **Recognition** selects which stored problem's associations to consult.
- **Associative retrieval** searches those associations, accepts an answer above a criterion, or exhausts its limited search and invokes backup.

The error may result from choosing the wrong *otherwise reliable* memory, rather than from weak or noisy associations within the chosen memory.

### 6.2 Formal assumptions

Let `q` be the familiar stored problem and `x` the unfamiliar presented problem. The general theorem requires:

1. Retrieval of `q` returns `q`'s stored code with probability 1.
2. Retrieval of `x` also returns `q`'s stored code with probability 1.
3. The sums differ: `x.sum ≠ q.sum`.
4. The associations attached to `q` are **sharp**: only `q.sum` can clear the confidence criterion.
5. Search probabilities are well-defined (the relevant totals are nonzero), and both backup distributions have total mass 1.

The representation, association strengths, threshold, number of searches, and backup algorithm otherwise remain parameters.

### 6.3 The three-part conclusion

The theorem proves:

\[
P(\text{wrong whole-problem answer}\mid q)=0,
\]

\[
P(\text{wrong whole-problem answer}\mid x)
=P(\text{whole-problem answer}\mid x),
\]

and

\[
P(\text{column backup}\mid x)
=P(\text{column backup}\mid q).
\]

The first result follows because every accepted retrieval answer from `q` is correct *for q*. The second follows because the same answer is necessarily incorrect *for x*. The third follows because both problems consult exactly the same associative distribution, so retrieval is exhausted with the same probability.

If the chance that one associative search clears the threshold is \(R_q\), and at most \(n\) searches occur, both problems use backup with probability

\[
(1-R_q)^n.
\]

The theorem does **not** assert that all trials are wrong. It asserts that all *whole-problem retrieval answers* on `x` are wrong. Backup answers may be correct. Nor does sharpness alone imply frequent confident errors: if \(R_q=0\), all trials could use backup. A claim of frequent, low-backup errors needs a further assumption that retrieval success is high. Calling the errors "fast" also needs an explicit timing model or interpretation of the response routes.

### 6.4 How the Lean proof composes prior theorems

The general proof in `AnyMemory.lean` establishes its three conjuncts with already proved results:

```lean
by
  refine ⟨confusion_gives_neighbours_answer
      retrieve E str as cc n backup q q
      (hT _) hq hs,
    wrong_eq_whole_of_sharp
      retrieve E str as cc n backup x q _
      (hT _) hx hs hne, ?_⟩

  rw [columns_prob_certain
        retrieve E str as cc n backup x _ hx hbx hT,
      columns_prob_certain
        retrieve E str as cc n backup q _ hq hbq hT]
```

The first subsidiary theorem shows that sharp associations cannot produce an incorrect whole-problem answer for the familiar problem. The second shows that whole-problem retrieval on the confused problem is equivalent to a wrong answer. The two rewrites turn the remaining backup-probability goal into an equality of identical expressions.

The EPAM-specific theorem in `Phenomena.lean` is nearly an adapter: it rewrites an EPAM `trial` as generic `trialWith`, supplies the fact that the discrimination net selects the required representation with certainty, and applies `AnyMemory.confident_errors`.

**This is already theorem inheritance across an abstraction boundary.** It is a prototype of the CogLean/Mathlib vision. Any memory implementation providing the same deterministic-routing conditions can use the general result, whether or not it is an EPAM net. A genuinely noisy retrieval model may instead require a graded version of the theorem.

### 6.5 A worked instance

The repository's worked example recognizes `150 + 100` as `100 + 100`. Under the selected association strengths and one-search setting, it returns the wrong whole-problem answer 200 with probability \(45/46\), and a correct column-backup answer 250 with probability \(1/46\). These are exact results for that *instance*, not fitted probabilities and not universal numeric consequences of the general theorem.

The important discovery is the structural **dissociation of error from uncertainty**: performance on an unfamiliar problem can be confidently wrong because the wrong familiar problem was selected, even when retrieval from the selected association set is strong and reliable.

## 7. How much reorganization is needed now?

The current division is fundamentally sound:

| Area | Recommended responsibility |
| --- | --- |
| **CogLib** | General interfaces, laws, generic mechanisms, composition operators, and reusable theorems |
| **CogMatrix** | Generated comparisons among implementations and empirical judgments, with theorems and sources kept distinct |
| **Experiments** | Task protocols, measurable quantities, experiment-level theorems, and formal observation assumptions |
| **EPAM / StrategyChoice / MultiDigit** | Concrete formalizations, historical/theoretical commitments, worked examples, and system-specific results |

Three changes are warranted now, without a grand redesign:

**First, place laws with their interfaces.** The five matrix laws presently live in CogMatrix, while older retrieval properties such as `StableRetrieval` and `AgreesOn` live under CogLib's `Phenomena`. Over time, the canonical general laws should be in CogLib's memory area and imported by CogMatrix. There should be a single clear home for each abstraction.

**Second, extract one small composition abstraction from MultiDigit.** The recognition-to-associative-search-to-backup connection is already real and understood. Generalize just enough to allow the same composition to be used in another task. Do not prematurely create a universal `CognitiveSystem` containing all possible faculties.

**Third, separate mechanism laws from behavioral phenomena.** Properties of a retriever should be organized with retrieval; observable behavioral consequences should live with experiments or higher-level phenomena. Their connecting theorems are where the scientific explanations become explicit.

New directories for attention, perception, and goal management should be created when actual formalizations need them, not as an empty speculative taxonomy. The Common Model of Cognition is a useful checklist, not necessarily the foundational type structure.

## 8. A prioritized research and engineering program

### Immediate: demonstrate laws and composition end to end

1. **Unify memory laws.** Reconcile the matrix's probabilistic `Stability` and `Certainty` with MultiDigit's earlier `StableRetrieval` and `AgreesOn`, retaining any genuinely distinct properties but relating them explicitly.
2. **Prove the order-freedom/recency experiment discriminator.** Define a counterbalanced study–test protocol and derive \(\Delta=0\) versus \(\Delta>0\) from law hypotheses alone. Specify the retrieval-to-response bridge.
3. **Extract the recognition–strategy composition.** Refactor only the generic parts of `trialWith`, associative search, and backup necessary for reuse; preserve the existing MultiDigit application as an instance.
4. **Reprove or inherit a substantive MultiDigit theorem through that composition.** `confident_errors` is a natural candidate; a graded-confusion theorem for probabilistic memory would make the comparison stronger.
5. **Apply the composition outside arithmetic.** A small categorization or word-association task would test whether the abstraction is genuinely domain-neutral.

### Next: strengthen theoretical discrimination

6. **Map parameter regions.** Replace a mere counterexample in a `lacks` cell with sufficient or necessary conditions for a family to satisfy a law, where feasible.
7. **Build a hierarchy of graded laws.** Include frequency sensitivity, similarity gradients, bounded interference, and quantitatively characterized recency. Prove implication and incompatibility relationships among laws.
8. **Add families as adversarial tests of the law vocabulary.** A new family should either fit existing distinctions or reveal a consequential dimension the laws miss, as MINERVA revealed the need for stored-only retrieval.
9. **Establish observational semantics.** Introduce decision and reporting components so that empirical tests target identifiable model properties, rather than inferring internal retrieval directly from old/new judgments.

### Longer term: multi-component cognition

10. **Introduce interfaces only when demanded by working theories.** Strategy choice is the obvious next area, followed by attention, goals/control, and action as concrete uses arise.
11. **Prove cross-component closure and interaction results.** Determine when component-level stability, competition, locality, or monotonicity survive composition—and when they do not.
12. **Develop experiment search.** For small finite domains, enumerate histories and probes to find behavioral witnesses of theoretical disagreement; lift selected findings into general Lean theorems.
13. **Keep quantitative contact with data.** Law-level results identify constraints and informative contrasts; full mechanisms and statistical observation models are still needed for fitting and uncertainty assessment.

## 9. Criteria for success

The most meaningful progress metrics are not simply the number of models or the number of Lean theorems.

The next milestones should be judged by the following questions:

1. Can an experiment be **derived from incompatible law-level commitments**, and can Lean prove the promised separation?
2. Can a behavioral theorem be proved from the laws of **two or more composed cognitive mechanisms**?
3. Can one mechanism be replaced by a different implementation while retaining the general theorem wherever its hypotheses remain satisfied?
4. Can that composition be reused in a **different cognitive task** without carrying arithmetic-specific assumptions?
5. Can an empirical observation be connected to the predicted mathematical quantity by a clearly stated response/measurement model?
6. Can model comparisons distinguish universal guarantees, parameter-dependent possibilities, and genuine impossibilities?

The fourth criterion is especially telling. A theorem about a recognition–choice composition becomes a true reusable cognitive abstraction when it operates outside the domain in which it was discovered.

## 10. Overall assessment

CogLean is headed in the right direction. It has already crossed the crucial boundary from theorem-proving *inside* particular cognitive models toward stating and proving results *about properties* that multiple models may share. The `Retriever` interface, the five-law matrix, the law-based experiment theorem, and the generalized MultiDigit results all support the intended direction.

The most important thing missing is a reusable account of **composition**, including explicit assumptions about the information and state that pass between mechanisms. A stable memory need not imply stable behavior when strategy preferences also change; a changing memory need not produce changing behavior if downstream decisions mask the difference. General cognitive predictions depend on both component laws and interaction laws.

No sweeping reorganization is needed. The appropriate next experiment in library design is small and concrete: extract a reusable composition from MultiDigit, prove one nontrivial inherited theorem, and apply the composition to a second task. In parallel, derive a counterbalanced experiment directly from the incompatibility of recency and order-freedom.

The ultimate value proposition is not merely that EPAM, ACT-R, DOA, Soar, and many other theories can each be formalized. It is that someone may establish a reusable result about memory, someone else a result about attention or choice, and a third researcher may combine them to obtain a behavioral prediction none of the original formalizations explicitly anticipated.

**CogLean's prospective contribution is a cumulative theory of the relationships among cognitive theories: their shared commitments, disagreements, composition principles, and empirically discriminating consequences.** The matrices are informative maps of those relationships; the reusable theorems are the real destination.

## Repository sources consulted

- [CogLean repository](https://github.com/jeffshrager/CogLean)
- [PROSPECTUS.md — Laws, families, theory matrix, and "What is true here"](https://github.com/jeffshrager/CogLean/blob/main/notes/PROSPECTUS.md)
- [notes/MATRIX.md — Generated matrix and evidence](https://github.com/jeffshrager/CogLean/blob/main/notes/MATRIX.md)
- [CogMatrix/Laws.lean — Exact law definitions](https://github.com/jeffshrager/CogLean/blob/main/CogMatrix/CogMatrix/Laws.lean)
- [CogMatrix/README.md — Family and cell qualifications](https://github.com/jeffshrager/CogLean/blob/main/CogMatrix/README.md)
- [Experiments/README.md — Study–test demonstration](https://github.com/jeffshrager/CogLean/blob/main/Experiments/README.md)
- [Experiments/StudyTest.lean — `curve_flat` theorem](https://github.com/jeffshrager/CogLean/blob/main/Experiments/Experiments/StudyTest.lean)
- [notes/MultiDigit_PREDICTIONS.md — Especially "Which predictions need EPAM"](https://github.com/jeffshrager/CogLean/blob/main/notes/MultiDigit_PREDICTIONS.md)
- [MultiDigit/MultiDigit/AnyMemory.lean — General `confident_errors`](https://github.com/jeffshrager/CogLean/blob/main/MultiDigit/MultiDigit/AnyMemory.lean)
- [MultiDigit/MultiDigit/Phenomena.lean — EPAM-specific corollary](https://github.com/jeffshrager/CogLean/blob/main/MultiDigit/MultiDigit/Phenomena.lean)
- [MultiDigit/MultiDigit/Postulates.lean — `trial`, `trialWith`, and composition of routes](https://github.com/jeffshrager/CogLean/blob/main/MultiDigit/MultiDigit/Postulates.lean)

*This memorandum is an architectural and scientific synthesis, not a claim that every suggested future theorem has already been formalized or that the repository has been independently rebuilt for this review.*
