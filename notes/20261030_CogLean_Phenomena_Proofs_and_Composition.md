# CogLean: Phenomena, Explanatory Proofs, and Cross-Domain Composition

**Conversation summary — October 30, 2026**  
**Project:** [CogLean](https://github.com/jeffshrager/CogLean)  
**Status:** Conceptual discussion and targeted source review; no repository modifications were made.

## Executive summary

The conversation examined whether CogLean's formal theorems actually **explain empirical cognitive phenomena** or merely restate properties already built into model definitions. The central conclusion was that the crucial distinction is **not where a definition lives in the repository**, but **what is assumed and what is derived**. A phenomenon such as the serial-position effect (SPE) is an empirically observed regularity, represented in Lean as a predicate. A cognitive mechanism can be proved to satisfy that predicate. But the explanatory strength of the proof depends on whether the phenomenon is genuinely derived from independently motivated mechanism assumptions rather than effectively stipulated in the definitions.

We considered—and then rejected as premature—an elaborate CogLean-specific checker for the provenance of explanatory proofs. Lean already enforces logical derivation and exposes theorem assumptions. The practical recommendation is to make explanatory premises explicit, use phenomena as theorem targets or properly discharged intermediate lemmas, and subject the scientific appropriateness of the assumptions to review.

A targeted review found the current **serial-position** result formally sound but relatively close to its premises; the **recognize–retrieve/confident-errors** result substantially more compositional and promising; and the **problem-solving** modules rich in executable mechanisms but currently possessing only minimal, mostly definitional theorems. The conversation ended with a stronger proposed demonstration: **`dont_practice_while_sleepy`**, a cross-domain derivation connecting fatigue-induced errors, procedural skill acquisition/chunking, and later behavior. Its most scientifically interesting prediction is conditional: sleepy practice can lead to persistent errors, especially when learning preserves erroneous choices and feedback does not correct them before consolidation.

## 1. What belongs in `Phenomena/`?

The initial concern was that phenomena are **observed in the psychological literature**, whereas theorems are **derived from postulates**. The serial-position effect, for example, is a behavioral pattern that some memory or attention mechanism is supposed to cause. Placing its formal definition in `Phenomena/` must not amount to assuming it as a foundational truth.

We distinguished three levels:

1. **Empirical phenomenon:** An observed pattern, such as better performance at the beginning and end of a list than in its middle.
2. **Formal characterization:** A Lean predicate specifying precisely what it means for a set of measurements or predictions to exhibit that pattern.
3. **Explanatory theorem:** A proof that a specified cognitive mechanism, under stated conditions, generates behavior satisfying the predicate.

For example, conceptually:

```lean
-- Defines a target; does not assert that any model exhibits it.
def SerialPositionEffect (n : Nat) (errors : Nat → Nat) : Prop :=
  ...

-- Derives that target for a particular mechanism.
theorem anchorAttention_serialPosition (n : Nat) :
    SerialPositionEffect n (errorsAt n) := by
  ...
```

A phenomenon definition is not an axiom. It is a proposition that may be proved about the behavior of a model. `Phenomena/` is therefore a defensible name and location. Moving or renaming files would not address the substantive epistemological issue.

A useful further distinction is between **observables** (e.g., accuracy or error rate by position), **phenomenon predicates** (e.g., primacy, recency, a bowed curve), and **predictions** (theorems that a model's observables satisfy those predicates). Some phenomena may need several formalizations: real serial-position curves can be asymmetric and condition-dependent, whereas a single stringent predicate might inadvertently favor one theory.

## 2. The proof-chain concern: phenomena must not be smuggled into assumptions

The user emphasized that a phenomenon could legitimately be a **lemma**, but should not be at the bottom of an explanatory proof chain—just above the foundational axioms—unless it has already been established from mechanisms.

Consider a conditional theorem:

```lean
theorem otherEffect
    (hSPE : SerialPositionEffect n errors) :
    SomeOtherEffect errors := by
  ...
```

This may be mathematically valid, but it does **not** show that the model explains `SomeOtherEffect`; it assumes the SPE. By contrast:

```lean
have hSPE : SerialPositionEffect n errors :=
  anchorAttention_serialPosition n
exact otherEffect hSPE
```

Here the intermediate phenomenon is discharged by an earlier proof. The final explanatory theorem should expose only the relevant theoretical commitments, parameters, and experimental conditions—not an unexplained instance of the phenomenon it purports to derive.

**Important nuance:** It is not inherently wrong to state conditional relationships between phenomena. Such theorems simply should not be presented as unconditional model-derived predictions. Nor is the presence of a phenomenon in a theorem's hypothesis itself logically circular; the problem arises when the scientific interpretation claims more than the theorem establishes.

### Lean's existing transparency

Lean's theorem statements show hypotheses and conclusions, and intermediate lemmas do not silently make their premises disappear. Commands such as:

```lean
#print someTheorem
#print axioms someTheorem
```

are useful for auditing. However, **`#print axioms` checks dependencies on axioms; it does not detect an ordinary phenomenon hypothesis in a theorem's type**. One must examine the statement and, where needed, definitions and dependencies. An assumption can also be disguised behind an innocuous name or definition, which is a scientific modeling issue rather than merely a proof-engine issue.

## 3. Should CogLean implement a special explanatory-proof checker?

An initial suggestion was to add metadata such as `@[cog_phenomenon]`, `@[cog_postulate]`, and `@[cog_prediction]`, or a special `cog_theorem` command, and have a metaprogram inspect declarations for undischarged phenomenon assumptions, unapproved axioms, or inappropriate dependencies.

**The user objected that this sounded like substantial work and raised the regress question: “Who checks the checker?!”**

The recommendation was revised: **do not build this machinery now.** Lean already checks formal validity. CogLean can adopt lightweight conventions:

- Define phenomena as predicates rather than asserting their occurrence as foundational facts.
- State the premises of explanatory theorems explicitly, distinguishing mechanism assumptions from experimental conditions.
- Present full theorem statements in scientific publications so readers can judge what has and has not been derived.
- Allow derived phenomena as lemmas when their premises have been discharged.
- Treat the scientific plausibility and independence of the postulates as matters for scientific scrutiny, not as things a custom checker can decide.

The central methodological point is that **formal validity and explanatory legitimacy are different standards**. CogLean should exploit Lean's proof transparency without building an elaborate parallel certification system prematurely.

## 4. Do CogLean's existing theorems actually derive interesting phenomena?

We distinguished three levels of achievement:

1. **Mechanism-to-behavior derivation:** A mechanism entails a specified behavioral pattern.
2. **Explanatory derivation:** The pattern follows from independently motivated premises, not premises that simply encode the result.
3. **Discriminating empirical prediction:** The theory yields an observable consequence that distinguishes it from plausible alternatives under comparable conditions.

A useful diagnostic question emerged:

> **How much of the predicted behavioral structure is already present in the premises, and how much emerges from the interaction of mechanisms?**

### 4.1 Serial-position effect: correct but close to definitional

The inspected file `CogLib/CogLib/Control/Serial.lean` defines:

```lean
def learnedOnTrial (n i : Nat) : Nat :=
  2 * distFromEnds n i +
    (if i ≤ n - 1 - i then 0 else 1)

def errorsAt (n i : Nat) : Nat :=
  learnedOnTrial n i
```

The corresponding phenomenon predicate in `CogLib/CogLib/Phenomena/SerialPosition.lean` says that, for positions in the list, greater distance from the nearer end implies strictly more errors. The theorem:

```lean
theorem anchorAttention_serialPosition (n : Nat) :
    SerialPositionEffect n (errorsAt n) :=
  ...
```

proves that the stipulated inward-from-the-ends schedule produces the stipulated bowed error pattern.

**Assessment:** This is a valid formal demonstration of an anchor-attention account, but the bow is substantially encoded in `learnedOnTrial` itself. The theorem does not derive the attention schedule from a more general attentional process, nor does it independently model learning and error generation. It is not logically circular, but its explanatory distance from the assumptions is small.

### 4.2 Recognize–retrieve: a stronger compositional result

The inspected `CogLib/CogLib/Process/RecognizeRetrieve.lean` composes:

- recognition of a problem code through memory;
- associative retrieval of an answer from the recognized code;
- a backup strategy if recognition or retrieval fails.

Its `confident_errors` theorem establishes a conjunction of outcomes when a novel problem is confused with a familiar one whose associations are sharp and whose correct answer differs:

- whole-problem retrieval on the familiar problem does not give a wrong answer;
- whole-problem retrieval on the novel problem always gives a wrong answer when it gives an answer at all;
- the novel and familiar problems have equal backup-use probability.

The more general `confident_errors_of_laws` obtains the same pattern from explicit memory properties—determinacy, certainty, and stability—together with conditions such as positive-probability confusion, sharp associations, and different correct answers.

**Assessment:** This is a much stronger example of mechanisms interacting to produce a behavioral conjunction, especially the combination of incorrect answers and no increase in backup use. Still, the theorem assumes critical conditions; it does not establish how often confusion and sharp associations arise in actual participants. A next step would be to compare predictions across memory families in `CogMatrix` under comparable training conditions and to identify independently manipulable conditions.

## 5. Audit of the problem-solving modules

The inspected `CogLib/CogLib/Process/ProblemSolving.lean` implements a shared problem-space abstraction and two control regimes.

### 5.1 Shared problem space

```lean
structure Space (S O : Type) where
  pre   : O → S → Bool
  apply : O → S → Dist S
```

This is a promising reusable interface: operators have preconditions and potentially probabilistic effects on states. It allows different problem-solving controls to operate on a common space.

### 5.2 Means–ends analysis (GPS-style)

The `MEA` structure supplies condition tests, a difference table mapping conditions to relevant operators, and operator preconditions. The recursive `achieve` function finds an unmet goal condition, tries relevant operators in order, recursively achieves their preconditions, applies an operator, and resumes work on the goal, with a depth bound.

**Important implementation detail:** The current `achieve` explicitly supports backtracking through `orElse`. It therefore cannot substantiate a theorem about inevitable failure after the first blocked operator unless a different policy is implemented or imposed.

**Current theorem status:** No theorems about `achieve` were found in this module. The code specifies a recognizable cognitive process, but it does not yet derive characteristic empirical consequences of means–ends analysis.

Potential explanatory targets include operator-order sensitivity, subgoal ordering, bounded-search failures, and cases where a solver fails despite an available solution.

### 5.3 Decision cycle with impasses and repairs (Soar/repair-theory-style)

A `Procedure` proposes an operator. When its precondition fails, the solver reaches an impasse. A `Repairer` supplies alternative operators; critics veto some; a surviving repair is selected uniformly. `step` implements one cycle and `run` repeats it.

Two existing theorems were inspected:

- `step_impasse_iff`: an impasse is equivalent to a proposed operator having a failed precondition. This is essentially a Boolean reformulation of the definition of `AtImpasse`.
- `step_no_impasse`: when the proposed operator's precondition holds, `step` applies that operator. This is essentially a direct consequence of the definition of `step`.

**Assessment:** These are sound code-level properties, not yet psychological explanations. There are no substantive theorems in this file about patterns of procedural errors, learning, success rates, or contrasts between problem-solving strategies.

### 5.4 What would make the problem-solving results more explanatory?

Three candidate directions were identified:

1. **Repair invariants:** A critic-vetoed repair cannot be selected. Useful verification, but close to definitional.
2. **Systematic procedural errors:** A repair that preserves some properties of an intended action while violating others can generate structured, repeatable errors. This could connect the implementation to the Brown–VanLehn repair-theory literature, provided the error pattern is not merely stipulated in the heuristics.
3. **Control-regime comparisons:** Run distinct problem-solving policies over the same problem space and derive conditions under which their success, failure, or error patterns diverge. This is especially promising for discriminating predictions.

Two limitations need attention: the current models chiefly return resulting states, rather than complete behavioral traces; and the means–ends and repair solvers differ in supplied knowledge as well as control. A clean comparison must hold relevant representational and knowledge commitments constant.

**Architectural recommendation:** Do not reorganize the problem-solving file merely for tidiness. First develop substantive theorems and observables. The scientifically important work is deriving consequences, not renaming or moving code.

## 6. Proposed cross-domain theorem: `dont_practice_while_sleepy`

The user's final proposal was a theorem informally called **`dont_practice_while_sleepy`**, combining:

1. **Fatigue/error relation:** People make more errors when sleepy. This could initially be an explicitly stated empirical assumption, and later a theorem of a fatigue or attention mechanism.
2. **Skill acquisition:** Practiced choices or procedures influence what becomes encoded in a learned skill.
3. **Future performance:** A learned skill influences later action selection, potentially preserving errors even after the person becomes alert.

The intended prediction is:

> Practicing while sleepy can increase the probability of acquiring an erroneous skill and later repeating the error while alert.

This is attractive because it **composes mechanisms from different domains** rather than proving a property of one mechanism in isolation.

### 6.1 A simple illustrative probabilistic model

Let:

- \(p_a\): probability of an erroneous action while alert;
- \(p_s\): probability of an erroneous action while sleepy;
- \(q\): probability that the executed action is encoded into a reusable skill;
- \(r\): probability that the learned skill is later used.

Under simplifying assumptions that encoding and later use are independent of alertness and of the error event in the relevant way, the probability of a later error through this pathway is \(pqr\). Thus:

\[
 p_s > p_a,\quad q > 0,\quad r > 0
 \quad\Longrightarrow\quad
 p_s q r > p_a q r.
\]

This arithmetic is straightforward. Its explanatory value would come from **connecting independently motivated mechanisms** and establishing the assumptions under which the product expression is appropriate.

### 6.2 Crucial scientific qualification: not all practice errors are learned

It does **not** follow from “sleepiness increases immediate errors” plus “practice creates chunks” alone that sleepy practice must increase later errors.

For example:

- Learning may preferentially encode successful rather than failed actions.
- Feedback may detect and correct an error before consolidation.
- Chunking may encode the result of subgoal reasoning, not simply copy each executed action.
- Sleepiness might alter the probability of learning or later skill selection, not just immediate action accuracy.

In particular, **Soar's chunking mechanism should not be described as indiscriminately storing every action chosen**. Standard Soar chunking constructs productions from subgoal processing and its results. A CogLean model of the proposed effect would need an explicit account of which results or decisions are learned, and under what conditions incorrect productions can arise.

### 6.3 A stronger conditional prediction

The most interesting result may be an interaction, not an unconditional slogan:

> **Sleepy practice increases persistent errors when the learning policy retains erroneous behavior sufficiently often, but the effect can be reduced or eliminated when feedback and correction prevent erroneous consolidation.**

This suggests an experimental design: compare sleepy and alert practice, cross that manipulation with feedback quality or timing, and test everyone later under alert conditions. The model should predict differences in later performance—not merely differences during practice.

A conceptual Lean theorem might look like:

```lean
-- Illustrative signature, not compiling CogLean code.
theorem dont_practice_while_sleepy
    (hFatigue : errorRate sleepy > errorRate alert)
    (hEncoding : ...)   -- Errors can be retained by practice
    (hReuse : ...)      -- Retained skills influence later choices
    (hConditions : ...) :
    laterErrorRate sleepy > laterErrorRate alert := by
  ...
```

Initially, `hFatigue` is an openly acknowledged premise. Later, a fatigue model could prove it, and the composed theorem would then depend on the fatigue model's postulates rather than on the empirical regularity as an undischarged assumption. The same approach applies to the encoding and reuse premises.

### 6.4 What would be required to implement this convincingly?

The discussion suggests the following development plan, **not yet implemented**:

1. Define a task-independent observable for immediate action correctness and a separate observable for later performance.
2. Formalize a fatigue-sensitive action-selection distribution, initially parameterized by an error-rate inequality.
3. Formalize a practice-to-skill update rule that distinguishes executed actions, successful outcomes, feedback, and retained productions.
4. Formalize later execution or selection of the learned skill in a common task environment.
5. Prove a conditional theorem showing when increased practice errors lead to increased later errors.
6. Prove counterexamples or boundary cases in which selective learning or corrective feedback prevents that result.
7. Eventually replace empirical premises with derived consequences of independently specified mechanisms, where feasible.
8. Compare resulting predictions with empirical literature and, ideally, design a discriminating experiment.

The boundary cases are as important as the positive theorem: they clarify exactly which cognitive assumptions make the prediction follow.

## 7. Broader implications for CogLean

This discussion sharpens CogLean's long-term ambition as a reusable library of cognitive theory:

- **Phenomena are explanatory targets**, not privileged foundational truths.
- **Mechanisms are reusable building blocks** with explicit assumptions and executable behavior.
- **Theorems establish consequences** of those mechanisms; their scientific strength depends on the independence and plausibility of their premises.
- **Composition is the opportunity:** Combining mechanisms of attention, memory, learning, and problem solving may produce predictions that no individual theory states on its own.
- **Conditional predictions are legitimate and valuable** when their premises are visible and the conditions can be tested or manipulated.
- **A stronger library is not necessarily one with more proofs.** It is one with more nontrivial, independently motivated, empirically interpretable deductions.

The proposed `dont_practice_while_sleepy` result illustrates the desired trajectory: begin with an explicit empirical assumption about fatigue; combine it with a formal theory of skill acquisition and later execution; derive a conditional prediction about persistent errors; identify the boundary conditions; and progressively replace assumptions with further mechanism-level derivations.

## 8. Conclusions and priorities

**Current state:** The serial-position module demonstrates a relatively direct mechanism-to-pattern derivation. Recognize–retrieve offers a stronger example of a cross-mechanism behavioral consequence. The problem-solving module implements meaningful processes but currently proves only elementary properties of the decision cycle.

**Near-term scientific priority:** Develop a substantive problem-solving/learning theorem rather than spend effort on file movement or an explanatory-proof checker.

**Most promising proposed demonstration:** `dont_practice_while_sleepy`, framed not as an unconditional fact but as a theorem about **the circumstances under which errors made during practice become persistent learned behavior**.

**Central criterion for judging progress:** The theorem should make clear which behavior is **derived**, which assumptions are **theoretical postulates**, which are **empirical premises awaiting explanation**, and which consequences are **novel and discriminating**.

---

### Source files examined during the conversation

- [`CogLib/CogLib/Phenomena/SerialPosition.lean`](https://github.com/jeffshrager/CogLean/blob/main/CogLib/CogLib/Phenomena/SerialPosition.lean)
- [`CogLib/CogLib/Control/Serial.lean`](https://github.com/jeffshrager/CogLean/blob/main/CogLib/CogLib/Control/Serial.lean)
- [`CogLib/CogLib/Process/RecognizeRetrieve.lean`](https://github.com/jeffshrager/CogLean/blob/main/CogLib/CogLib/Process/RecognizeRetrieve.lean)
- [`CogLib/CogLib/Process/ProblemSolving.lean`](https://github.com/jeffshrager/CogLean/blob/main/CogLib/CogLib/Process/ProblemSolving.lean)
- [`CogLib/README.md`](https://github.com/jeffshrager/CogLean/blob/main/CogLib/README.md)

*The Lean snippets labeled illustrative are conceptual sketches, not checked additions to the repository. This document summarizes the discussion and targeted code inspection, not an exhaustive audit or a completed implementation.*
