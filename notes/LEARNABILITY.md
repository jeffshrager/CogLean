# Learnability theorems available in CogLean (candidates, 2026-10-30)

A learnability theorem says that **for every task in a class, and any instruction or experience of a given form, the mechanism reaches competence from a task-independent start**. The task enters as data, quantified over, so no task model is assumed. These are the candidates in CogLean. None of them has been started.

| # | Theorem | Status | Notes |
|---|---|---|---|
| 1 | **EPAM learns any list to criterion.** For every list of mutually distinguishable items, study yields a net recognizing each, with no interference. | Proved (`netLearner_reachesCriterion`, `learnAll_recognizes`) | Needs relabelling as learnability, not proof. |
| 2 | **DOA learns sharp associations from its own backup.** For every problem, take an exact backup, a criterion above the initial wrong-answer strengths, and retrieval that states only answers above the criterion. Then every stated answer is correct, only the correct one is strengthened, and within about (criterion − initial) / (2 × increment) trials only the correct answer clears the criterion. | Close | Discharges the premise the audit flags as assumed, never derived: *sharp associations*, in every confident-errors result. |
| 3 | **Practice removes errors for every studied problem set.** EPAM's `learnAll_recognizes` plus (2): for every finite problem set, study and column-backup practice yield correct retrieval on every studied problem. | Close, compositional | Makes confident errors developmental: present before discrimination and practice, gone after. |
| 4 | **The arithmetic view works for every number concept.** Quantify `after_exact` over the concept: every "multiple of k", and conjunctions of them, becomes exact after the view. | Small | Instruction as data, quantified over concepts. |
| 5 | **Instruction as data repairs a procedure.** A learner lacking the carry rule receives the carry operator as a view; view application merges it, and the solver is exact on every problem. | Larger | Needs the addition operators moved from Lean definitions into data (knowledge-net frames, or CMC rules). Overlaps the CMC proposal's stage 5. |

**Recommended order:** (2), (4), (3), then (5).

**Deferred:** chunking ("a subgoal solved once becomes retrieval"), at the user's request. It would add further theorems of this kind, linking Soar's chunking to DOA's strengthening.
