# Explanatory audit: what each headline result derives, and from what

Prompted by `20261030_CogLean_Phenomena_Proofs_and_Composition.md`. Lean checks that every theorem follows from its premises. It cannot say whether those premises already contain the phenomenon. This audit says that, for the headline results.

The catalog (`CATALOG.md`, column **Given**) reports mechanically which laws or phenomena a theorem assumes. The judgments below are scientific, not mechanical, and are open to dispute.

## How to read it

**Premises** are sorted into four kinds:
- **postulates:** a theory's mechanism, stated as definitions;
- **conditions:** situational hypotheses, such as "x is confused with q" or "the associations are sharp";
- **empirical premises:** assumptions taken from data and not yet explained by any mechanism;
- **assumed laws:** phenomena among the hypotheses, which makes the result conditional on them.

**Distance** says how far the result is from its premises:
- **definitional:** a restatement of the definitions;
- **close:** the pattern is largely encoded in the mechanism;
- **derived:** it follows from premises that do not mention it;
- **compositional:** it needs two or more mechanisms working together.

Where the result names its own theory as "derived", the question to ask is the memo's: *how much of the behaviour is in the premises, and how much emerges?*

## The library (CogLib)

| Result | Premises | Distance | Comment |
|---|---|---|---|
| `anchorAttention_serialPosition` | postulates: the attention rule (nearer an anchor first), one learning cycle per trial, anticipation scoring | close | Since this audit, derived from a rule over any anchors instead of a closed-form schedule. The rule still orders by nearness, so the bow is near the surface. Its value is that the same rule also gives the isolation effect. |
| `isolation_effect` | the same rule, with a distinctive item as a third anchor | derived | A second consequence of the rule, not built in. |
| `rank_lt_of_before` | the rule, for any anchors | derived | General: nearer an anchor means learned earlier. |
| `criterion_of_nonInterference` | assumed law: non-interference; condition: an invariant | derived, conditional | A relation between phenomena, not a model prediction. It becomes one when a model discharges non-interference, as discrimination nets do. |
| `netLearner_nonInterference` | postulates: discrimination learning | derived | Learning adds a test only where codes are confused, so nothing learned is disturbed. Close to the mechanism, but not stated in it. |
| `not_recency_of_orderFree` | assumed law: order-freedom | derived, conditional | Pure logic between laws. |
| `confident_errors_of_laws` | assumed laws: determinacy, certainty, stability; conditions: the stranger can be taken for a studied item, sharp associations, different correct answers | compositional, conditional | The strongest kind of library result. Its conditions (confusability, sharp associations) are not derived: how often they hold in people is open. |
| `RR.confident_errors` | postulates: recognize, then retrieve, then back up; conditions: certain retrieval of q, and of x as q; sharp associations | compositional | Certainty enters as a condition, which `confident_errors_of_laws` then derives from laws. |
| `not_dissociates` | assumed property: membership nondecreasing in typicality | derived, conditional | — |
| `achieve_sound`, the merge theorems, `activation_append`, `step_impasse_iff`, `step_no_impasse` | the algorithms' definitions | definitional | Properties of mechanisms, not psychological predictions. They are needed, but they explain nothing on their own. |

## Theories

| Result | Premises | Distance | Comment |
|---|---|---|---|
| EPAM's non-interference, criterion, oscillation, retroactive inhibition | postulates: nets, cue codes, learning | derived | Oscillation and retroactive inhibition come from cue codes outgrown by the net, which is not stated in the postulates. |
| `SC.counting_error_share` (DOA) | postulates A1–A5 | derived | The chapter's "nonintuitive prediction": the associations don't affect the counting error share. |
| `SC.retrieval_prob`, `retrieval_error_share` | postulates A2–A3 | close | The algebra of sampling. |
| `SC.peaking_can_raise_overt_use` | postulates; one setting | derived (counterexample) | Refutes an informal claim of the chapter at one setting. |
| `MD.confident_errors` | postulates: EPAM and DOA; conditions: the net confuses x with q, sharp associations | compositional | Confusion is derived for learned nets elsewhere (`near_miss_*_learned`). Sharp associations remain a condition. |
| `MD.column_error_is_doa_error` | postulates: column backup and DOA facts | compositional | — |
| `Integrated.integrated_confident_errors`, `errors_two_sources` | postulates: EPAM, DOA (whole-problem and single-digit), the decision-cycle solver; conditions: confusion (from the learned net), sharp associations, proper strengths | compositional | Confident errors with a computed backup, so no route is handed the answer. A second consequence: the column route's errors are the single-digit DOA errors, scaled to their column, so a confused problem has two sources of error with different signatures. |
| `Integrated.whole_independent_of_solver` | the same | compositional | A better solver cannot repair a whole-problem error. |
| `Integrated.setting_*` | the above, at chosen numbers | instance | Values at one setting (150 + 100 answered 200 with probability about .978). An illustration, not evidence. |
| `Solver.bridge` | two formalizations | definitional (an equivalence) | It licenses replacing the backup; it predicts nothing itself. |
| `Solver.noCarry_bug` | postulates: the procedure with the carry rule deleted, repair heuristics, critics | derived | The bug isn't in any one premise. It comes from the deletion, the impasse and the critics together. |
| `Solver.noCarry_exact` | the same | derived | A learner lacking carrying looks competent without carries. |
| `gps_every_problem`, `gps_exact` | postulates: means-ends analysis, the difference table, operator preconditions | derived | The goal names no order. The units-first order is carried by the preconditions (adding a column needs its right neighbour written), so it is domain knowledge, not control. |
| `regimes_diverge` | the same operators and the same deletion, under two control regimes | compositional, discriminating | The same knowledge deficit gives a confident bug under repair, and no answer under means-ends analysis. A testable contrast between control regimes, with knowledge held constant. |
| The CogMatrix cells (has / never) | each family's postulates | derived | Several are close: activation never has certainty because retrieval always has a failure weight. |
| `Exp.orderFree_recency_inconsistent` | assumed laws | derived, conditional | — |
| `Exp.curve_flat` | assumed laws: certainty, stability | derived, conditional | `epam_curve_flat` discharges both from EPAM's cells, which makes it a model prediction. |
| `Concepts.conjunction_effect` | postulates SO1–SO4 | close | Modification moves votes onto the instance's value, so similarity rises nearly by construction. Over-extension then needs Hampton's H1, a second mechanism. |
| `cq_distanceEffect`, `cq_no_typicality`, `cq_no_reversal` | postulates CQ1–CQ3 | definitional / close | Cost is distance by definition. The value is in the contrast with feature comparison (the matrix), not in the derivation. |
| `fc_typicality` | postulates FC1–FC2 | close | — |
| `ViewApplication.after_exact`, `after_no_overextension`, `typicality_unchanged` | postulates: view application, categorization; data: the learner's theory and the ARITHMETIC view | compositional | Two generic mechanisms. The over-extension disappears and typicality survives, which neither mechanism says alone. |

## Empirical premises still awaiting explanation

- **Sharp associations**, in every confident-errors result: assumed, not derived from learning.
- **Prior associations** in the worked cases and the DOA simulation's parameters: chosen, not grounded (OPEN_ISSUES #18).
- **The evidence row** of the theory matrix: a judgment of the literature.
- **The anchors** themselves: which items are distinctive is given, not derived from features.

## Weakest results, as targets

1. **Semantic-memory costs** (`cq_*`): definitional. A process model of search, such as spreading activation with a decision criterion (C&L assumptions 8–13), would make distance effects derived, not defined.
2. **The serial-position bow:** improved, but still close. Deriving the attention rule itself from distinctiveness of features would make the anchors derived.
3. **`conjunction_effect`:** close. Its interest lies in what it combines with (threshold membership, views).
4. **The algorithm properties:** fine as library facts. They should never be presented as explanations.
5. **Sharp associations:** derive them from DOA learning, where the simulation shows peaked distributions emerging. A theorem would replace a condition.

## Conventions (also in `CLAUDE.md`)

- Phenomena are targets, not premises.
- A theorem with a law among its hypotheses is conditional, and is named or documented as such (`…_of_laws`, "given …"). The catalog flags it.
- Headline docstrings say which premises are postulates and which are conditions.
- Algorithm properties are not presented as psychological explanations.
