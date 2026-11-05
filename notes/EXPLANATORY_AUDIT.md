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
| `RR.confident_errors_graded` | the same postulates; conditions: retrieval of q, and of x as q, with probability at least 1 - δ; sharp associations; well-formedness | compositional | The pattern within 2δ. Certainty is no longer needed, so memories whose retrieval is never certain can be instances. |
| `RR.act_priming_confident_errors` | postulates: ACT-R's activation retrieval with priming (as a factor on a chunk's weight), sharp-criterion retrieval, the backup; conditions: x partially matches q, q is stored, sharp associations | compositional | A second explanation of confident errors, from partial matching and priming rather than discrimination. The priming factor is a parameter: what primes q (a recent trial, the context) is not derived. The two explanations predict different error patterns: EPAM's follow shared features, primed ACT-R's follow the context. |
| `Act.spaced_not_powerLaw`, `spaced_diminishingRelative`, `massed_scaleRatio` | postulates: ACT-R's base level (decay 1) and latency rule; conditions: the practice schedule and test time | derived | The curve's shape is not in the postulates. The same mechanism gives an exact power law (massed, tested later) or a logarithmic curve with every qualitative signature of a power law (spaced). So "ACT-R produces the power law" depends on a condition, the schedule. Decay 0.5, ACT-R's usual value, needs real powers and is not done. |
| `mix_diminishingRelative`, `mix_not_shiftRatio` | none beyond the curves: two exponential learners, averaged | derived | Not a mechanism result but a relation between phenomena: averaging alone produces a power-like signature. It is why group curves can't decide between power and exponential learning in individuals (Estes 1956; Heathcote, Brown & Mewhort 2000). |
| `not_dissociates` | assumed property: membership nondecreasing in typicality | derived, conditional | — |
| `achieve_sound`, the merge theorems, `activation_append`, `step_impasse_iff`, `step_no_impasse` | the algorithms' definitions | definitional | Properties of mechanisms, not psychological predictions. They are needed, but they explain nothing on their own. |

## Theories

| Result | Premises | Distance | Comment |
|---|---|---|---|
| EPAM's non-interference, criterion, oscillation, retroactive inhibition | postulates: nets, cue codes, learning | derived | Oscillation and retroactive inhibition come from cue codes outgrown by the net, which is not stated in the postulates. |
| `SC.counting_error_share` (DOA) | postulates A1–A5 | derived | The chapter's "nonintuitive prediction": the associations don't affect the counting error share. |
| `SC.retrieval_prob`, `retrieval_error_share` | postulates A2–A3 | close | The algebra of sampling. |
| `SC.peaking_can_raise_overt_use` | postulates; one setting | derived (counterexample) | Refutes an informal claim of the chapter at one setting. |
| `Cog.exhausted_boost`, `SC.correct_strengthening_never_raises_backup`, `SC.dominant_strengthening_never_raises_backup` | postulates; condition (correct answer above the criterion, or dominant) | derived, general | Learning under raw strengths never raises backup use; the condition is shown needed by `SC.strengthening_below_criterion_can_raise_backup`. |
| `SC.normalized_strengthening_can_raise_backup` | an alternative learning rule; one setting | derived (counterexample) | Separates raw from renormalized learning on the same regularity. |
| `MD.confident_errors` | postulates: EPAM and DOA; conditions: the net confuses x with q, sharp associations | compositional | Confusion is derived for learned nets elsewhere (`near_miss_*_learned`). Sharp associations remain a condition. |
| `MD.column_error_is_doa_error` | postulates: column backup and DOA facts | compositional | — |
| `Shared.memFact_self`, `strial_reduces`, `strial_net_reduces` | postulates: the integrated model's, with column facts from the same memory; condition: each digit pair recognized as itself | compositional | The separate DOA table is a special case of one memory, so the integrated model's theorems carry over. |
| `Shared.shared_learning_preserves_trial` | EPAM's learning; condition: the problem and its three digit pairs were learned | compositional, conditional | `MD.learning_preserves_trial` holds the backup fixed; with one memory, learning could change the backup, so noninterference transfers only under this condition. Unconditional noninterference for the shared model is not proved. |
| `Shared.column_confident_errors` | the same; conditions: a digit pair confused with another, sharp associations | compositional, conditional | Confident errors one level down, inherited from `RR.confident_errors` with no new proof. |
| `Shared.setting_act_values`, `setting_act_pairs`, `setting_act_control` | ACT-R's memory, one setting | setting | Sharing a memory lowers ACT-R's solver accuracy (pairs confused with pairs); EPAM's values are unchanged (`setting_epam_values`). The control (five items, separate table) separates the two changes: the extra items alone raise correct answers (.238 to .267); the solver's use of the memory lowers them (.157). |
| `Integrated.setting_actr_not_pattern` | ACT-R's memory at the illustrative setting | setting, counterexample | With ACT-R's memory the trial lacks `ConfusionErrorPattern` (backup use 383/1058 against 107/782). One setting, not every setting. |
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
| `revise_same_of_determinate` (`Process/ViewRevision`), `view_of_determinate` | the law of determinacy; the loop does not change memory | class-level, conditional | Perseveration for every determinate memory: the cue brings in the same view at every failure. Close to the law (determinacy says retrieval is a single outcome); the content is that, in the revision loop, this becomes repetition of a failed interpretation. |
| `view_confusion_pattern` | view retrieval; conditions: certain confusion of two cues, the shared view right for one and wrong for the other | compositional, conditional | The confusion-error pattern of arithmetic, for a different mechanism. The conditions carry most of the content. |
| `same_parent_same_reading`, `never_both_shared` | denotations that read an action's type only through its slots | general (first); impossibility, for every theory of the form (second) | Views act on types, so actions of one type cannot be told apart by any view on it. Close to the definitions, but it is what makes differentiation necessary rather than optional. |
| `split_conservative`, `split_separates` | the split copies the type exactly; freshness | general | A split changes nothing by itself; it only makes a separate re-interpretation possible. |
| `merge_keeps_unmentioned` | view application's merge | library fact | Composition of views; commutation is open in general. |
| `DeviceLearning.Diff.no_split_session`, `split_session` | the microwave, EPAM's net, one setting | setting | Witnesses: without splitting, never both and oscillation; with conflict-driven splitting, both and no oscillation. |
| `DeviceLearning.epam_two_cues`, `act_two_cues`, `epam_label_only`, `act_label_only` | the microwave, the two memories, one setting | setting | Witnesses: EPAM perseverates for certain with one cue, ACT-R escapes with probability about .90. |

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
