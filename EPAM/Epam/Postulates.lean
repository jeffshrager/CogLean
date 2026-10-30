/-
EPAM's postulates, as choices from CogLib.

EPAM (Feigenbaum, RAND P-1817, 1959; Feigenbaum & Simon 1962) is stated as a
set of postulates (P-1817 §2.4). Each is an instance of a general construct
in CogLib. This file records which, quoting the postulate, so that every
theorem about EPAM can be traced to the postulates it uses.

**Microprocesses**

| Postulate | CogLib |
|---|---|
| D2 Selection: "uses codes ... to select images in a discrimination net" | `Cog.Item`, `Cog.Net`, `Net.select` |
| F1 Discrimination learning: "finding a unique terminal ... or creating such a terminal by growing the net at a point of confusion" | `Net.learn`; with redundancy, `Net.learnK` |
| F1a Redundancy: more than one difference noticed per confusion (the listing's P2) | `Net.learnK`, `Net.chain` |
| F1b Noticing order: "the scanning of codes for differences is controlled by a noticing order" | `Cog.NoticingOrder`, `firstDiff`, `diffs` |
| F2 Association: "storing with the image of X a cue code for Y; i.e., enough of the code for Y, so that D2 can use this cue code to select the image of Y" | `Cog.Cue`, `cueOf`, `cueFor` |
| R Responder: "apply D2 to X, obtain cue code from image of X, apply D2 to cue code" | `Net.CueSelects`, `Net.cueResults`; as a responder, `netResponder` |
| D8 Restoration: "add information to the cue code, sufficient to re-establish the link" | `Net.restoration` |
| (§3.5.1.2) a test with missing information branches at random | `CueSelects.guess0`, `guess1` |

**Macroprocesses**

| Postulate | CogLib |
|---|---|
| M0 Serial mechanism, M1 Unit processing time | `Cog.trials_at_least_items` |
| M2 Immediate memory | not yet used |
| M3 Anchor points: "items with features of uniqueness will be attended to first ... then ... items adjacent to those already learned" | the attention rule `Cog.before`, `Cog.attentionRank` (any anchors); `Cog.learnedOnTrial`, `Cog.errorsAt` (the ends as anchors) |

The EPAM-specific content is the combination, and the parameters left to
the experimenter: the codes, the noticing order, P2, and the learning
schedule of an experiment (`ListA.lean`, `Experiment.lean`, `Fig41.lean`).
-/

import CogLib

namespace Epam

open Cog

/-- EPAM's learner with one test grown per confusion (P2 = 1), as an
incremental learner: D2 for recognition, F1 for study, under noticing order
`order` (F1b). -/
abbrev learner (order : NoticingOrder) : IncrementalLearner Net Item := netLearner order

/-- EPAM's responder (R): a cue code retrieved through the net (D2), with
random branching where the cue is silent. -/
abbrev responder : Responder Net Cue Item := netResponder

end Epam
