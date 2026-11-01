# Editorial note on the draft

The draft is `paper.tex`, with an accompanying talk in `talk.tex`; `make` builds both. It is the second CogLean paper. It does not introduce CogLean, which the companion paper does (`../2026_multidigit/`). Its point is that the library carries over to a different domain: concept and theory formation by view application. It reuses CogLib's memory interface and laws, the confusion-error phenomenon, and the decision cycle. Every result cited was checked against the Lean source on 2026-11-01.

## Claims of novelty
1. **A domain the library was not built for.** Device learning reuses components built for arithmetic by citing their proofs:
   - the retriever interface, EPAM and ACT-R;
   - the laws of memory and the memory matrix;
   - `ConfusionErrorPattern`;
   - the decision cycle.
2. **The 1987 account completed in two places.** Which view is applied is decided by retrieval through a swappable memory. When the theory is revised is decided by the impasse structure of problem solving.
3. **A phenomenon transferred across domains** without bridging the mechanisms (`view_confusion_pattern`).
4. **A class-level result about concept formation.** Perseveration holds for every determinate memory (`revise_same_of_determinate`).

## Objections to expect
- **"The transferred pattern is close to its premises."** Yes, and the paper says so. Its interest is that the predicate needed no change.
- **"The microwave is a toy."** Yes. It is a witness. The paper puts the numbers in an appendix and makes no claims about people.
- **"Where is the learning?"** Memory does not learn during revision, and types are not split. Both are stated as limitations. Type splitting is where conceptual-change theory ("differentiation") would bite.
- **"No data."** The instructionless-learning protocols (Shrager & Klahr 1986) are named as the first source.

## To verify
**References.** The references marked "Unverified" in `refs.bib` need checking:
- Carey (1985);
- Minsky (1975) chapter pages;
- Gentner & Stevens (1983).

All others were checked against Crossref on 2026-11-01. The reference list is almost entirely different from the companion paper's. It is oriented to concept formation and theory change.

**Characterizations of the literature** are from memory and should be checked:
- Murphy & Medin's theory-based concepts;
- Carey's restructuring and differentiation;
- Rumelhart & Norman's three modes of learning;
- Kieras & Bovair's device models;
- Luchins's *Einstellung*.

**Tag.** Tag the repository commit the paper describes.

## Lean results cited
- CogLib `Process/ViewApplication`: `merge_keeps_view`, `merge_view_wins`, `merge_keeps_unmatched`, `merge_reparents`.
- `ViewApplication/`: `table4_reproduced`; `after_exact`, `after_no_overextension`, `typicality_unchanged`, `dissociation`; `naive`, `primed`.
- CogLib `ViewRetrieval`: `confusion_gives_neighbours_view`, `view_of_determinate`, `view_confusion_pattern`.
- CogLib `TheoryRevision`: `impasse_iff_fails`, `correct_theory_stable`.
- CogLib `ViewRevision`: `viewReviser_theory`, `revise_same_of_determinate`.
- CogLib `TheoryExecution`: `predict_congr`.
- CogLib `Phenomena/TheoryChange`: `gardenPath`, `perseverates`.
- `DeviceLearning/Session`: `net_facts`, `act_graded`, `view_predictions`, `epam_confusion_pattern`, `epam_revisions_same`, `epam_two_cues`, `act_two_cues`, `epam_label_only`, `act_label_only`, `duration_kept`.
