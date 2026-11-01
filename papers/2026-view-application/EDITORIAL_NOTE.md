# Editorial note on the draft

The draft is `paper.tex`, with an accompanying talk in `talk.tex`; `make` builds both. It is the second CogLean paper. It does not introduce CogLean, which the companion paper does (`../2026_multidigit/`). Its point is that the library carries over to a different domain: concept and theory formation by view application. It reuses CogLib's memory interface and laws, the confusion-error phenomenon, and the decision cycle. Every result cited was checked against the Lean source on 2026-11-01.

## Claims of novelty
1. **A second domain for a general library.** CogLean is designed as a general library; arithmetic was only its first worked example. Device learning reuses general components that the arithmetic example also used, by citing their proofs:
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

## Revision of 2026-11-01 (decomposed views and differentiation)

**New §6, "Composing views, and differentiation."** It covers:
- views built from parts (SET-A-NUMBER; NUMBER-IS-A-TIME and NUMBER-IS-A-DURATION), with `merge_keeps_unmentioned`, `one_view_not_enough`, `two_views_compose` and `revision_keeps_number`;
- the impossibility for every theory with a shared type (`same_parent_same_reading`, `never_both_shared`);
- splitting (`split_conservative`, `split_separates`);
- conflict-driven splitting (`viewSplitReviser`);
- the sessions (`no_split_session`, `split_session`): never both, with oscillation, against both, without oscillation.

**Other changes**
- The abstract, the shared-components table and the index now include this work.
- The discussion's "views act on types" point is now a result, not a limitation.
- Limitations now say that splitting is conflict-driven and not weighed against overwriting, and that commutation is proved only in instances.
- Appendix B has the new session table.
- The talk has three new slides ("Views from parts", "Why concepts must split", "Differentiation: split, then re-interpret") and updated concept-formation, limitations and take-home slides.

The paper is 13 pages; the talk is 19 slides.

## Revision of 2026-11-01 (splitting explained)

**In §6, three new paragraphs:**
- "A split, step by step", with Figure 1: the microwave before, after the split, and after re-interpreting the copy;
- "Aiming a view": why `retarget` is needed, and the change to view application's matching (a view frame is reserved for the theory frame of the same name); every earlier result checks unchanged;
- "What a split costs": conservative, but one more type to keep track of, which is why the learner splits only when forced.

**In the talk,** a new slide, "A split, step by step", with the same three panels and spoken notes covering aiming and cost.

The paper is 14 pages; the talk is 20 slides.

## Revision of 2026-11-01 (framing)
The draft had said in several places (the abstract, the introduction, the discussion, the conclusion and the talk) that CogLean was "built around arithmetic" and that this paper takes it to a domain it "was not built for". That is wrong. CogLean was designed from the start as a general, Mathlib-like library of reusable cognitive processes, on which any model can be built, provable and executable. Arithmetic was the first example worked out in it. All of these passages now say so. This paper is presented as a second worked example, in a very different domain, testing that design.
