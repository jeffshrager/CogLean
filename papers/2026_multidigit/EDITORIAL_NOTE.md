# Editorial note on the draft

The draft is `paper.tex` (build with `make`). It follows `notes/20261031_paper_drafting_instructions.md`.

It is written fresh rather than as an edit of `MultiDigit/paper/paper.tex`, which is untouched. Some passages are carried over and revised: the EPAM and DOA summaries, and the account of the blind simulation. Every number in it was checked against the current Lean files on 2026-10-31.

## Revision of 2026-10-31 (focused review)

Each technical point was checked against the Lean source. New theorems were added where the source fell short.

1. **Confident errors.** Equal backup use is not low backup use. New: `integrated_backup_rate` (the rate is `(1 - R_q)^n`) and `integrated_backup_le` (if `R_q ≥ r`, solver use is at most `(1 - r)^n`). The paper now separates the equality from the high-confidence setting.
2. **Comparison table.** The practiced-problem rows came from `ExampleACTR.lean`, which has an exact backup. The table now gives whole-retrieval errors and overall errors with the solver as separate rows. New: `setting_practiced_errors`:
   - EPAM ≈ .0073;
   - ACT-R ≈ .334, then ≈ .616 after studying 100 + 300.
   EPAM's value is unchanged after study by `MD.learning_preserves_trial`, which holds for any backup.
3. **Column signatures.** The one-digit signature is now stated as holding only when the other columns are exact; multiple and propagating errors are acknowledged. Exact facts are sufficient, not necessary. New: `compensating_errors` (units 10 and tens 4 still give 250).
4. **Unrealized hypotheses.** Reworded throughout as "unrealized in the tested learning histories". The paper notes that no impossibility theorem exists.
5. **Nonnegativity.** It was not enforced. New: `Dist.Nonneg` and lemmas through the composition (`nonneg_itrial`, `setting_valid`). The library-wide limitation is recorded in the paper and in OPEN_ISSUES #23.
6. **ACT-R applicability.** The paper now states that the hypotheses failing means the theorem does not apply. That does not mean ACT-R cannot behave similarly: it answers 200 with probability .43, but its solver use differs from the familiar problem's (383/1058 against 107/782).
7. **Peaking.** Now its own subsection (§3.3) and in the abstract. It pairs the general result (peaking never raises retrieval errors) with the counterexample on overt strategy use.
8. **Novelty.**
   - The abstract no longer says every theorem predated the composition.
   - The kinds table now separates library facts, compositional deductions, conditional results and values at settings.
   - The paper says none of these is yet an empirical finding.
9. **Discussion.** "What the approach bought" was rewritten as one paragraph on the four kinds of gain. The conclusion was shortened. The intro caution was condensed.

## Revision of 2026-10-31 (confusion-error predicate)

The confident-errors theorems now conclude one theory-neutral predicate, CogLib's `Phenomena.ConfusionErrorPattern`; `ConfidentErrors r` adds a bound on backup use. The paper's statement of `integrated_confident_errors` shows the predicate and its definition. New: `integrated_confident_errors_le`, `setting_confident_errors_bound`, and `setting_actr_not_pattern`. The last one proves that ACT-R lacks the pattern at the setting, so §5 now says "proved at this setting" where it said "fails". The talk's Lean slide and its ACT-R slide are updated to match.

## Revision of 2026-10-31 (one memory)

- **New §5.5, "One memory for whole problems and column facts"** (`MultiDigit/SharedMemory.lean`). It covers:
  - the reduction to the integrated model;
  - confident errors on digit pairs;
  - EPAM unchanged against ACT-R's drop, from .656 to .385.
- **New limitations:**
  - finger counting is an implausible column fallback for a multi-digit adder;
  - ACT-R appears without retrieval as use, which affects every ACT-R value.
- **Future work** now names retrieval that changes memory.
- **Removed:** the "Premises still unexplained" paragraph. Its items are covered in Limitations, apart from serial-learning anchors.
- **Talk:** a new slide, "One memory for both levels", and the limitations slide is updated.

## Revision of 2026-10-31 (Table 1 review)

The table was split into two:
- **Table 1** has the separate column-fact table.
- **Table 2** has one memory, with a control column: ACT-R with the five items studied, but the separate table.

Other changes:
- Solver rows now separate three things: whether the solver is invoked, whether it is correct given that it is invoked, and whether it is correct overall (the joint probability). The caption says the joint is the product of the other two, and this was checked exactly for every column.
- Noninterference is restricted to the fixed-backup configuration. For one memory it is now proved under a condition: the problem and its digit pairs were learned (`shared_learning_preserves_trial`). Unconditional noninterference is stated as not proved.
- New Lean theorems: `setting_epam_solver`, `setting_00_not_5`, `setting_act_control`, `shared_learning_preserves_trial`. Every number in Table 2 now cites a theorem.
- The talk's memory-swap slide uses the same row definitions. The one-memory slide is split into two: theorems, then numbers with the control.

## Revision of 2026-10-31 (reorientation toward general results)

This follows the revision guidance "Reorient the CogLean Paper Toward General Theoretical Results". The mathematics and the Lean code are unchanged.

**Restructured around the levels of results**
1. Components, formalized independently: EPAM, DOA, and general problem solving (now its own subsection).
2. The composition, including the bridge.
3. A theory-neutral phenomenon (new §5): `ConfusionErrorPattern` and `ConfidentErrors r`.
4. General deductions (§6): confident errors, solver independence, two sources, and one memory.
5. Classes of mechanisms (new §7): `confident_errors_of_laws`, the memory-law matrix, and what failing a law does and does not show.
6. The role of representation (new §8): representation-independent results; results that need properties of the encoding (Zeros, Magnitude, ColumnFacts in `FeaturePhenomena.lean`); and instance-specific results.
7. Concrete realizations (new §9): the five purposes of the numbers, and a qualitative EPAM/ACT-R table.

**Numbers moved to an appendix.** The exact-value tables, the setting and the numerical narrative are now Appendix B.

**Other changes**
- Abstract and introduction rewritten: a capability added for generalization over classes, an "aspiration" paragraph, and the numbers described as illustrative.
- §2's kinds of object now include representations.
- New Discussion subsection, "The scientific program", lists what has been demonstrated and what is still largely aspirational: weakest sufficient assumptions, necessary and sufficient conditions, equivalent representations, and general divergence theorems. It notes that the laws are shown sufficient, not necessary, and that universal results remain conditional.
- The kinds table gains a "class-level" row and representational properties.
- The conclusion now gives the central message.

The paper is 27 pages.

## Revision of 2026-10-31 (four precision edits)

1. The phenomena are stated over "answer and strategy-route distributions", not "observable outcomes". §5 now says that mechanism-independent is not the same as observable, and that applying the predicate to people requires measuring the route.
2. The qualitative table's caption now says EPAM's noninterference entry is also general (fixed backup).
3. In Table B1, the row "whole-problem retrieval" is now "whole-problem retrieval errors".
4. The expression (1 - R_q)^n is now stated with its condition, certain recognition as q, both in the kinds table and in §6.1.

 of scientific novelty

1. **Theorem composition across independently developed theories.** The integrated model's predictions are proved by reusing theorems established separately for three things:
   - EPAM's nets (CogLib);
   - DOA (StrategyChoice);
   - a decision-cycle solver (CogLib and MultiDigit).

   The chain behind `integrated_confident_errors` (§5.1) is the clearest case. As far as the review below found, earlier formal work verifies one architecture or one model at a time.
2. **Derived dissociations that neither theory makes alone, with every premise sorted.** There are three:
   - confident errors: wrong answers with no more backup use than the familiar problem;
   - whole-problem errors independent of solver quality;
   - two sources of error with different signatures.

   Each premise is labelled as a postulate, a condition (and whether it is derivable), or an illustrative setting.
3. **Predictions about classes of models, explained by laws.** The confident-errors pattern is proved for *any* memory with determinacy, certainty and stability. The theory matrix proves that EPAM's net has all three at every setting and ACT-R's memory has none. So the EPAM/ACT-R divergence is explained by a property of memory, not just observed at one setting.

## 2. The three most serious objections a skeptical cognitive scientist might raise

1. **"The interesting conditions are assumed, so the explanation is thin."** Confident errors need sharp associations, and the library assumes these rather than deriving them. The worked case's strengths are chosen.

   *Response in the draft:* sharpness is flagged as an unexplained empirical premise (§5.1, §7, Limitations), and confusion is derivable for learned nets. *Still a gap:* until sharpness is derived from DOA learning, the strongest result is conditional on its most important premise.
2. **"This is software engineering with extra steps; a well-designed simulation library could do the same."** A modular simulator can also swap memories and reuse components.

   *Response:* the difference is reuse of *results* (theorems quantified over every setting, and over every memory satisfying a law), not of code. The draft makes this argument in §1 and §4.3. *A reviewer may still ask* for an example where a proof established something a careful simulation study would have missed. The best candidates in the draft are the class-level law result and the counterexample to the DOA chapter's informal claim. The simulation finding that hypotheses were unreachable cuts the other way: it shows simulation catching what proof missed.
3. **"No contact with data."** There are no children's three-digit addition data, nothing is fitted, and confident errors are not shown to occur in people.

   *Response:* the paper is methodological, says so repeatedly, and never presents the numbers as predictions about children. *Still a gap:* a reader will want at least a pointer to whether confident whole-problem errors are observed in multi-digit arithmetic, and to how the predicted signatures (a familiar problem's sum versus a one-digit displacement) could be tested.

## 3. Claims that still need verification, empirical grounding, or literature review

**Bibliography**
- **Ganeriwala et al. (2025), SBP-BRiMS working paper.** I could not open the PDF (the host did not resolve). Its title, authors and venue come from a reference list in the 2026 chapter. The draft describes it only by its title ("proposed enabling formal verification of cognitive models"). Read it and describe what it actually does. (A web search returned a description, nuXmv and correctness and termination of small ACT-R and Soar models, but that description came from CogLean's own README, so it is circular and was not used.)
- **Ganeriwala et al. (2026), NASA Formal Methods.** Authors, pages and DOI were verified via Crossref. The description (Soar compiled to discrete-time Markov chains for PRISM) comes from the abstract as reported by search. The LNCS volume number is missing.
- **Stewart and West (2007).** Bibliographic details were verified via Crossref. The characterization ("rebuilt ACT-R in order to separate its core commitments from implementation detail and to explore alternative components") is from memory of the paper, not from reading it. Check it.
- **Langenfeld, Westphal and Podelski (2019).** The pages (618–624) come from a search listing. The 2021 paper's title and venue were verified via DBLP and eScholarship; it has no pages.
- **Ragni et al. (2018).** Verified from the paper's first page and DBLP; no page numbers.
- **Gall and Frühwirth (2017), the confluence test.** Cited as an arXiv preprint. It may have a published version, possibly at RuleML+RR 2017; check.
- **Finkel et al. (2025) and Macklem and Mili (2006).** Carried over or verified only at the venue level.
- **Milnes et al. (1992).** The report number and author list were verified from the catalog records. The draft's description ("covered the architecture completely but at a low level, and it could not be executed") comes from the report's own description and from a later DTIC report.
- **Verified via Crossref:** all other entries with DOIs.

**Positioning against model checking** (added 2026-10-31). The Discussion now separates simulation, probabilistic model checking and deductive proof, and frames the contrast as model verification versus theoretical deduction, with the approaches complementary. PRISM 4.0 and parametric model checking (Hahn et al. 2011) are cited and verified via Crossref. The rationale is in `notes/literature.md`.
- *Check:* how far the PRISM work handles parameters symbolically. The draft says only that PRISM *can*. It does not say that the Soar translation does.

**Novelty**
- The claim that CogLean's *combination* of emphases is new rests on a review of about fifteen works. Before submission, search further:
  - formalizations of psychological models in other proof assistants (Coq/Rocq, Isabelle, Agda);
  - category-theoretic or institution-theoretic approaches to composing models;
  - the "formal theory" literature in psychology beyond Guest & Martin and van Rooij & Baggio;
  - work on modular cognitive modelling environments (COGENT; the Python ACT-R and CCM lineage).
- The draft says that whether any single emphasis is novel is "a matter for a more complete review". Keep that hedge unless the review supports something stronger.

**Empirical grounding**
- Whether children or adults make confident whole-problem errors on multi-digit addition, and with what latencies. The draft makes no empirical claim, but a pointer to the error literature would help: for example, the buggy-arithmetic and repair-theory data on procedural errors, and any data on retrieval of multi-digit facts.
- The single-digit association rule (sum 4/5, next count 3/25, rest 1/100) is arbitrary. It is stated as arbitrary.

**Internal**
- The paper describes the repository as of 2026-10-31. Tag that commit and cite the tag, so that the theorem names in Appendix A stay valid.
- §8's "a small number of new lemmas" is qualitative. The earlier draft said three for the 18 predictions; the integrated model adds the lemmas in `Integrated.lean`. Give a count if a reviewer will care.
- The blind simulation predates the problem solver. The draft claims its results carry over by `Solver.bridge`. That holds for the column backup the simulator implements (the full procedure, exact carrying), not for the buggy procedures.

## Revision (relation to cognitive architectures)

Credited the cognitive-architecture tradition (Newell; Soar; ACT-R; the Common Model) as the main prior effort to make theory cumulative. CogLean is positioned as complementary: it accumulates machine-checked results, reusable deductively and stated across architectural commitments (confident errors / perseveration for classes of memories; laws sufficient, not necessary; no general equivalence or divergence claimed). The novelty claim is the combination only. Talk slides updated to match. Added refs laird1987, laird2012 / laird2017.

## Revision (Appendix C: Chris uses CogLean)

Added the author's worked-use appendix, with the suggested fixes: the raw-strength monotonicity result and the normalized counterexample are now proved in Lean (CogLib `reach_boost`, `exhausted_boost`; SC `correct_strengthening_never_raises_backup`, `dominant_strengthening_never_raises_backup`, `strengthening_below_criterion_can_raise_backup`, `strengthenNorm`, `normalized_strengthening_can_raise_backup`), so the appendix says "proved". The precise condition (correct answer above the criterion, or none) is stated; dominance implies it. Notes that the chapter renormalizes after elaboration (A4) but not after learning (A6); the .05 is twice an increment of .025; ties to Section 3.4's peaking example; cites Lean names; trimmed. Index row and an intro pointer added.

- Peaking precision edit (Section 3.3 and abstract): the counterexample is now described as an arbitrary redistribution (moving strength), distinguished from DOA's additive learning rule; added the learning results (additive rule never raises backup use above the criterion; renormalized rule can). "Corrected the theory" softened to "exposed an ambiguity and established which conclusions follow from which assumptions." Also softened the intro "Discovery" item and the Discussion ("corrections" → "clarifications").
