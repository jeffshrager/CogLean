# Editorial note on the draft

The draft is `paper.tex` (build with `make`). It follows `notes/20261031_paper_drafting_instructions.md`.

It is written fresh rather than as an edit of `MultiDigit/paper/paper.tex`, which is untouched. Some passages are carried over and revised: the EPAM and DOA summaries, and the account of the blind simulation. Every number in it was checked against the current Lean files on 2026-10-31.

## 1. The three strongest claims of scientific novelty

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
