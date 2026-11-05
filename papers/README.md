# Papers

Manuscripts about CogLean, one directory each.

- `2026-coglean-intro/`: *CogLean: Towards a Cumulative, Machine-Checked Theory of Cognition*. The introduction to CogLean: its organization; theorems as explanations, with the map from scientific notions to Lean; one small example (confident errors in naming people: EPAM, the laws, ACT-R, and a second explanation by priming); imprecise mechanisms and phenomena (learning curves: the power law unbundled, averaging, ACT-R's practice schedules); kinds of results; the status of proofs; relation to other formal work and to architectures; directions; and Chris and Robin (Appendix A). `make` builds `paper.pdf`, `talk.pdf` and `talk-notes.pdf` (with a spoken paragraph per slide).

- `2026_multidigit/`: *Composing Cognitive Theories in CogLean: Multi-Digit Addition*. The first extended test: EPAM, DOA and a problem solver composed into an executable model of three-digit addition, with its consequences derived largely from the components' theorems. It cites the intro paper for the framework. Same build and files as above. `EDITORIAL_NOTE.md` lists its novelty claims, the objections to expect, and what still needs checking. Drafted from `notes/20261031_paper_drafting_instructions.md`; split from the intro paper on 2026-11-05 (the combined version is tagged `20261105-per-pete-presentation`).

- `2026-view-application/`: *Concept Formation by View Application: A Second Domain on Shared Foundations in CogLean*. It does not introduce CogLean (see `2026-coglean-intro/`); it takes the library to concept and theory formation (view application, Shrager 1987, on a microwave), reusing CogLib's memory interface and laws, the confusion-error phenomenon and the decision cycle. Same build and files as above.

The earlier multi-digit paper, which predates the integrated model, is in `MultiDigit/paper/`.
