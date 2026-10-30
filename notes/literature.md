# Literature

Work related to CogLean's approach: deriving tests from theories' core assumptions, comparing theories by proof, and formalizing cognitive architectures.

## Fisher, Houpt, Larue & Schmidt (2024): critical tests of ACT-R from core assumptions

Fisher, C. R., Houpt, J., Larue, O., & Schmidt, K. D. (2024, June). *Deriving critical tests of ACT-R using systems factorial technology with global model analysis.* Paper presented at Virtual MathPsych/ICCM 2024. https://mathpsych.org/presentation/1440#/abstract

**Abstract.**

> Cognitive architectures (CAs) are unified theories of cognition which describe invariant properties in the structure and function of cognition, and how sub-systems (e.g., memory, vision) interact as a coherent system. An important role of CAs is integrating findings across many domains into a unified theory and preventing research silos. One downside of CAs is that their breadth and complexity create challenges for deriving critical tests of core architectural assumptions. Consequentially, it is often unclear to what extent empirical tests of CAs are driven by core architectural vs. auxiliary assumptions. To address this issue, we developed a methodology for deriving critical tests of CAs which combines systems factorial technology (SFT; Townsend & Nozawa, 1995) and global model analysis (GMA), forming what we call SFT-GMA. In SFT-GMA, GMA is performed within an SFT model space of qualitative model classes spanning four dimensions: architecture, stopping rule, dependence, and workload capacity. Constraints on the model space are derived from core architectural assumptions which may provide a basis for critical tests. To demonstrate the utility of SFT-GMA, we applied it to the ACT-R cognitive architecture (Anderson et al., 2004). Despite many degrees of freedom in the specification of parameters values, production rules, and declarative memory representations, SFT-GMA revealed that ACT-R's core architectural assumptions impose testable constraints on the SFT model space. In particular, ACT-R is incompatible with most parallel SFT models of perceptual processing. We believe that the use of theorem-based methods such as SFT-GMA have the potential to stimulate theoretical progress for CAs. The views expressed in this paper are those of the authors and do not reflect the official policy or position of the Department of Defense or the US Government. This work was supported by the Air Force Research Laboratory (FA8650-22-C-1046). Approved for public release; distribution unlimited. Cleared 12/21/2023; Case Number: AFRL-2023-6387.

**Journal version.** Fisher, C. R., Houpt, J. W., Larue, O., & Schmidt, K. (2025). Using systems factorial technology for global model analysis of ACT-R's core architectural assumptions. *Journal of Mathematical Psychology, 125*, 102924. https://doi.org/10.1016/j.jmp.2025.102924. A local copy is at `../papers/2025-Fisher-etal-JMP1-s2.0-S0022249625000252-main.pdf`, outside the repo. Simulation code: https://github.com/itsdfish/ACTR_SFT.jl (Julia).

**What the paper does.**
- **Space.** 45 SFT model classes, from crossing architecture (serial, parallel, coactive), stopping rule (AND, OR), stochastic dependence (independent, inhibitory, facilitatory) and workload capacity (limited, unlimited, super).
- **Auxiliary versus core.** Auxiliary: ACT-R 7's 105 parameters, 22 hooks, optional modules, the production rules and chunks, and the processing-time distributions. Core: eight assumptions they propose, since there is no official list:
  1. discrete production cycles;
  2. chunks;
  3. modularity with encapsulation;
  4. no redundant modules;
  5. one production fires at a time;
  6. a module handles one request at a time;
  7. a buffer holds at most one chunk;
  8. a perceptual module encodes one stimulus per chunk.

  They state each assumption in set notation, as "the set of models violating it is empty".
- **Theorems.** Three, proved in prose by enumerating the pathways to parallelism and showing that each conflicts with a core assumption:
  1. within one modality, perceptual processing is serial;
  2. across modalities, it cannot be coactive;
  3. parallel cross-modal processing must be independent and unlimited-capacity (UCIP).
- **Tables.** Tables 1 and 3 mark each of the 45 classes as producible or ruled out, with the ruling theorem as a superscript. They have the same shape as a CogMatrix column, with each verdict naming the result behind it. Their ✗ ("cannot produce", under any auxiliary choices) is CogMatrix's **never**, and their ✓ ("can produce") is closer to **can hold** than to **has**.
- **Tests against data.**
  - Within one modality (two dots), published double-factorial results show parallel processing (Townsend & Nozawa 1995; Eidels et al. 2015; Howard et al. 2021). Wenger & Rhoten (2020) found a shift to parallel super-capacity with training.
  - Across modalities, Yang et al. (2018) found parallel exhaustive processing with super-capacity or facilitation.
  - Both results contradict ACT-R, so at least one of its core assumptions fails: 4, 5, 6 or 8 for the first, and 3, 6, 7 or 8 for the second.
- **Relaxing assumptions.**
  - Dropping encapsulation (3) lets ACT-R produce every cross-modal pattern.
  - Dropping one-stimulus-per-chunk (8) lets it produce every within-modality pattern.
  - Dropping both makes ACT-R unfalsifiable in this space.

  It is a robustness analysis of the verdicts over the core list.

**Relation to CogLean.**
- **The same aim and shape.** Separate what follows from a theory's *core* from what depends on auxiliary choices, and record verdicts per qualitative class with the result behind each. Their tables are one column of a matrix whose rows are SFT classes; CogMatrix has laws as rows and several families as columns.
- **Proofs.** Theirs are careful prose case analyses over informally stated assumptions; CogLean's are machine-checked. Their Theorem 1 argument (each pathway to parallelism contradicts some assumption) is a natural candidate to formalize: it needs a small model of modules, buffers and production cycles, not ACT-R's activation equations.
- **Domain.** They constrain the *timing structure* of perception, seen in response-time distributions. CogLean constrains what *declarative memory retrieves* and how study changes it. The two don't overlap yet: their analysis says nothing about retrieval content, and CogLean has no time.
- **Link to data.** This is their strength. SFT comes with a paradigm (the double factorial design), diagnostics (SIC and the capacity coefficient), an assumption that makes them interpretable (selective influence), and published data. CogLean's evidence row is judgment, with bridges.
- **Base-level learning, Section 8.2.** A reviewer suggested two core properties of base-level activation: retrieval time weakly decreases with the number of uses, and weakly increases with the time since the last use. The authors note that a critical test is hard, because these depend on how other activation terms (spreading activation, for instance) are constrained. Footnote 12 cites edge cases where the standard form violates them (Fisher, Houpt & Gunzelmann 2018). These are the monotonicity laws that `notes/20261028_law_specificity.md` proposes, for probability rather than time. A concrete first link: prove them for `actRetriever`, and show which other families have them.
- **Their limitations are ours.**
  - The possible/impossible split gives strong evidence against a theory but no graded support. That is our has/never problem, and the graded laws are the fix. CogMatrix now separates claims about every setting (**has**, **never**) from claims about one setting (**lacks**, **can hold**), and only the former can refute a family. That is the asymmetry SFT-GMA relies on.
  - Duhem–Quine: statistical tests bring their own auxiliary assumptions, just as CogLean's bridges do.
  - SFT is neutral on representation, while CogLean's laws are tied to one representation.
- **Future work they propose:** applying SFT-GMA to other architectures to compare them. That is CogLean's comparison of families, for processing structure.

Presented in `presentations/coglean-overview` and `coglean-story` (slide "A related approach: SFT-GMA").

## Conceptual combination

Formalized in `Concepts/` (see its README).

- **Smith, E. E., Osherson, D. N., Rips, L. J., & Keane, M. (1988).** Combining prototypes: A selective modification model. *Cognitive Science*, 12, 485–527. Local copy: `../papers/1988-SmithandOsherson-1-s2.0-0364021388900110-main.pdf`. Prototypes with diagnosticity and votes; typicality by Tversky's contrast rule; an adjective shifts its attribute's votes and boosts its diagnosticity. Postulates SO1–SO4; the figures are reproduced exactly.
- **Hampton, J. A. (2007).** Typicality, graded membership, and vagueness. *Cognitive Science*, 31, 355–384. Local copy: `../papers/2007-Hampton-Typicality.pdf`. The threshold model: typicality and membership are both nondecreasing functions of one similarity; membership by his Eq. 8. Postulate H1. With it, S&O's conjunction effect becomes over-extension, which fuzzy logic's min rule forbids.
- **Shrager, J. (1987).** Theory change via view application in instructionless learning. *Machine Learning*, 2, 247–276. Local copy: `../papers/1987MLVA.pdf` (a scan, no text layer). View application combines abstract knowledge structures into a learner's theory. Formalized in `ViewApplication/`: Table 4 reproduced; applied to number concepts, it removes over-extension and keeps typicality, the dissociation Armstrong, Gleitman & Gleitman (1983, *Cognition* 13, 263–308; not in `../papers/`) report.

## Semantic memory

Formalized in `SemanticMemory/` (see its README).

- **Collins, A. M., & Quillian, M. R. (1969).** Retrieval time from semantic memory. *JVLVB*, 8, 240–247. Local copy: `../papers/` (saved as `Unconfirmed 811174.crdownload`; complete, 8 pages, a scan). The hierarchical network; postulates CQ1–CQ3; Fig. 1 reproduced.
- **Smith, E. E., Shoben, E. J., & Rips, L. J. (1974).** Structure and process in semantic memory: A featural model for semantic decisions. *Psychological Review*, 81, 214–241. Local copy: `../papers/1974-Structure_and_process_in_semantic_memory_A_featura.pdf` (a scan). Defining and characteristic features; the two-stage feature comparison model; postulates FC1–FC2.
- **Collins, A. M., & Loftus, E. F. (1975).** A spreading-activation theory of semantic processing. *Psychological Review*, 82, 407–428. Local copy: `../papers/1975_A_Spreading_Activation_Theory_of_Semantic_Processi.pdf` (a scan). Formalized in part (CogLib `Process/SpreadingActivation`): assumptions 1-4 (spread in a decreasing gradient, release, decay as bounded depth, summation); used for view selection (`ViewApplication/Selection.lean`). The decision process (assumptions 8-13) is not yet formalized.

