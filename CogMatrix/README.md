# CogMatrix: laws of memory, model families, and the theory matrix

The direction in `../notes/PROSPECTUS.md`, begun with retrieval. Laws are theory-neutral properties of a `Retriever` (CogLib's interface: study a stimulus; retrieve, for a probe, a distribution over stored stimuli). Model families are formalized once, with their parameters free. Each cell of the matrix is a theorem: the family has the law, under stated conditions, or it lacks it, by a counterexample.

```sh
cd CogMatrix && lake build     # builds CogLib too; core Lean only
python3 gen_matrix.py           # regenerates ../notes/MATRIX.md from the cells
```

`gen_matrix.py` builds the package, then checks every cell in Lean:
- **Its verdict is read from its statement**, not its name (`cell_shape.lean`): a law or the negation of one, and whether the family's parameters are bound by the theorem or fixed. There are four verdicts:
  - **has**: the law holds at every setting, within the hypotheses the theorem states;
  - **never**: the law fails at every setting;
  - **lacks**: it fails at one setting (a counterexample);
  - **can hold**: it holds at one setting.

  The name must agree: `<law>`, `not_<law>` (one setting) or `never_<law>` (every setting). Otherwise the script stops.
- **Its axioms are checked by `#print axioms`.** A cell that depends on `sorry` (`sorryAx`), anywhere underneath it, or on any axiom beyond `propext`, `Classical.choice` and `Quot.sound` is marked **unproved**, and the script exits with an error.

So a generated matrix certifies that every verdict is proved and says what its theorem says. Only **has** and **never** speak for the whole family, so only they can be refuted by evidence.

- The laws are in CogLib (`../CogLib/CogLib/Phenomena/RetrievalLaws.lean`), next to the `Retriever` interface. Each is stated relative to a starting state `s0` and a set `U` of stimuli that may be studied.
  - `Certainty`: a stimulus just studied is retrieved for certain.
  - `Stability`: studying one stimulus leaves another's chance of retrieving itself unchanged.
  - `OrderFree`: the order of study doesn't matter.
  - `Recency`: of two stimuli studied last and equally similar to the probe, the later is retrieved more often.
  - `StoredOnly`: nothing is retrieved that was not studied.
  - `Determinate`: every retrieval has a single outcome. Structural as stated, but each "lacks" cell shows two outcomes with positive probability, so it fails any probabilistic version too.
- `CogMatrix/Families/Minerva.lean`: the global-matching family (MINERVA 2). Every study stores a trace; a probe activates all traces by the cube of their similarity, and memory returns the echo, their weighted sum read feature by feature.
- `CogMatrix/Families/Strength.lean`: the strength family (after the distributions-of-associations model). Strengths only add, the probe samples in proportion to strength discounted by mismatch, and a criterion and a search length apply. The other two families come from CogLib: discrimination nets (`netRetriever`) and activation (`actRetriever`, ACT-R with decay 1 and temperature 1).
- `CogMatrix/Matrix/*.lean`: the cells, one file per family. `Common.lean` is the small universe the counterexamples use: the eight 3-bit codes. Where a family has both a counterexample (`not_<law>`) and a general negation (`never_<law>`), the matrix shows the general one; the counterexample stays as a worked case.
- [`../notes/MATRIX.md`](../notes/MATRIX.md): the matrix, generated. It also shows a row for people, from `evidence.json` (a judgment of what experiments show, with sources, kept apart from the theorems), and how well each family fits it.

## What the matrix shows

Every law holds for some family and fails for another, and every family has its own row:
- **Discrimination** has certainty, stability and stored-only retrieval: learning is local and recognition is exact. It is order-dependent and has no recency.
- **Activation** has recency (the later of two stimuli is retrieved exactly twice as often) and stored-only retrieval. It *never* has certainty, stability, order-freedom or determinacy, at any setting with a positive failure weight: these four negations are general proofs, not just counterexamples.
- **Strength** is order-free (only totals matter), with stored-only retrieval. It *never* has recency.
- **Global matching** is order-free, and *never* has recency. It retrieves what was never studied: probed with the centre of three studied variants, it returns the centre (schema abstraction).

Global matching was added as a test of the first four laws, which were chosen with the other three families in view. They failed the test: on them, global matching has exactly the row of strength memory. Stored-only retrieval, the law that separates the two, says what is distinctive about global matching, that its output is a blend. It was found by asking what the laws missed. A fifth family is the next such test.

Order-free memories never have recency for a general reason. Studying two items in either order leaves the same retrieval, so neither order can favour the later item (`Laws.not_recency_of_orderFree`, in CogLib). So strength and global matching never have recency, at any setting, wherever recency can be tested.

## What the laws buy: confident errors

`Cog.RR.confident_errors_of_laws` (`CogLib/Process/RecognizeRetrieve.lean`) derives confident errors in the recognize-retrieve composition from three laws: determinacy, certainty and stability. Any memory with all three gives every stranger who can be taken for a studied item a confidently wrong answer, with no extra backup use. In the matrix, only discrimination has all three. Face naming derives its confident misnaming this way, from EPAM's cells (`Experiments/FaceNaming.lean`, `epam_confident_misnaming_of_laws`).

The evidence row judges that people lack certainty. So the law-level route to confident errors, as stated, does not apply to people. If people make confident errors, a graded version (certainty and determinacy with high probability, not probability 1) is what would explain them. That theorem is still to be proved.

## Against the evidence

As recorded in `evidence.json`:
- people lack certainty and order-freedom, and have recency;
- stability is mixed: it fails in recall but may hold in recognition;
- stored-only retrieval is mixed. Calling an unseen prototype old doesn't show it was retrieved; discrimination and strength memory call it old by retrieving a studied item.

Against these, a cell is **refuted** when it speaks for the whole family and goes the other way. That can happen two ways: the family *never* has a law people have, or it *has* at every setting a law people lack. A cell is only **open** when it is a counterexample at one setting and people have the law, since another setting might have it too. As things stand:
- activation fits every settled entry;
- discrimination is refuted on certainty (it has it at every setting, and people lack it); its recency conflict is only open, since `not_recency` is one setting;
- strength and global matching are each refuted twice. They are order-free at every setting, and people aren't; and they never have recency, and people have it.

But each judgment rests on an unformalized bridge from what experiments measure (reports) to what laws are about (retrieval), and the stored-only bridge is the one that would decide. Decision and report components are the missing piece. ACT-R with blended retrieval is still a natural next family. See `../notes/PROSPECTUS.md`, "What is true here", for what this row is and is not.

The discrimination family here is EPAM's recognition net. EPAM's paired-associate memory, with cue codes (`CogLib/Process/Association.lean`), shows retroactive interference (`netResponder_retroactiveInterference`). So it would not have stability: the law depends on which part of a theory is put in the matrix.

## What a cell does and does not say

- **A "has" cell is general.** It holds for every parameter choice satisfying the stated conditions:
  - discrimination: certainty needs pairwise noticeable stimuli; stability needs nothing;
  - activation: recency needs a positive discount and failure weight, from an empty memory;
  - strength: order-freedom and stored-only retrieval hold always;
  - activation: stored-only retrieval holds always;
  - global matching: order-freedom holds always.
- **A "never" cell is general too.** It holds for every parameter choice meeting its conditions:
  - activation: certainty, stability, order-freedom and determinacy fail for every positive failure weight (and nonnegative discount), on any `U` with one or two stimuli;
  - strength and global matching: recency fails for every choice of parameters, from every state, wherever recency can be tested.
- **A "lacks" cell is a single counterexample.** It shows the family does not have the law in general. It leaves open whether some region of the parameters has it. For example, strength memory with no generalization (`μ = 0`) may well have certainty. Mapping those regions, or turning a "lacks" into a "never", is further work. Eight cells are still of this kind.
- **The laws were chosen with these three families in view.** Global matching was one test of that, and it forced a fifth law. Further families are further tests (`../notes/OPEN_ISSUES.md` #17).
