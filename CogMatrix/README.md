# CogMatrix: laws of memory, model families, and the theory matrix

The direction in `../PROSPECTUS.md`, begun with retrieval. Laws are theory-neutral properties of a `Retriever` (CogLib's interface: study a stimulus; retrieve, for a probe, a distribution over stored stimuli). Model families are formalized once, with their parameters free. Each cell of the matrix is a theorem: the family has the law, under stated conditions, or it lacks it, by a counterexample.

```sh
cd CogMatrix && lake build     # builds CogLib too; core Lean only
python3 gen_matrix.py           # regenerates MATRIX.md from the cells
```

- `CogMatrix/Laws.lean`: the laws. Each is stated relative to a starting state `s0` and a set `U` of stimuli that may be studied.
  - `Certainty`: a stimulus just studied is retrieved for certain.
  - `Stability`: studying one stimulus leaves another's chance of retrieving itself unchanged.
  - `OrderFree`: the order of study doesn't matter.
  - `Recency`: of two stimuli studied last and equally similar to the probe, the later is retrieved more often.
  - `StoredOnly`: nothing is retrieved that was not studied.
- `CogMatrix/Families/Minerva.lean`: the global-matching family (MINERVA 2). Every study stores a trace; a probe activates all traces by the cube of their similarity, and memory returns the echo, their weighted sum read feature by feature.
- `CogMatrix/Families/Strength.lean`: the strength family (after the distributions-of-associations model). Strengths only add, the probe samples in proportion to strength discounted by mismatch, and a criterion and a search length apply. The other two families come from CogLib: discrimination nets (`netRetriever`) and activation (`actRetriever`, ACT-R with decay 1 and temperature 1).
- `CogMatrix/Matrix/*.lean`: the cells, one file per family. `Common.lean` is the small universe the counterexamples use: the eight 3-bit codes.
- [`MATRIX.md`](MATRIX.md): the matrix, generated.

## What the matrix shows

Every law is had by some family and lacked by another, and every family has its own row:
- **Discrimination** has certainty, stability and stored-only retrieval: learning is local and recognition is exact. It is order-dependent and has no recency.
- **Activation** has recency (the later of two stimuli is retrieved exactly twice as often) and stored-only retrieval.
- **Strength** is order-free (only totals matter), with stored-only retrieval.
- **Global matching** is order-free, and retrieves what was never studied: probed with the centre of three studied variants, it returns the centre (schema abstraction).

Global matching was added as a test of the first four laws, which were chosen with the other three families in view. They failed the test: on them, global matching has exactly the row of strength memory. Stored-only retrieval, the law that separates the two, says what is distinctive about global matching, that its output is a blend. It was found by asking what the laws missed. A fifth family is the next such test.

## What a cell does and does not say

- **A "has" cell is general.** It holds for every parameter choice satisfying the stated conditions:
  - discrimination: certainty needs pairwise noticeable stimuli; stability needs nothing;
  - activation: recency needs a positive discount and failure weight, from an empty memory;
  - strength: order-freedom and stored-only retrieval hold always;
  - activation: stored-only retrieval holds always;
  - global matching: order-freedom holds always.
- **A "lacks" cell is a single counterexample.** It shows the family does not have the law in general. It leaves open whether some region of the parameters has it. For example, strength memory with no generalization (`μ = 0`) may well have certainty. Mapping those regions is further work.
- **The laws were chosen with these three families in view.** Global matching was one test of that, and it forced a fifth law. Further families are further tests (`../OPEN_ISSUES.md` #17).
