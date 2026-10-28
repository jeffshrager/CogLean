# The laws are too specific

**Status:** open; a design problem for `CogLib/CogLib/Phenomena/RetrievalLaws.lean` and the matrix (`CogMatrix/`, `notes/MATRIX.md`).

## The worry

The constants in the worked examples (100 + 100, faces 000 and 110) are not the problem. The general theorems hold for all values, and the instances only show that their hypotheses can be met. The problem is the **laws themselves**: several are stated so narrowly that the matrix partly records how each law was phrased, not a cognitive property of the family.

## Law by law

| Law | How it is too specific | Consequence |
|---|---|---|
| Recency | Exactly two items, both new, studied last; a probe *exactly* equally similar to both (a count of mismatching binary features); a strict inequality. The shape was chosen partly because ACT-R's general proof could handle it, and that proof starts only from an empty memory. | It tests one narrow configuration. The general claim, "a more recent use never lowers retrieval", is not stated. |
| Certainty | Probability exactly 1. | Any memory with any noise lacks it. The "lacks" cells for ACT-R, strength and MINERVA come cheaply. |
| Stability | Exact equality of self-retrieval before and after studying another item. | Any interference at all, however small, violates it. |
| Determinacy | A single outcome, and syntactic (`= pure r`). | Again separates noiseless from noisy memories, not much else. |
| Order-freedom | Swaps only the last two study events, and requires the full retrieval distributions to be equal. | A narrow notion of order-independence. |
| Stored-only | Identity of binary codes. | Can't express "retrieves something close to a studied item". |

**Symptom:** certainty and stability have identical rows; only discrimination has either. Plausibly what separates EPAM from the other three on those columns is noise, not two distinct properties.

## Two further problems

- **Representation.** Every law presupposes binary feature codes, Hamming similarity (`mismatches`), and identity of codes. The laws are mechanism-neutral, not representation-neutral.
- **Fit to the families.** The laws were chosen, and stored-only was added after MINERVA, with these four families in view. "Every family has its own row" is partly by construction. Testing on new families helps, but each test that forces a new law also adds a law shaped by that family.

## What would fix it

1. **Graded, parameterized laws** in place of exact ones:
   - ε-certainty: a just-studied item retrieves itself with probability at least 1 − ε;
   - δ-stability: studying another item changes self-retrieval by at most δ;
   - recency as a monotonicity: moving any use later in time never lowers retrieval.

   A cell then becomes a **threshold** ("ACT-R has ε-certainty exactly when ε ≥ θ/(w + θ)"), not has/lacks. This also answers the open question of parameter regions (`notes/OPEN_ISSUES.md` #17), and it shows which "lacks" cells were only about noise.
2. **Monotonicity and ordering laws** rather than equalities. Frequency: an extra study of y never lowers P(y | y). Similarity: more mismatches never raise retrieval. These are closer to how regularities are stated in psychology, and they survive small noise.
3. **An abstract similarity relation** in place of Hamming distance on binary codes, so the laws assume less about representation.
4. **Robustness checks on the matrix.** For each cell, does the verdict survive a slight relaxation of the law? A cell that flips under an ε-relaxation reflects the law's form, not the family.
5. **Logical relations between laws.** Prove implications and incompatibilities (as already done for recency and order-freedom), so it is clear which columns are independent.

Items 1 and 2 are the core. They turn the matrix from "does the family satisfy this exact property?" into "how strongly, and under which parameters, does it satisfy this kind of property?", which is what the scientific claims need.

## What stays valid

- **Every proved cell stays true.** Exact laws are special cases of graded ones (ε = 0, δ = 0).
- **The law-derived theorems remain correct as stated:** `confident_errors_of_laws`, `curve_flat`, and the AB/BA theorems. They will need graded versions to apply to noisy memories, and so, by the evidence row's judgment, to people. A graded confident-errors theorem is already noted as open.
