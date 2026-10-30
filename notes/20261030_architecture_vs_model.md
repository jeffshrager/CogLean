# Architecture versus model: a question, and the answer drafted (2026-10-30)

## The question (paraphrased)

A colleague's question sets out the duality.
- **Architectures** are task-invariant, but cannot usually be applied to a task directly.
- **Task models** are the opposite: they apply directly, but are not task-invariant.
- The duality is not inherent. We hand-craft task models out of expedience, whereas nobody specifies task models for our brains. Instructions come in as data, not program.
- Connectionist models learn from data. Methods such as instruction-following and instance-based learning narrow the gap.

Can CogLean's analytical capabilities guide further along that path?

## The formal answer ("the party line")

In Lean, the difference between architecture and model is **the difference between what a theorem quantifies over and what it fixes**.
- **Task knowledge as data** (rules, facts, instructions, experience given as arguments) is quantified over. A result that holds for all such data is architectural.
- **Task knowledge as program** (definitions written for one task) makes a result model-specific.
- The type checker enforces this, so how task-invariant a result is can be read off its statement.

This gives a path:
1. **Measure** how much of each prediction depends on task definitions rather than data.
2. **Move** task knowledge into data:
   - in the CMC formalization, procedural memory is already part of the state;
   - in CogLean, the view-application examples are pure data run by one generic process, and EPAM's learning results are fully general over lists;
   - elsewhere the library is uneven.
3. **Prove learnability theorems**: for every task in a class, and any instruction or experience of a given form, the architecture reaches competence from a task-independent starting state. Each one retires hand-built task models for that class. Instance-based learning and instruction-following are the mechanisms such theorems would be about. Laird's specification lists one for Soar as future work; CogLean's candidates are in `LEARNABILITY.md`.

## The practical answer (the user's view)

In practice, models will be built by giving Claude a paper and CogLean, and asking for the paper as a CogLean model. That conversation will settle at what level the model belongs, guided by the paper and by what is already in CogLib, the task-general layer, where most of the CMC would also live. In the best case the model is constructible from CogLib and the rest is data. More often the new work forces a generalization of CogLib, and the model keeps evolving toward generality.

**Evidence that this is already happening.** This month, each paper either went in as data or forced a CogLib generalization:
- **Smith & Osherson (1988), Hampton (2007):** frames, the contrast rule, selective modification, threshold membership.
- **Collins & Quillian (1969):** semantic nets. A missing property ("a canary has no skin") forced the value search that accumulates many-valued properties.
- **Smith, Shoben & Rips (1974):** verification as an interface, with laws.
- **Shrager (1987):** terms with typed holes; knowledge nets; view application as a generic process. BigTrak went in as pure data.
- **Collins & Loftus (1975):** spreading activation over the same nets.

The git history records each generalization.

**A possible measure of progress:** the share of results quantified over data rather than fixed. The catalog already reports general against instance for every theorem. A finer column could report whether task knowledge enters as an argument or as a definition.

The user's reply to the colleague kept its hedge ("we're feeling our way through this") and its open edges, deliberately.
