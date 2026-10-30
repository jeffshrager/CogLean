# View application: one knowledge model, two domains

View application (Shrager 1987) on CogLib's knowledge nets. A knowledge net is a semantic net (`Rep/SemanticNet`) whose nodes are terms (`Rep/Terms`): atoms, structured values, and typed holes. Frames, slots, patterns, prototypes and categorization methods are all links in the same net. View application is one generic process on such nets (`Process/ViewApplication`). This package supplies only data: the paper's BigTrak tables, and number concepts with an ARITHMETIC view.

Shrager, J. (1987). Theory change via view application in instructionless learning. *Machine Learning*, 2, 247–276.

```sh
cd ViewApplication && lake build    # builds CogLib and Concepts too; core Lean only
```

## The process (CogLib, `Process/ViewApplication`), after §3.4.2

1. **Copy** the view: this is the base.
2. **Merge** the theory into it.
   - **Matching:** each theory type frame is matched to the view's frame of the same abstract type. If there is none, it is matched to a view type frame of the same kind, chosen at random, or left unmatched. Ties are never revisited (p. 261), so application yields a distribution over theories.
   - **Conflicts:** on a matched frame, the view's slots win.
   - **The rest:** everything else in the theory is copied, with matched frames renamed throughout.
3. **Coerce** each re-parented instance's slots. Each value is matched against the old parent's pattern for that slot, and the new parent's pattern is filled with the result.
4. **Bind** the holes in the view's instance frames to the theory atoms that the holes' types point to.
5. **Single function:** an atom bound in step 4 leaves every other frame's lists. A script that ran the operation that lost the atom then also runs the operation that gained it.

**Proved for any view, theory and matching:**
- the view is kept;
- on matched frames the view wins: a non-monotonic change;
- unmatched theory frames survive, renamed;
- instances are re-parented.

## BigTrak (`BigTrak.lean`): the paper's own example

Tables 1 and 2 are given as data. Applying CODE.AND.STARTUP yields **Table 4 exactly**, with probability 1/2. The other half of the time, Action-operation is matched to Immediate-operation, which is the paper's random tie-breaking.

The only fact added beyond the tables is from the device description (§3.1): GO's label indicates CODE.AND.STARTUP. Forward-9 keeps its name; the paper renames it New-Forward-Operation.

## Numbers (`Numbers.lean`): over-extension removed, typicality kept

**The learner's theory** (CogLib, `Process/Categorize`):
- A `category` type frame decides membership by similarity to the prototype, graded by Hampton's threshold. It combines concepts by selective modification.
- The prototypes of *multiple of 3* and *even* are links in the net, learned from exemplars.

**The ARITHMETIC view** has its own `category` frame:
- membership by divisibility, reading the divisor from the concept's name;
- combination by conjunction.

Applying the view replaces `category`'s test and combination. The concepts' frames and prototypes are not matched, so they are kept.

| | Before the view | After the view |
|---|---|---|
| 14 in *multiple of 3* | .06 | 0 |
| 14 in *even multiple of 3* | .80: over-extension | 0 |
| *even multiple of 3* | similarity to the modified prototype | exactly divisibility by 6, for every number (`after_exact`) |
| over-extension | at 14 (`before`) | never, at any number (`after_no_overextension`) |
| typicality | | unchanged, for every number (`typicality_unchanged`) |

So after the view, typicality and membership dissociate (`dissociation`). 14 as an *even multiple of 3* is more typical (−16) than 9 as a *multiple of 3* (−23), yet only 9 is a member. Before the view, that is impossible: membership is a nondecreasing function of typicality (`Cog.not_dissociates`). 14 also remains more typical of *even multiple of 3* than of *multiple of 3*. That is Armstrong, Gleitman & Gleitman's (1983) finding for *odd number*: graded typicality for a concept whose membership is all-or-none.

Apples are unaffected, since no view applies to them. S&O's and Hampton's results (`../Concepts/`) stand.

## Selecting the view by spreading activation (`Selection.lean`)

The 1987 paper had no principled account of view selection (§3.4.1). Here selection is **spreading activation** (Collins & Loftus 1975; CogLib `Process/SpreadingActivation`), run over the same knowledge net that holds the learner's theory and the views' associations.

- Activation starts at the cue (a key's label) and at the concepts the current theory uses.
- It spreads along `suggests` links, each passing on a fraction set by its strength.
- A view is chosen in proportion to its activation.
- The chosen view is then applied.

So the composition is a mixture, the same shape as recognition followed by retrieval in MultiDigit.

**Proved generally (CogLib):**
- activation from several sources sums, which is C&L's assumption 4;
- activation is never negative;
- priming never lowers any node's activation;
- priming a candidate never lowers its share of the choice.

**The example: a hypothetical device with a "+" key.**
- "+" suggests a CALCULATING view ("+" adds to the display) and, more weakly, a PROGRAMMING view ("+" appends a step).
- *Memory* suggests PROGRAMMING.
- A learner whose theory has no memory reads "+" as adding with probability 2/3 (`naive`).
- A learner whose theory already has a memory reads it as appending a step with probability 3/5 (`primed`).

The same cue brings in different knowledge depending on what the learner already knows. The strengths are illustrative.

## Not yet

- **View selection by EPAM recognition** of cues, as an alternative to spreading activation. Also C&L's decision process: evidence summed toward positive and negative criteria.
- **Learning the view itself.**
- **Holding the feature comparison model's `Meaning`s in knowledge nets.** S&O prototypes already are held in nets (`protoOfNet`); SSR's features aren't yet.
- **Coercion, binding and single function are minimal general forms** of what the paper describes in prose. The paper calls their heuristics partly domain-specific.
