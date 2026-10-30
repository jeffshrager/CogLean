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

So after the view, typicality and membership dissociate. 14 is still more typical of *even multiple of 3* than of *multiple of 3*, and a member of neither (`dissociation`). That is Armstrong, Gleitman & Gleitman's (1983) finding for *odd number*: graded typicality for a concept whose membership is all-or-none.

Apples are unaffected, since no view applies to them. S&O's and Hampton's results (`../Concepts/`) stand.

## Not yet

- **View selection** (§3.4.1), for instance by EPAM recognition of a cue such as a label.
- **Learning the view itself.**
- **Holding the feature comparison model's `Meaning`s in knowledge nets.** S&O prototypes already are held in nets (`protoOfNet`); SSR's features aren't yet.
- **Coercion, binding and single function are minimal general forms** of what the paper describes in prose. The paper calls their heuristics partly domain-specific.
