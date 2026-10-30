# Semantic memory: hierarchical networks and feature comparison

The fifth theory package in CogLean (`../README.md`): two rival accounts of how people verify statements like "a canary is a bird", formalized on CogLib's semantic nets (`Rep/SemanticNet`) and held to theory-neutral laws (`Phenomena/Verification`). Costs are ordinal, steps or stages, not milliseconds: the models disagree in the *order* of verification times, and that is what is proved.

Collins, A. M., & Quillian, M. R. (1969). Retrieval time from semantic memory. *Journal of Verbal Learning and Verbal Behavior*, 8, 240–247.
Smith, E. E., Shoben, E. J., & Rips, L. J. (1974). Structure and process in semantic memory: A featural model for semantic decisions. *Psychological Review*, 81, 214–241.

```sh
cd SemanticMemory && lake build    # builds CogLib too; core Lean only
```

## The two models

| Postulate (page) | Lean |
|---|---|
| CQ1 Concepts are nodes in a hierarchy, with pointers to their superset and properties; a property true of a superset is stored only there (cognitive economy); an exception is stored at its node (p. 240) | `Cog.SemNet` |
| CQ2 Verification moves up from the subject, searching properties at each node; moving and retrieving each take time (pp. 240–241) | `cq`, `cqProp`, using `SemNet.isaDist`, `SemNet.findVal` |
| CQ3 The times add; retrieving a property takes the same time at any level (p. 241) | costs: levels moved, plus one retrieval |
| FC1 A term's meaning is a set of features, more or less defining; those above a bound are defining, the rest characteristic (pp. 215–217) | `Meaning` |
| FC2 Stage 1: overall similarity over all features; above `c1` true, below `c0` false, at once. Otherwise stage 2: true iff every defining feature of the category is the instance's (pp. 222–223, Fig. 3) | `decide2`, `fc` |

Declared simplifications for FC: similarity is the share of the category's features the instance has (the paper leaves the rule open, p. 222); it is fixed for a pair, not sampled; cost counts stages.

## Laws (CogLib, `Phenomena/Verification`)

Stated for any verifier, against a hierarchy that says what is true:
- **Distance effect**: the farther category costs more ("a canary is an animal" after "a canary is a bird").
- **Typicality effect**: two instances equally far below a category, both verified, at different costs.
- **Reversal**: an instance verified faster as a member of a farther category ("a chicken is an animal" faster than "a chicken is a bird").

A reversal contradicts the distance effect (`not_distanceEffect_of_reversal`).

## What is proved

| | Distance effect | Typicality effect | Reversal |
|---|---|---|---|
| Hierarchical (C&Q) | **has**, every net (`cq_distanceEffect`) | **never** (`cq_no_typicality`) | **never** (`cq_no_reversal`) |
| Feature comparison (SSR) | lacks (`Birds.no_distanceEffect`) | can hold (`Birds.typicality`) | can hold (`Birds.reversal`) |

Also, for every net, **parallel lines** (`cq_parallel`): a property found *k* levels up costs exactly one more than a superset *k* levels up (C&Q, p. 244). For every choice of features and criteria, **typicality sets the cost** in the feature model (`fc_typicality`): an instance at least as similar as one verified true is never slower.

**Figure 1** (`Fig1`): C&Q's 3-level hierarchy. The six sentence types of Fig. 2 come out in the paper's order: S0, S1, S2 cost 0, 1, 2 levels; P0, P1, P2 cost 1, 2, 3 ("a canary can sing", "can fly", "has skin"). The ostrich exception is found at the ostrich, so "an ostrich can fly" is false.

The evidence (Rips, Shoben & Smith 1973; SSR 1974, Exp. 2) shows typicality effects and reversals, which the hierarchical model can never produce at any setting.

## Not yet

- Spreading activation (Collins & Loftus 1975) as a third family.
- Similarity as a random variable (the paper's form); false responses (the relatedness effect; C&Q's contradiction and search-and-destroy hypotheses).
- View application (Shrager 1987) on these nets: `../notes/OPEN_ISSUES.md` #19.
