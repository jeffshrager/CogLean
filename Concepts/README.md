# Concepts: prototype combination and over-extension

The fourth theory in CogLean (`../README.md`): the selective modification model of conceptual combination (Smith, Osherson, Rips & Keane 1988), with graded membership by the threshold model (Hampton 2007). A concept is a prototype of attributes and values. An adjective modifies a noun's prototype; typicality is similarity to a prototype; membership is a nondecreasing function of the same similarity. From these, an instance can be more a member of *even multiple of 3* than of *multiple of 3*. That is **over-extension**, which fuzzy logic's rule for conjunction forbids.

Smith, E. E., Osherson, D. N., Rips, L. J., & Keane, M. (1988). Combining prototypes: A selective modification model. *Cognitive Science*, 12, 485–527.
Hampton, J. A. (2007). Typicality, graded membership, and vagueness. *Cognitive Science*, 31, 355–384.

```sh
cd Concepts
lake build                   # builds CogLib too; core Lean only
python3 analysis/mirror.py   # the same model in Python, exact fractions
```

## Postulates

| Postulate (page) | CogLib / this package |
|---|---|
| SO1 A concept is a prototype: attributes, their values, each value's salience ("votes"), each attribute's diagnosticity (pp. 488–489) | `Cog.Proto`, `Cog.Schema` (`Rep/Frames`) |
| SO2 An instance is represented like a prototype, without diagnosticity; in the paper's examples all its votes on an attribute are on one value, as many as the prototype has there (p. 489) | `Cog.Inst`, `Cog.Inst.pure` |
| SO3 Typicality is similarity by Tversky's contrast rule, attribute by attribute: each vote a feature, common features weighed by `a`, the prototype's and the instance's distinct ones by `b` and `c`, each multiplied by diagnosticity (pp. 489–491, Eq. 2) | `Cog.sim` |
| SO4 An adjective selects its attribute in the noun, shifts all of that attribute's votes to its value, and boosts the attribute's diagnosticity (by 2, "an arbitrary choice") (pp. 492–493) | `Cog.modify` (`Process/Combination`), `Concepts.combine` |
| H1 Membership is a nondecreasing function of the same similarity: 0 below a bound, 1 above another, graded between (Hampton 2007, pp. 360, 365, Eqs. 6 and 8) | `Cog.thresholdM` (`Phenomena/Combination`), `Concepts.membership` |

The free parameters are `a`, `b`, `c`, the boost, H1's two bounds, and each concept's prototype.

## What is proved

For every prototype and every choice of parameters satisfying the stated conditions (`Concepts/Phenomena.lean`):

- **The conjunction effect** (`conjunction_effect`): an instance with the adjective's value is more typical of the combination than of the noun. It needs `a > 0`, `b, c ≥ 0`, a boost of at least 1, a diagnostic attribute, and something to change: a boost above 1, or noun votes not already all on the value.
- **The reverse conjunction effect** (`reverse_conjunction_effect`): an instance with another value is less typical of the combination. It needs only `b + c > 0` among the weights.
- **The attribute, not the value** (`attribute_not_value`): a red apple is exactly as typical of *red apple* as a brown apple is of *brown apple*, for every parameter choice. The paper states this on p. 495.
- **Over-extension** (`overExtends_binary`, `member_mono`): with yes/no membership at some criterion, such an instance is judged a member of the combination and not of the noun. Under any nondecreasing graded membership, it is never less a member of the combination.

These are stated in CogLib for any similarity (`Phenomena/Combination`), so a rival theory of combination can be held to the same phenomena.

## The paper's figures (`Concepts/Data.lean`)

The apple prototype and three apples, with `a = b = c = 1` and a boost of 2, reproduce every similarity in Figs. 1–4 exactly: 85/4, −215/4, 5/2, 265/4 and −455/4. The paper rounds these to 21, −54, 2.5, 66 and −114. The conjunction effect is 120 for *brown apple* and 45 for *red apple* (p. 495). Our copy of the figures is partly illegible. The sums in the text fix the totals, and for these instances any split of the remaining votes gives the same values.

## Numbers (`Concepts/Numbers.lean`)

Number concepts have a truth to compare against.

- **The attributes** are computed from the number: parity, last digit, digit sum mod 3, and number of digits.
- **The truth** is proved:
  - a number is divisible by 6 iff it is even and divisible by 3;
  - the digit-sum test for 3, below 1000;
  - the last-digit test for 2.
- **The prototype comes from experience, not choice.** *multiple of 3* counts the values of the exemplars 3, 6, …, 30. *even multiple of 3* is that prototype modified by *even*.
- **`even_more_typical`:** every even number is more typical of *even multiple of 3* than of *multiple of 3*, whether or not it is a multiple of 3. This is the general theorem, applied.
- **`even_overExtends`:** so every even non-multiple of 3 is, at some criterion, judged an even multiple of 3 and not a multiple of 3. That is incoherent, and also false.
- **`fourteen`:** with Hampton bounds −50 and 0, chosen for illustration, 14 is an *even multiple of 3* to degree 497/625 (about .80), and a *multiple of 3* to degree 81/1250 (about .06). The number 9 is a *multiple of 3* only to degree 721/1250 (about .58).

So the model's over-extensions are not only incoherent, which is what the classic literature can show. Against arithmetic, they are wrong.

## Not yet

- **Hampton's threshold function is not proved monotone.** It is defined and computed, but its monotonicity isn't proved, so the graded over-extension theorem takes the membership function's rise as a hypothesis.
- **Diagnosticity is set to 1 for numbers.** S&O derive it from a contrast class; that could be derived here too.
- **Rival theories of combination.** One is view application (Shrager 1987), held to the same phenomena. See `../notes/OPEN_ISSUES.md`.
