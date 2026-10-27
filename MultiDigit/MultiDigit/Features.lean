/-
Problem features beyond the digits (M1a-M1c).

M1 asks only that a problem's code carry each digit of each addend. A code
may carry more, and a discrimination net can test only what the code
carries. Three further kinds of feature are stated here as laws an encoding
may satisfy, each as a structure over an `Encoding`:

| Postulate | Law |
|---|---|
| M1a Zeros: whether a digit is 0 | `Zeros`: `zero i j` reads `p.digit i j == 0` |
| M1b Magnitude: a digit's size, as thresholds | `Magnitude`: `above i j k` reads `k < p.digit i j` |
| M1c Column facts: the single-digit fact in each column | `ColumnFacts`: `fact j` determines the column's sum |

Under M1b close digits share most of their features (`threshold_diffs`):
digits d and e differ on exactly |d - e| of the nine thresholds. Under M1c a
column's fact is coded without regard to order, so 3 + 4 and 4 + 3 are the
same fact; the laws ask only that the fact features determine the column's
sum.
-/

import MultiDigit.Postulates

namespace MD

open Cog

/-- The sum of a problem's digits in one column. -/
def Problem.colSum (p : Problem) (j : Place) : Nat := p.digit .first j + p.digit .second j

/-- Both addends have 0 in place `j`. -/
def Problem.RoundIn (p : Problem) (j : Place) : Prop :=
  p.digit .first j = 0 ∧ p.digit .second j = 0

/-- A round problem, such as 100 + 200: 0 in the tens and units of both
addends. -/
def Problem.Round (p : Problem) : Prop := p.RoundIn .tens ∧ p.RoundIn .units

/-- **M1a Zeros.** For each digit, a feature that says whether it is 0. -/
structure Zeros (E : Encoding) where
  zero : Addend → Place → Feature
  reads : ∀ p i j, (E.code p).feat (zero i j) = (p.digit i j == 0)

/-- **M1b Magnitude.** For each digit, nine threshold features: the `k`th says
whether the digit exceeds `k` (a thermometer code). -/
structure Magnitude (E : Encoding) where
  above : Addend → Place → Nat → Feature
  reads : ∀ p i j k, (E.code p).feat (above i j k) = decide (k < p.digit i j)

/-- **M1c Column facts.** For each column, features that identify its
single-digit fact, and so determine the column's sum. -/
structure ColumnFacts (E : Encoding) where
  fact : Place → List Feature
  determines : ∀ j, Determines E.code (fact j) (fun p => p.colSum j)

variable {E : Encoding}

theorem Zeros.determines (Z : Zeros E) (i : Addend) (j : Place) :
    Determines E.code [Z.zero i j] (fun p => p.digit i j == 0) := by
  intro p q h
  dsimp only
  rw [← Z.reads p i j, ← Z.reads q i j]
  exact h _ (List.mem_singleton_self _)

theorem Magnitude.determines (M : Magnitude E) (i : Addend) (j : Place) (k : Nat) :
    Determines E.code [M.above i j k] (fun p => decide (k < p.digit i j)) := by
  intro p q h
  dsimp only
  rw [← M.reads p i j k, ← M.reads q i j k]
  exact h _ (List.mem_singleton_self _)

/-- The thresholds at which digits `d` and `e` differ. -/
def thresholdDiffs (d e : Nat) : List Nat :=
  (List.range 9).filter fun k => decide (k < d) != decide (k < e)

/-- **Close digits share features.** Two digits differ on exactly `|d - e|` of
the nine thresholds, so they agree on `9 - |d - e|`. -/
theorem threshold_diffs : ∀ d, d < 10 → ∀ e, e < 10 →
    (thresholdDiffs d e).length = (d - e) + (e - d) := by
  decide

/-- So a magnitude encoding makes two problems differ on exactly
`|d - e|` of a digit's threshold features. -/
theorem Magnitude.diffs (M : Magnitude E) (p q : Problem) (i : Addend) (j : Place) :
    ((List.range 9).filter fun k =>
        (E.code p).feat (M.above i j k) != (E.code q).feat (M.above i j k)).length =
      (p.digit i j - q.digit i j) + (q.digit i j - p.digit i j) := by
  simp only [M.reads]
  exact threshold_diffs _ (digit_lt p i j) _ (digit_lt q i j)

end MD
