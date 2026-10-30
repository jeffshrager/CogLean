/-
Phenomena of semantic verification, for any verifier.

A verifier decides statements "x is a c" (category statements), giving an
answer and a cost. The cost is ordinal: a count of steps or stages, not a
time. The laws are stated against a hierarchy that says what is true and
how far apart the terms are (`SemNet.isaDist`).

* `DistanceEffect`: of two true statements about one instance, the one
  whose category is farther up the hierarchy costs more ("a canary is an
  animal" after "a canary is a bird"; Collins & Quillian 1969).
* `TypicalityEffect`: two instances equally far below a category, both
  verified, at different costs ("a robin is a bird" faster than "a chicken
  is a bird"; Rips, Shoben & Smith 1973).
* `Reversal`: an instance verified faster as a member of a farther category
  than of a nearer one ("a chicken is an animal" faster than "a chicken is
  a bird"; Smith, Shoben & Rips 1974, p. 221).

A reversal contradicts the distance effect (`not_distanceEffect_of_reversal`).
-/

import CogLib.Rep.SemanticNet

namespace Cog

/-- A verifier of category statements: for "x is a c", an answer and a cost. -/
structure Verifier (N : Type) where
  verify : N → N → Bool × Nat

variable {N L : Type} [DecidableEq N] [DecidableEq L]

/-- The cost of verifying "x is a c". -/
abbrev Verifier.cost (V : Verifier N) (x c : N) : Nat := (V.verify x c).2

/-- "x is a c" is verified true. -/
abbrev Verifier.yes (V : Verifier N) (x c : N) : Prop := (V.verify x c).1 = true

/-- **The distance effect**: of two true statements about `x`, the farther
category costs more. -/
def DistanceEffect (H : SemNet N L) (fuel : Nat) (V : Verifier N) : Prop :=
  ∀ x c d j k, H.isaDist fuel x c = some j → H.isaDist fuel x d = some k → j < k →
    V.cost x c < V.cost x d

/-- **The typicality effect**: two instances equally far below a category,
both verified true, at different costs. -/
def TypicalityEffect (H : SemNet N L) (fuel : Nat) (V : Verifier N) : Prop :=
  ∃ x y c k, H.isaDist fuel x c = some k ∧ H.isaDist fuel y c = some k ∧
    V.yes x c ∧ V.yes y c ∧ V.cost x c ≠ V.cost y c

/-- **A reversal**: `x` is verified faster as a member of a farther category. -/
def Reversal (H : SemNet N L) (fuel : Nat) (V : Verifier N) : Prop :=
  ∃ x c d j k, H.isaDist fuel x c = some j ∧ H.isaDist fuel x d = some k ∧ j < k ∧
    V.yes x c ∧ V.yes x d ∧ V.cost x d < V.cost x c

theorem not_distanceEffect_of_reversal (H : SemNet N L) (fuel : Nat) (V : Verifier N)
    (h : Reversal H fuel V) : ¬ DistanceEffect H fuel V := by
  intro hd
  obtain ⟨x, c, d, j, k, hj, hk, hjk, _, _, hlt⟩ := h
  have := hd x c d j k hj hk hjk
  omega

end Cog
