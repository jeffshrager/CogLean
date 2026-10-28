/-
The small universe the counterexamples use: the eight 3-bit codes, all
features compared, scanned in order.
-/

import CogLib

namespace Cog.Matrix

/-- The 3-bit code of `k`, low bit first. -/
def bits (k : Nat) : Item := [k % 2 == 1, k / 2 % 2 == 1, k / 4 % 2 == 1]

/-- All eight 3-bit codes. -/
def U3 : List Item := (List.range 8).map bits

/-- The three features, in order. -/
def F3 : List Feature := [0, 1, 2]

/-- Any two different 3-bit codes differ on a feature EPAM notices. -/
theorem noticeable_U3 : PairwiseNoticeable F3 U3 := by
  have h : ∀ x ∈ U3, ∀ z ∈ U3, z ≠ x → (firstDiff F3 x z).isSome = true := by decide
  intro x hx z hz hzx
  exact Option.isSome_iff_exists.mp (h x hx z hz hzx)

end Cog.Matrix
