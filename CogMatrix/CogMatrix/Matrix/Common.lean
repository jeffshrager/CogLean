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

end Cog.Matrix
