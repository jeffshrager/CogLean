/-
Phenomena of serial learning, stated theory-neutrally.

* `SerialPositionEffect`: over the positions of a list, errors increase with
  distance from the nearer end, giving the bowed serial position curve.
-/

namespace Cog.Phenomena

/-- The distance of position `i` (of `0 .. n-1`) from the nearer end of a
list of length `n`. -/
def distFromEnds (n i : Nat) : Nat := min i (n - 1 - i)

/-- **The serial position effect.** Of two positions in a list of length
`n`, the one further from its nearer end has strictly more errors. -/
def SerialPositionEffect (n : Nat) (errors : Nat → Nat) : Prop :=
  ∀ i j, i < n → j < n → distFromEnds n i < distFromEnds n j → errors i < errors j

end Cog.Phenomena
