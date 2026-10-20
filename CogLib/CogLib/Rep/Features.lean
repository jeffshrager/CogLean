/-
Representations: feature codes.

A stimulus reaches a cognitive system as a *code*: a vector of binary
features. This is the simplest representation that supports similarity
(agreement on features), discrimination (a feature on which two codes
differ), and partial information (some features known, others not).
-/

namespace Cog

/-- A feature: an index into a code. -/
abbrev Feature := Nat

/-- A feature code: a list of bits. Features beyond its length read as 0. -/
abbrev Item := List Bool

/-- The value of feature `f` of code `x`. -/
def Item.feat (x : Item) (f : Feature) : Bool := x.getD f false

end Cog
