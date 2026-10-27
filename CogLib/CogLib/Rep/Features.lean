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

/-- The features `fs` of a code *determine* a property `P` of what is coded:
two things whose codes agree on `fs` agree on `P`. -/
def Determines {α β : Type} (code : α → Item) (fs : List Feature) (P : α → β) : Prop :=
  ∀ p q, (∀ f ∈ fs, (code p).feat f = (code q).feat f) → P p = P q

/-- The number of features in `fs` on which two codes differ. -/
def mismatches (fs : List Feature) (x y : Item) : Nat :=
  (fs.filter fun f => x.feat f != y.feat f).length

end Cog
