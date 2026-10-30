/-
Sampling from the library's exact distributions, for simulation.

A model in CogLean defines an exact distribution (`Dist`). A simulation
draws one outcome from it at a time, with a seeded generator (Lean core's
`StdGen`). A draw is exact rational arithmetic: a uniform number `k / 10^9`
is compared with the distribution's cumulative probabilities.

Nothing here is used by the library or the theories; simulations import it.
-/

import CogLib

namespace Sims

open Cog

/-- The resolution of a uniform draw. -/
def resolution : Nat := 1000000000

/-- A uniform rational in `[0, 1)`, in steps of `1 / resolution`. -/
def drawUnit (g : StdGen) : Rat × StdGen :=
  let (k, g) := randNat g 0 (resolution - 1)
  ((k : Rat) / (resolution : Rat), g)

/-- A uniform natural number in `[lo, hi]`. -/
def drawNat (lo hi : Nat) (g : StdGen) : Nat × StdGen := randNat g lo hi

/-- Draw one outcome of a distribution, in proportion to its probabilities
(normalized by the total mass). The distribution must be nonempty. -/
def drawDist {α : Type} [Inhabited α] (d : Dist α) (g : StdGen) : α × StdGen :=
  let total := (d.map (·.2)).foldl (· + ·) 0
  let (u, g) := drawUnit g
  let target := u * total
  let rec go : List (α × Rat) → Rat → α
    | [], _ => default
    | [(a, _)], _ => a
    | (a, p) :: rest, acc => if target < acc + p then a else go rest (acc + p)
  (go d 0, g)

end Sims
