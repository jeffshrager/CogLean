/-
The hierarchical network model of semantic memory (Collins & Quillian 1969).

* CQ1 (p. 240): concepts are nodes in a hierarchy; each has a pointer to
  its superset and to its properties. A property true of a superset is
  stored only there (cognitive economy); an exception is stored with the
  node it applies to (an ostrich cannot fly).
* CQ2 (pp. 240–241): to verify a statement, one moves up the hierarchy
  from the subject, searching the properties at each node. Moving up a
  level and retrieving a property each take time.
* CQ3 (p. 241): the times add (Donders' additivity); the time to retrieve
  a property does not depend on the level of its node.

Costs here are ordinal: a superset statement ("a canary is an animal")
costs the levels moved; a property statement costs the levels moved plus
one retrieval. The net is also the truth the laws are stated against.

For every net:
* `cq_distanceEffect`: the distance effect.
* `cq_no_typicality`, `cq_no_reversal`: never a typicality effect, never a
  reversal: cost depends only on distance.
* `cq_parallel`: property statements cost exactly one more than superset
  statements at the same level ("two parallel straight lines", p. 244).

`Fig1` is the paper's Figure 1, and the six sentence types of Fig. 2 come
out in the paper's order.
-/

import CogLib.Phenomena.Verification

namespace SemanticMemory

open Cog

variable {N L : Type} [DecidableEq N] [DecidableEq L]

/-- CQ2: verify "x is a c" by moving up from `x`; the cost is the levels moved. -/
def cq (G : SemNet N L) (fuel : Nat) : Verifier N where
  verify x c := match G.isaDist fuel x c with
    | some k => (true, k)
    | none => (false, fuel + 1)

/-- CQ1–CQ3: verify "x has value `v` of property `l`": the levels moved to
the node where `v` is found, plus one retrieval. For a single-valued
property (`single l`), a conflicting value found first is a contradiction:
false, at that level (an ostrich can't fly). -/
def cqProp (G : SemNet N L) (single : L → Bool) (fuel : Nat) (x : N) (l : L) (v : N) :
    Bool × Nat :=
  match G.findVal (single l) fuel x l v with
  | some (b, k) => (b, k + 1)
  | none => (false, fuel + 2)

theorem cq_cost (G : SemNet N L) (fuel : Nat) (x c : N) (k : Nat)
    (h : G.isaDist fuel x c = some k) : (cq G fuel).cost x c = k ∧ (cq G fuel).yes x c := by
  simp [Verifier.cost, Verifier.yes, cq, h]

/-- **The distance effect**, for every net. -/
theorem cq_distanceEffect (G : SemNet N L) (fuel : Nat) : DistanceEffect G fuel (cq G fuel) := by
  intro x c d j k hj hk hjk
  rw [(cq_cost G fuel x c j hj).1, (cq_cost G fuel x d k hk).1]
  exact hjk

/-- **Never a typicality effect**: instances equally far below a category
cost the same. -/
theorem cq_no_typicality (G : SemNet N L) (fuel : Nat) : ¬ TypicalityEffect G fuel (cq G fuel) := by
  rintro ⟨x, y, c, k, hx, hy, _, _, hne⟩
  rw [(cq_cost G fuel x c k hx).1, (cq_cost G fuel y c k hy).1] at hne
  exact hne rfl

/-- **Never a reversal.** -/
theorem cq_no_reversal (G : SemNet N L) (fuel : Nat) : ¬ Reversal G fuel (cq G fuel) :=
  fun h => not_distanceEffect_of_reversal G fuel _ h (cq_distanceEffect G fuel)

/-- **Parallel lines**: a property found `k` levels up costs one more than a
superset `k` levels up. -/
theorem cq_parallel (G : SemNet N L) (single : L → Bool) (fuel : Nat) (x c : N) (l : L) (v : N)
    (k : Nat) (hl : G.findVal (single l) fuel x l v = some (true, k))
    (hc : G.isaDist fuel x c = some k) :
    (cqProp G single fuel x l v).2 = (cq G fuel).cost x c + 1 := by
  simp [cqProp, hl, (cq_cost G fuel x c k hc).1]

/-! ### Figure 1 -/

namespace Fig1

inductive Node | animal | bird | fish | canary | ostrich | shark | salmon
  | skin | moveAround | eat | breathe | wings | fly | feathers | fins | swim | gills
  | sing | yellow | longThinLegs | tall | bite | dangerous | pink | edible | swimUpstream
  | yes | no
  deriving DecidableEq

inductive Label | isa | has | can | is | canFly
  deriving DecidableEq

open Node Label in
/-- Collins & Quillian's Figure 1: a 3-level hierarchy. "Can fly" is a
property of birds, overridden at ostrich ("can't fly"). -/
def G : SemNet Node Label where
  isa := Label.isa
  links := [
    (canary, isa, bird), (ostrich, isa, bird), (shark, isa, fish), (salmon, isa, fish),
    (bird, isa, animal), (fish, isa, animal),
    (animal, has, skin), (animal, can, moveAround), (animal, can, eat), (animal, can, breathe),
    (bird, has, wings), (bird, canFly, Node.yes), (bird, has, feathers),
    (fish, has, fins), (fish, can, swim), (fish, has, gills),
    (canary, can, sing), (canary, is, yellow),
    (ostrich, has, longThinLegs), (ostrich, is, tall), (ostrich, canFly, Node.no),
    (shark, can, bite), (shark, is, dangerous),
    (salmon, is, pink), (salmon, is, edible), (salmon, can, swimUpstream)]

/-- "Can fly" is single-valued; "has", "can", "is" are many-valued. -/
def single : Label → Bool
  | .canFly => true
  | _ => false

/-- The six sentence types of Fig. 2, with their ordinal costs. S0–S2: a canary
is a canary, a bird, an animal. P0–P2: a canary can sing, can fly, has skin. -/
theorem sentence_types :
    (cq G 3).verify .canary .canary = (true, 0) ∧ (cq G 3).verify .canary .bird = (true, 1) ∧
      (cq G 3).verify .canary .animal = (true, 2) ∧
      cqProp G single 3 .canary .can .sing = (true, 1) ∧ cqProp G single 3 .canary .canFly .yes = (true, 2) ∧
      cqProp G single 3 .canary .has .skin = (true, 3) := by
  decide

/-- An exception overrides: an ostrich can't fly, found at the ostrich node. -/
theorem ostrich : cqProp G single 3 .ostrich .canFly .no = (true, 1) ∧
    cqProp G single 3 .ostrich .canFly .yes = (false, 1) := by
  decide

/-- "A canary is a fish" is false. -/
theorem canary_not_fish : (cq G 3).verify .canary .fish = (false, 4) := by decide

end Fig1

end SemanticMemory
