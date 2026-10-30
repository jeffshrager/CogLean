/-
The feature comparison model (Smith, Shoben & Rips 1974).

* FC1 (pp. 215–217): the meaning of a term is a set of semantic features,
  which vary in how defining they are; those above a bound are *defining*,
  the rest *characteristic*.
* FC2 (pp. 222–223, Fig. 3): to decide "x is a c", stage 1 retrieves both
  feature lists and computes their overall similarity `s`, over all
  features. If `s > c1`, respond true at once; if `s < c0`, false at once.
  Otherwise stage 2 compares the defining features only: true if every
  defining feature of `c` is a feature of `x`.

Simplifications, as declared choices: similarity is the share of the
category's features that the instance has (the paper leaves the
combination rule open, p. 222); it is fixed for a pair, not sampled (the
paper treats it as a random variable); cost counts stages.

For every choice of features and criteria:
* `fc_typicality`: an instance at least as similar as one verified true is
  never slower. So typicality, through similarity, sets the cost.

With features for *robin*, *chicken*, *bird* and *animal* (`Birds`), the
model shows the typicality effect (*robin* is a bird in one stage,
*chicken* in two) and a reversal (*chicken* is an animal in one stage),
so it lacks the distance effect, which the hierarchical model has for every
net.
-/

import CogLib.Phenomena.Verification

namespace SemanticMemory

open Cog

/-- FC1: a term's meaning: its features, and the defining ones among them. -/
structure Meaning where
  feats : List Nat
  defining : List Nat

/-- The parameters: the two stage-1 criteria. -/
structure FCParams where
  c0 : Rat
  c1 : Rat

/-- Overall similarity of instance to category: the share of the category's
features the instance has. -/
def similarity (x c : Meaning) : Rat :=
  ((c.feats.filter fun f => f ∈ x.feats).length : Rat) / (c.feats.length : Rat)

/-- FC2: the two-stage decision, with the number of stages used. -/
def decide2 (P : FCParams) (x c : Meaning) : Bool × Nat :=
  let s := similarity x c
  if P.c1 < s then (true, 1)
  else if s < P.c0 then (false, 1)
  else (c.defining.all fun f => f ∈ x.feats, 2)

/-- The verifier, for terms named by `N`. -/
def fc {N : Type} (P : FCParams) (meaning : N → Meaning) : Verifier N where
  verify x c := decide2 P (meaning x) (meaning c)

/-- **Typicality sets the cost**: an instance at least as similar to the
category as one verified true is never slower. -/
theorem fc_typicality {N : Type} (P : FCParams) (meaning : N → Meaning) (x y c : N)
    (hle : similarity (meaning x) (meaning c) ≤ similarity (meaning y) (meaning c))
    (hx : (fc P meaning).yes x c) :
    (fc P meaning).cost y c ≤ (fc P meaning).cost x c := by
  simp only [Verifier.cost, Verifier.yes, fc, decide2] at *
  generalize similarity (meaning x) (meaning c) = sx at *
  generalize similarity (meaning y) (meaning c) = sy at *
  by_cases h1 : P.c1 < sx
  · have : P.c1 < sy := by grind
    simp [h1, this]
  · by_cases h0 : sx < P.c0
    · simp [h1, h0] at hx
    · simp only [h1, h0, ite_false]
      split <;> (try split) <;> simp

/-! ### Birds -/

namespace Birds

inductive Term | robin | chicken | bird | animal
  deriving DecidableEq

/-- Features: 0 wings, 1 feathers, 2 lays eggs (defining for *bird*);
3 flies, 4 sings, 5 small, 6 perches (characteristic of *bird*);
7 alive, 8 moves, 9 eats (defining for *animal*); 10 walks, 11 large-ish,
12 farm (characteristic of *animal*, illustratively). -/
def meaning : Term → Meaning
  | .robin => ⟨[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], []⟩
  | .chicken => ⟨[0, 1, 2, 7, 8, 9, 10, 11, 12], []⟩
  | .bird => ⟨[0, 1, 2, 3, 4, 5, 6], [0, 1, 2]⟩
  | .animal => ⟨[7, 8, 9, 10, 11, 12], [7, 8, 9]⟩

/-- The truth: robin and chicken are birds, birds are animals. -/
def H : SemNet Term Unit where
  isa := ()
  links := [(.robin, (), .bird), (.chicken, (), .bird), (.bird, (), .animal)]

def P : FCParams := ⟨1 / 4, 3 / 4⟩

theorem costs :
    (fc P meaning).verify .robin .bird = (true, 1) ∧ (fc P meaning).verify .chicken .bird = (true, 2) ∧
      (fc P meaning).verify .chicken .animal = (true, 1) ∧
      (fc P meaning).verify .robin .animal = (true, 2) := by
  decide +kernel

/-- **The typicality effect**: a robin is a bird in one stage, a chicken in two. -/
theorem typicality : TypicalityEffect H 2 (fc P meaning) :=
  ⟨.robin, .chicken, .bird, 1, by decide, by decide, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- **A reversal**: a chicken is an animal in one stage, a bird in two. -/
theorem reversal : Reversal H 2 (fc P meaning) :=
  ⟨.chicken, .bird, .animal, 1, 2, by decide, by decide, by decide, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- So the feature comparison model lacks the distance effect. -/
theorem no_distanceEffect : ¬ DistanceEffect H 2 (fc P meaning) :=
  not_distanceEffect_of_reversal H 2 _ reversal

end Birds

end SemanticMemory
