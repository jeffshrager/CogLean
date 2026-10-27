/-
A family of memories: strength with sampling and a criterion (after the
distributions-of-associations model, Siegler & Shrager 1984).

Each stimulus has a strength, which study raises by a fixed increment. A
probe samples stored stimuli in proportion to strength, discounted by `μ`
for each mismatching feature. A sample is stated if its weight clears the
criterion; otherwise sampling is repeated, up to the search length, and then
retrieval fails. Nothing decays, and nothing records when study happened.
-/

import CogLib

namespace Cog

/-- The parameters: the stimuli that can be stored, the features compared,
the discount per mismatch, the increment per study, the criterion and the
search length. -/
structure StrParams where
  items : List Item
  fs : List Feature
  mu : Rat
  inc : Rat
  cc : Rat
  n : Nat

/-- A memory state: each stimulus's strength. -/
abbrev StrState := Item → Rat

namespace Str

/-- The weight of a stored `y` for the probe `x`. -/
def weight (P : StrParams) (s : StrState) (x : Item) (y : Item) : Rat :=
  s y * P.mu ^ mismatches P.fs x y

/-- **Retrieval**: search the stored stimuli, stating the first sample that
clears the criterion. -/
def retrieve (P : StrParams) (s : StrState) (x : Item) : Dist (Option Item) :=
  Dist.bind (search P.items (weight P s x) P.cc 0 P.n) fun
    | .stated y _ => Dist.pure (some y)
    | .exhausted => Dist.pure none

/-- **Study** raises a stimulus's strength by the increment. -/
def study (P : StrParams) (s : StrState) (y : Item) : StrState :=
  fun z => if z = y then s z + P.inc else s z

end Str

/-- Strength memory as a retriever. -/
def strRetriever (P : StrParams) : Retriever StrState Item := ⟨Str.study P, Str.retrieve P⟩

end Cog
