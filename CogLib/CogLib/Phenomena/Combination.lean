/-
Phenomena of conceptual combination, for any similarity to a prototype.

* The **conjunction effect** (Smith & Osherson 1984): an instance is more
  typical of the combination (`red apple`) than of the head noun (`apple`).
* **Graded membership** by the threshold model (Hampton 2007): membership
  is a nondecreasing function of the same similarity that typicality rests
  on, 0 below a lower bound, 1 above an upper one, graded in between
  (`thresholdM`, his Eq. 8).
* **Over-extension** (Hampton 1988b): an instance is more a member of the
  combination than of one of its constituents. Fuzzy logic's rule for
  conjunction (membership is the minimum) forbids it.

* **Dissociation**: a more typical judgment that is less a member. It is
  impossible when membership is a nondecreasing function of typicality
  (`not_dissociates`).

Over-extension follows from the conjunction effect for any nondecreasing
membership function that rises between the two similarities
(`overExtends_of_conjunctionEffect`), and, for yes/no judgments, at some
threshold (`overExtends_binary_of_conjunctionEffect`).
-/

import CogLib.Rep.Frames

namespace Cog

variable {A V : Type}

/-- **The conjunction effect**: `I` is more similar to the combination than
to the head. -/
def ConjunctionEffect (K : Contrast) (S : Schema A V) (comb head : Proto A V) (I : Inst A V) : Prop :=
  sim K S head I < sim K S comb I

/-- **The reverse conjunction effect**: `I` is less similar to the
combination than to the head. -/
def ReverseConjunctionEffect (K : Contrast) (S : Schema A V) (comb head : Proto A V)
    (I : Inst A V) : Prop :=
  sim K S comb I < sim K S head I

/-- Hampton's threshold function (2007, Eq. 8): membership from similarity
`s`, 0 up to `SL`, 1 from `SH`, and two quadratic pieces meeting at the
midpoint, where it is 1/2. -/
def thresholdM (SL SH s : Rat) : Rat :=
  if s ≤ SL then 0
  else if s ≤ (SL + SH) / 2 then 2 * ((s - SL) / (SH - SL)) ^ 2
  else if s < SH then 1 - 2 * ((SH - s) / (SH - SL)) ^ 2
  else 1

/-- A membership function that never falls as similarity rises. -/
def Nondecreasing (m : Rat → Rat) : Prop := ∀ x y, x ≤ y → m x ≤ m y

/-- **Over-extension**: with membership `m` of similarity, `I` is more a
member of the combination than of the head. -/
def OverExtends (m : Rat → Rat) (K : Contrast) (S : Schema A V) (comb head : Proto A V)
    (I : Inst A V) : Prop :=
  m (sim K S head I) < m (sim K S comb I)

/-- **Over-extension, yes/no**: at criterion `θ`, `I` is judged a member of
the combination and not of the head. -/
def OverExtendsBinary (θ : Rat) (K : Contrast) (S : Schema A V) (comb head : Proto A V)
    (I : Inst A V) : Prop :=
  sim K S head I < θ ∧ θ ≤ sim K S comb I

/-- **Typicality and membership dissociate**: of two judgments (an instance
in a concept), the more typical is less a member. -/
def Dissociates {β : Type} (typ mem : β → Rat) : Prop :=
  ∃ p q, typ q < typ p ∧ mem p < mem q

/-- **No dissociation when membership is a nondecreasing function of
typicality** (the threshold model, with one function for every concept). -/
theorem not_dissociates {β : Type} (typ : β → Rat) (m : Rat → Rat) (hm : Nondecreasing m) :
    ¬ Dissociates typ (fun p => m (typ p)) := by
  rintro ⟨p, q, hlt, hmem⟩
  have := hm _ _ (Rat.le_of_lt hlt)
  exact absurd hmem (Rat.not_lt.mpr this)

/-- Under any nondecreasing membership, the conjunction effect makes `I` at
least as much a member of the combination as of the head. -/
theorem member_mono_of_conjunctionEffect (m : Rat → Rat) (hm : Nondecreasing m) (K : Contrast)
    (S : Schema A V) (comb head : Proto A V) (I : Inst A V)
    (h : ConjunctionEffect K S comb head I) :
    m (sim K S head I) ≤ m (sim K S comb I) :=
  hm _ _ (Rat.le_of_lt h)

/-- The conjunction effect gives over-extension under any membership that
rises between the two similarities. -/
theorem overExtends_of_conjunctionEffect (m : Rat → Rat) (K : Contrast) (S : Schema A V)
    (comb head : Proto A V) (I : Inst A V) (h : ConjunctionEffect K S comb head I)
    (hrise : ∀ x y, sim K S head I ≤ x → x < y → y ≤ sim K S comb I → m x < m y) :
    OverExtends m K S comb head I :=
  hrise _ _ Rat.le_refl h Rat.le_refl

/-- The conjunction effect gives yes/no over-extension at some criterion:
the combination's similarity itself. -/
theorem overExtends_binary_of_conjunctionEffect (K : Contrast) (S : Schema A V)
    (comb head : Proto A V) (I : Inst A V) (h : ConjunctionEffect K S comb head I) :
    ∃ θ, OverExtendsBinary θ K S comb head I :=
  ⟨sim K S comb I, h, Rat.le_refl⟩

end Cog
