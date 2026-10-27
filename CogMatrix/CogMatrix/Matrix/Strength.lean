/-
The strength family (strength with sampling and a criterion) against the
laws.

* `orderFree`: has it, for every choice of parameters. Strengths only add.
* `not_certainty`, `not_stability`: lacks them. A similar stimulus competes
  for retrieval.
* `not_recency`: lacks it. Nothing records when study happened.
-/

import CogMatrix.Matrix.Common
import CogMatrix.Families.Strength

namespace Cog.Matrix.Strength

open Laws Dist

theorem study_comm (P : StrParams) (s : StrState) (a b : Item) :
    Str.study P (Str.study P s a) b = Str.study P (Str.study P s b) a := by
  funext z
  simp only [Str.study]
  by_cases ha : z = a <;> by_cases hb : z = b <;> simp [ha, hb] <;> grind

/-- **Strength memory is order-free**, for every choice of parameters, from
every state. -/
theorem orderFree (P : StrParams) (s0 : StrState) (U : List Item) :
    OrderFree (strRetriever P) s0 U := by
  intro s _ a _ b _ x
  show Str.retrieve P (Str.study P (Str.study P s a) b) x =
    Str.retrieve P (Str.study P (Str.study P s b) a) x
  rw [study_comm]

/-- The instance for the counterexamples: all eight 3-bit codes, each
mismatch discounting by 3/4, increment 1, criterion 1/2, one search. -/
def P : StrParams := ⟨U3, F3, 3 / 4, 1, 1 / 2, 1⟩

/-- Nothing studied. -/
def s0 : StrState := fun _ => 0

/-- **Strength memory lacks certainty.** With 100 studied, 000 just studied
is retrieved by itself with probability 4/7: 100 competes. -/
theorem not_certainty : ¬ Certainty (strRetriever P) s0 U3 := by
  intro h
  have := h ((strRetriever P).studyAll s0 [bits 1]) ⟨_, by decide, rfl⟩ (bits 0) (by decide)
  revert this
  decide +kernel

/-- **Strength memory lacks stability.** Studying 100 lowers the chance that
000 retrieves itself from 1 to 4/7. -/
theorem not_stability : ¬ Stability (strRetriever P) s0 U3 := by
  intro h
  have := h ((strRetriever P).studyAll s0 [bits 0]) ⟨_, by decide, rfl⟩ (bits 0) (by decide)
    (bits 1) (by decide) (by decide)
  revert this
  decide +kernel

/-- **Strength memory lacks recency.** After 000 and then 110, the probe
010 retrieves each equally often. -/
theorem not_recency : ¬ Recency F3 (strRetriever P) s0 U3 := by
  intro h
  have := h [] (by decide) (bits 0) (by decide) (bits 3) (by decide) (by decide) (by decide)
    (by decide) (bits 2) (by decide)
  revert this
  decide +kernel

end Cog.Matrix.Strength
