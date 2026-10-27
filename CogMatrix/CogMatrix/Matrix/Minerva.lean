/-
The global-matching family (MINERVA 2) against the laws.

* `orderFree`: has it, for every choice of parameters. The echo is a sum over
  traces.
* `not_certainty`, `not_stability`: lacks them. Enough traces of a neighbour
  outweigh a stimulus's own.
* `not_recency`: lacks it. Nothing records when study happened.
* `not_storedOnly`: lacks it. Probed with the centre of three studied
  variants, memory returns the centre, never studied.

On the first four laws, global matching has the same row as strength memory.
Only stored-only retrieval separates them.
-/

import CogMatrix.Matrix.Common
import CogMatrix.Families.Minerva

namespace Cog.Matrix.Minerva

open Laws Dist Cog.Minerva

theorem sum_swap (s : MinState) (a b : Item) (g : Item → Rat) :
    (((s ++ [a]) ++ [b]).map g).sum = (((s ++ [b]) ++ [a]).map g).sum := by
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  grind

/-- **Global matching is order-free**, for every width, from every state. -/
theorem orderFree (P : MinParams) (s0 : MinState) (U : List Item) :
    OrderFree (minRetriever P) s0 U := by
  intro s _ a _ b _ x
  show retrieve P ((s ++ [a]) ++ [b]) x = retrieve P ((s ++ [b]) ++ [a]) x
  have hI : intensity P ((s ++ [a]) ++ [b]) x = intensity P ((s ++ [b]) ++ [a]) x :=
    sum_swap s a b _
  have hE : echo P ((s ++ [a]) ++ [b]) x = echo P ((s ++ [b]) ++ [a]) x := by
    unfold echo
    congr 1
    funext f
    rw [show content P ((s ++ [a]) ++ [b]) x f = content P ((s ++ [b]) ++ [a]) x f from
      sum_swap s a b _]
  unfold retrieve
  rw [hI, hE]

/-- Three features. -/
def P : MinParams := ⟨3⟩

/-- **Global matching lacks certainty.** After 27 traces of 000, a trace of
100 just stored: probed with 100, the echo is 000. -/
theorem not_certainty : ¬ Certainty (minRetriever P) [] U3 := by
  intro h
  have := h ((minRetriever P).studyAll [] (List.replicate 27 (bits 0))) ⟨_, by decide, rfl⟩
    (bits 1) (by decide)
  revert this
  decide +kernel

/-- **Global matching lacks stability.** With 100 and 26 traces of 000, 100
retrieves itself; one more trace of 000 and it retrieves 000. -/
theorem not_stability : ¬ Stability (minRetriever P) [] U3 := by
  intro h
  have := h ((minRetriever P).studyAll [] (bits 1 :: List.replicate 26 (bits 0)))
    ⟨_, by decide, rfl⟩ (bits 1) (by decide) (bits 0) (by decide) (by decide)
  revert this
  decide +kernel

/-- **Global matching lacks recency.** After 000 and then 110, the probe 010
returns 000, the earlier. -/
theorem not_recency : ¬ Recency F3 (minRetriever P) [] U3 := by
  intro h
  have := h [] (by decide) (bits 0) (by decide) (bits 3) (by decide) (by decide) (by decide)
    (by decide) (bits 2) (by decide)
  revert this
  decide +kernel

/-- **Global matching retrieves what was never studied.** After 110, 101 and
011, the probe 111 returns 111. -/
theorem not_storedOnly : ¬ StoredOnly (minRetriever P) [] U3 := by
  intro h
  have := h [bits 3, bits 5, bits 6] (by decide) (bits 7) (bits 7) (by decide)
  revert this
  decide +kernel

end Cog.Matrix.Minerva
