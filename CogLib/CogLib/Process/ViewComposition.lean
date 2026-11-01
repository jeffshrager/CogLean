/-
Processes: composing views.

A view can be one part of a larger interpretation: one view says that a key
enters a number, another what the number means. Applied in turn, they build
the interpretation up. What makes this work is view application's merge:
on a matched frame the view wins only on the slots it mentions
(`merge_view_wins`); every other slot of the theory, including those an
earlier view supplied, survives.

* `merge_keeps_unmentioned`: a matched frame keeps every slot the view does
  not mention, renamed. So a later view keeps what an earlier one said
  about other slots, and a revision can replace one part of an
  interpretation (what a number means) and keep the rest (that the key
  enters a number).

Open: that views mentioning disjoint slots *commute* (either order gives the
same theory, up to the order of links). It holds in the cases certified in
`DeviceLearning`; a general proof must pass through coercion, binding and
single function (OPEN_ISSUES #26).
-/

import CogLib.Process.ViewApplication

namespace Cog

variable {A L : Type} [DecidableEq A] [DecidableEq L]

/-- **A view keeps what it does not mention.** A link of a matched theory
frame `f` (matched to the view's `b`) survives the merge, renamed, if the
view says nothing about that slot of `b`. -/
theorem merge_keeps_unmentioned (V T : KNet A L) (m : Matching A) (f b : A) (l : L) (t : Term A)
    (hm : m.lookup f = some b) (hv : V.targets (.atom b) l = []) (he : (.atom f, l, t) ∈ T.links) :
    (.atom b, l, rn m t) ∈ (merge V T m).links := by
  apply List.mem_append_right
  rw [List.mem_map]
  refine ⟨(.atom f, l, t), List.mem_filter.mpr ⟨he, by simp [survives, hm, hv]⟩, ?_⟩
  simp [rn, Term.rename, hm]

end Cog
