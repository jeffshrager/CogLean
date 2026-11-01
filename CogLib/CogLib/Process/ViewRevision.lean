/-
Processes: the view-application learner, one instance of learning by
revision (`Process/TheoryRevision`).

The theory is a knowledge net. A cue is coded and recognized by a memory
(any `retrieve`); the view stored with what it calls up is applied to the
theory (`Process/ViewRetrieval`). Memory is not changed by a revision, and
what a revision brings in is what the memory called up. How the theory
predicts is a parameter: `Process/TheoryExecution` gives one way, for
theories whose actions are frames with a meaning slot.

Main results:
* `viewReviser_theory`: the theories a revision gives are those of
  `retrieveView`.
* `viewReviser_mem`: revision does not change memory.
* `revise_same_of_determinate`: with a memory that has the law of
  determinacy, every revision by a given cue brings in one and the same
  retrieval, from every theory and at every attempt: perseveration, for a
  class of memories.
-/

import CogLib.Process.TheoryRevision
import CogLib.Process.ViewRetrieval

namespace Cog

open Dist

variable {A L M Act Resp C : Type} [DecidableEq A] [DecidableEq L]

/-- **The view-application learner.** -/
def viewReviser (K : VAConfig L) (code : C → Item) (retrieve : M → Item → Dist (Option Item))
    (viewOf : Item → Option (KNet A L)) (predicts : KNet A L → List Act → Option Resp)
    (cues : Episode Act Resp → List C) (once : Bool) : Reviser (KNet A L) M Act Resp C (Option Item) where
  predicts := predicts
  revise c T m := Dist.bind (retrieve m (code c)) fun r =>
    Dist.bind (applyOpt K (r.bind viewOf) T) fun T' => Dist.pure (T', m, r)
  cues := cues
  once := once

variable (K : VAConfig L) (code : C → Item) (retrieve : M → Item → Dist (Option Item))
  (viewOf : Item → Option (KNet A L)) (predicts : KNet A L → List Act → Option Resp)
  (cues : Episode Act Resp → List C) (once : Bool)

/-- The theories a revision gives are those of `retrieveView`. -/
theorem viewReviser_theory (c : C) (T : KNet A L) (m : M) :
    Dist.bind ((viewReviser K code retrieve viewOf predicts cues once).revise c T m)
        (fun x => Dist.pure x.1) = retrieveView K code (retrieve m) viewOf T c := by
  simp only [viewReviser, retrieveView, bind_assoc, bind_pure_left, bind_pure_right]

/-- Revision does not change memory. -/
theorem viewReviser_mem (c : C) (T : KNet A L) (m : M) :
    ∀ x ∈ (viewReviser K code retrieve viewOf predicts cues once).revise c T m, x.1.2.1 = m := by
  intro x hx
  obtain ⟨y, _, z, hz, hxz⟩ := mem_bind _ _ x hx
  obtain ⟨w, _, u, hu, hzu⟩ := mem_bind _ _ z hz
  simp [Dist.pure] at hu
  rw [hxz, hzu, hu]

/-- A revision by a cue that calls up `r` for certain brings in `r`. -/
theorem viewReviser_brings (c : C) (T : KNet A L) (m : M) (r : Option Item)
    (h : retrieve m (code c) = Dist.pure r) :
    ∀ x ∈ (viewReviser K code retrieve viewOf predicts cues once).revise c T m, x.1.2.2 = r := by
  intro x hx
  simp only [viewReviser, h, bind_pure_left] at hx
  obtain ⟨w, _, u, hu, hzu⟩ := mem_bind _ _ x hx
  simp [Dist.pure] at hu
  rw [hzu, hu]

/-- **Perseveration, for every determinate memory.** In a state reachable by
study, a memory with the law of determinacy makes every revision by a cue
bring in one and the same retrieval, from every theory and at every
attempt (memory is never changed by the loop, `viewReviser_mem`). -/
theorem revise_same_of_determinate [DecidableEq Resp] [DecidableEq C] {S : Type}
    (R : Retriever S Item) (s0 : S) (U : List Item) (hd : Laws.Determinate R s0 U)
    (code : C → Item) (viewOf : Item → Option (KNet A L)) (predicts : KNet A L → List Act → Option Resp)
    (cues : Episode Act Resp → List C) (once : Bool)
    (m : S) (hm : Laws.Reachable R s0 U m) (c : C) :
    ∃ r : Option Item, ∀ s : LState (KNet A L) S Act Resp C (Option Item), s.mem = m →
      ∀ x ∈ (viewReviser K code R.retrieve viewOf predicts cues once).space.apply (.revise c) s,
        x.1.adopted = s.adopted ++ [r] := by
  obtain ⟨r, hr⟩ := hd m hm (code c)
  exact ⟨r, fun s hs => revise_adopts _ c s r
    (viewReviser_brings K code R.retrieve viewOf predicts cues once c s.theory s.mem r (by rw [hs, hr]))⟩

end Cog
