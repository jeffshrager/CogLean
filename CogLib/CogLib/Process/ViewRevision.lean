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
import CogLib.Process.TypeSplit

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
  cues _ _ e := cues e
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

/-! ### Revising by views and by splitting types -/

/-- What a revision does: apply the view a cue retrieves to an action's
type, or split an action's type. -/
inductive SCue (C A : Type) where
  | view (c : C) (target : A)
  | split (inst : A)
  deriving DecidableEq

/-- Whether two actions have the same type. -/
def sameType (T : KNet A L) (a b : A) : Bool :=
  match T.parent a, T.parent b with
  | some p, some q => p == q
  | _, _ => false

/-- **The view-and-split learner.** A view retrieved by a cue is aimed at the
type of the failing action (`target`) and applied. When the failing action
shares its type with the action of an episode already explained, and the
theory still predicts that episode, re-interpreting the shared type would
break it: then the learner splits the type first (conflict-driven
differentiation), and re-interprets afterwards. A revision records what it
brought in and the type it was applied to. `fresh` names the new type;
`allowSplit` turns splitting off, for comparison. -/
def viewSplitReviser (K : VAConfig L) (code : C → Item) (retrieve : M → Item → Dist (Option Item))
    (viewOf : Item → Option (KNet A L × A)) (predicts : KNet A L → List A → Option Resp)
    [DecidableEq Resp] (target : Episode A Resp → Option A) (vcues : Episode A Resp → List C)
    (fresh : KNet A L → A → A) (allowSplit once : Bool) :
    Reviser (KNet A L) M A Resp (SCue C A) (Option (Item × A)) where
  predicts := predicts
  revise
    | .view c t, T, m => Dist.bind (retrieve m (code c)) fun r =>
        match r, r.bind viewOf, T.parent t with
        | some y, some (V, frame), some p =>
            Dist.bind (applyView K (retarget V frame p) T) fun T' => Dist.pure (T', m, some (y, p))
        | _, _, _ => Dist.pure (T, m, none)
    | .split i, T, m => Dist.pure (splitType T i (fresh T i), m, none)
  cues T done e := match target e with
    | none => []
    | some t =>
      if allowSplit && done.any (fun e' => match target e' with
          | some t' => sameType T t t' && predicts T e'.1 == some e'.2
          | none => false)
      then [SCue.split t] else (vcues e).map (SCue.view · t)
  once := once

/-- The view-and-split learner never changes memory. -/
theorem viewSplitReviser_mem [DecidableEq Resp] (K : VAConfig L) (code : C → Item)
    (retrieve : M → Item → Dist (Option Item)) (viewOf : Item → Option (KNet A L × A))
    (predicts : KNet A L → List A → Option Resp) (target : Episode A Resp → Option A)
    (vcues : Episode A Resp → List C) (fresh : KNet A L → A → A) (allowSplit once : Bool)
    (c : SCue C A) (T : KNet A L) (m : M) :
    ∀ x ∈ (viewSplitReviser K code retrieve viewOf predicts target vcues fresh allowSplit once).revise
      c T m, x.1.2.1 = m := by
  intro x hx
  cases c with
  | split i => simp [viewSplitReviser, Dist.pure] at hx; rw [hx]
  | view c t =>
    obtain ⟨y, _, z, hz, hxz⟩ := mem_bind _ _ x hx
    rw [hxz]
    split at hz
    · obtain ⟨w, _, u, hu, hzu⟩ := mem_bind _ _ z hz
      simp [Dist.pure] at hu
      rw [hzu, hu]
    · simp [Dist.pure] at hz; rw [hz]

end Cog
