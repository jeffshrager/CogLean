/-
The experiment layer, first piece: a study-test experiment, run with any
memory.

An experiment is written once against the `Retriever` interface, and any
memory family can be plugged in. A study-test experiment studies a list once,
in order, with no feedback. It then tests with a list of probes. Testing does
not change memory.

Measures:
* `curve`: accuracy by serial position, the chance that each studied item,
  probed with itself, retrieves itself;
* `claimsOld`: the chance that a probe retrieves some studied item;
* `retrievesItself`: the chance that a probe retrieves itself, which for an
  unstudied lure means retrieving something never studied.

Result:
* `curve_flat`: any memory with certainty and stability (laws in
  `CogMatrix/Laws.lean`) gives a flat serial-position curve at 1. This is a
  property of the experiment that follows from laws alone, so every family
  with those laws has it.
-/

import CogMatrix

namespace Cog.Exp

open Laws Dist

/-- A study-test experiment: a study list, then probes. -/
structure StudyTest where
  study : List Item
  probes : List Item

variable {S : Type}

namespace StudyTest

/-- Memory after the study phase. -/
def memory (E : StudyTest) (R : Retriever S Item) (s0 : S) : S := R.studyAll s0 E.study

/-- Accuracy by serial position. -/
def curve (E : StudyTest) (R : Retriever S Item) (s0 : S) : List Rat :=
  E.study.map fun y => pRet R (E.memory R s0) y y

/-- The chance that probe `p` retrieves some studied item. -/
def claimsOld (E : StudyTest) (R : Retriever S Item) (s0 : S) (p : Item) : Rat :=
  prob (R.retrieve (E.memory R s0) p) fun
    | some y => decide (y ∈ E.study)
    | none => false

/-- The chance that probe `p` retrieves itself. -/
def retrievesItself (E : StudyTest) (R : Retriever S Item) (s0 : S) (p : Item) : Rat :=
  pRet R (E.memory R s0) p p

end StudyTest

theorem studyAll_append (R : Retriever S Item) (s : S) (xs ys : List Item) :
    R.studyAll s (xs ++ ys) = R.studyAll (R.studyAll s xs) ys := by
  simp [Retriever.studyAll, List.foldl_append]

/-- Under stability, studying other items leaves an item's chance of
retrieving itself unchanged. -/
theorem stable_after (R : Retriever S Item) (s0 : S) (U : List Item) (hs : Stability R s0 U)
    (y : Item) (hy : y ∈ U) :
    ∀ (post pre : List Item), (∀ x ∈ pre, x ∈ U) → (∀ z ∈ post, z ∈ U ∧ z ≠ y) →
      pRet R (R.studyAll s0 (pre ++ post)) y y = pRet R (R.studyAll s0 pre) y y := by
  intro post
  induction post with
  | nil => intro pre _ _; simp
  | cons z post ih =>
    intro pre hpre hpost
    have hz := hpost z (List.mem_cons_self ..)
    have e : pre ++ z :: post = (pre ++ [z]) ++ post := by simp
    rw [e, ih (pre ++ [z]) (by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hpre x h
        · simp at h; exact h ▸ hz.1)
      (fun w hw => hpost w (List.mem_cons_of_mem z hw)),
      studyAll_append]
    exact hs _ ⟨pre, hpre, rfl⟩ y hy z hz.1 hz.2

/-- **A flat serial-position curve, from laws alone.** With certainty and
stability, every item of a study list without repeats retrieves itself for
certain, whatever its position. -/
theorem curve_flat (R : Retriever S Item) (s0 : S) (U : List Item) (hc : Certainty R s0 U)
    (hs : Stability R s0 U) (E : StudyTest) (hU : ∀ x ∈ E.study, x ∈ U) (hnd : E.study.Nodup) :
    ∀ r ∈ E.curve R s0, r = 1 := by
  intro r hr
  simp only [StudyTest.curve, List.mem_map] at hr
  obtain ⟨y, hy, rfl⟩ := hr
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hy
  have hyU := hU y hy
  have hpre : ∀ x ∈ pre, x ∈ U := fun x hx => hU x (by rw [hsplit]; simp [hx])
  have hnd' := hnd
  rw [hsplit] at hnd'
  have hyp : y ∉ post := by
    rw [List.nodup_append] at hnd'
    exact (List.nodup_cons.mp hnd'.2.1).1
  have hpost : ∀ z ∈ post, z ∈ U ∧ z ≠ y := fun z hz =>
    ⟨hU z (by rw [hsplit]; simp [hz]), fun e => hyp (e ▸ hz)⟩
  show pRet R (R.studyAll s0 E.study) y y = 1
  rw [hsplit, show pre ++ y :: post = (pre ++ [y]) ++ post by simp,
    stable_after R s0 U hs y hyU post (pre ++ [y]) (by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hpre x h
      · simp at h; exact h ▸ hyU) hpost,
    studyAll_append]
  exact hc _ ⟨pre, hpre, rfl⟩ y hyU

end Cog.Exp
