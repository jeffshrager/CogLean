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
  `CogLib/Phenomena/RetrievalLaws.lean`) gives a flat serial-position curve at 1. This is a
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

/-- **A flat serial-position curve, from laws alone.** With certainty and
stability, every item of a study list without repeats retrieves itself for
certain, whatever its position (`Laws.studied_selfRetrieval`). -/
theorem curve_flat (R : Retriever S Item) (s0 : S) (U : List Item) (hc : Certainty R s0 U)
    (hs : Stability R s0 U) (E : StudyTest) (hU : ∀ x ∈ E.study, x ∈ U) (hnd : E.study.Nodup) :
    ∀ r ∈ E.curve R s0, r = 1 := by
  intro r hr
  simp only [StudyTest.curve, List.mem_map] at hr
  obtain ⟨y, hy, rfl⟩ := hr
  exact studied_selfRetrieval R s0 U hc hs E.study hU hnd y hy

end Cog.Exp
