/-
Phenomena of learning, stated theory-neutrally, and how they relate.

* `NonInterference`: studying one stimulus never undoes the recognition of
  another.
* `ReachesCriterion`: from a given starting state, any list satisfying a
  condition is completely learned by studying each item once.
* `StimulusGeneralization`: a stimulus is recognized as another, already
  learned one.

The main result, `criterion_of_nonInterference`, says that a learner with
non-interference reaches criterion whenever each study succeeds. That's the
argument "local change ⇒ non-interference ⇒ criterion" made once, for every
theory whose learning is local in this sense.
-/

import CogLib.Phenomena.Learner

namespace Cog.Phenomena

open IncrementalLearner

variable {State Stim : Type}

/-- **Non-interference.** Studying `x` leaves every other recognized
stimulus recognized. -/
def NonInterference (L : IncrementalLearner State Stim) : Prop :=
  ∀ s x y, L.Recognizes s y → y ≠ x → L.Recognizes (L.study s x) y

/-- **Learning to criterion.** From state `s0`, every list satisfying
`Learnable` is completely learned with one study of each item. -/
def ReachesCriterion (L : IncrementalLearner State Stim) (s0 : State)
    (Learnable : List Stim → Prop) : Prop :=
  ∀ xs, Learnable xs → ∀ x ∈ xs, L.Recognizes (L.studyAll s0 xs) x

/-- **Stimulus generalization.** In state `s`, a stimulus `y` is recognized
as a different stimulus `x` that has itself been learned. -/
def StimulusGeneralization (L : IncrementalLearner State Stim) (s : State) (x y : Stim) :
    Prop :=
  y ≠ x ∧ L.Recognizes s x ∧ L.recognizedAs s y = some x

/-- With non-interference, what is recognized stays recognized through any
study of other stimuli. -/
theorem studyAll_preserves (L : IncrementalLearner State Stim) (hni : NonInterference L) :
    ∀ (xs : List Stim) (s : State) (y : Stim),
      L.Recognizes s y → y ∉ xs → L.Recognizes (L.studyAll s xs) y := by
  intro xs
  induction xs with
  | nil => intro s y h _; simpa [studyAll] using h
  | cons a rest ih =>
    intro s y hy hnot
    simp only [List.mem_cons, not_or] at hnot
    have h1 := hni s a y hy hnot.1
    simpa [studyAll] using ih (L.study s a) y h1 hnot.2

/-- **Non-interference plus successful study gives criterion.** Suppose
an invariant `Inv` of the learner's state is kept by studying any item of
`xs`, and, while it holds, studying an item of `xs` makes it recognized. Then
studying `xs` once through leaves every item of `xs` recognized. -/
theorem studyAll_recognizes (L : IncrementalLearner State Stim) (hni : NonInterference L)
    (Inv : State → Prop) (xs : List Stim)
    (hinv : ∀ s x, x ∈ xs → Inv s → Inv (L.study s x))
    (hsucc : ∀ s x, x ∈ xs → Inv s → L.Recognizes (L.study s x) x) :
    ∀ s, Inv s → ∀ x ∈ xs, L.Recognizes (L.studyAll s xs) x := by
  induction xs with
  | nil => intro s _ x hx; simp at hx
  | cons a rest ih =>
    intro s hs x hx
    have ih' := ih (fun s x hx => hinv s x (List.mem_cons_of_mem a hx))
      (fun s x hx => hsucc s x (List.mem_cons_of_mem a hx))
    have hs' := hinv s a (List.mem_cons_self ..) hs
    by_cases hr : x ∈ rest
    · simpa [studyAll] using ih' (L.study s a) hs' x hr
    · have hxa : x = a := by
        rcases List.mem_cons.mp hx with h | h
        · exact h
        · exact absurd h hr
      subst hxa
      have h1 := hsucc s x (List.mem_cons_self ..) hs
      simpa [studyAll] using studyAll_preserves L hni rest (L.study s x) x h1 hr

/-- **Criterion from non-interference**, as a phenomenon: if every list
satisfying `Learnable` has an invariant, holding at `s0`, under which study
of its items succeeds and which study keeps, then the learner reaches
criterion on those lists. -/
theorem criterion_of_nonInterference (L : IncrementalLearner State Stim)
    (hni : NonInterference L) (s0 : State) (Learnable : List Stim → Prop)
    (hinv : ∀ xs, Learnable xs → ∃ Inv : State → Prop, Inv s0 ∧
      (∀ s x, x ∈ xs → Inv s → Inv (L.study s x)) ∧
      (∀ s x, x ∈ xs → Inv s → L.Recognizes (L.study s x) x)) :
    ReachesCriterion L s0 Learnable := by
  intro xs hxs
  obtain ⟨Inv, h0, hk, hs⟩ := hinv xs hxs
  exact studyAll_recognizes L hni Inv xs hk hs s0 h0

end Cog.Phenomena
