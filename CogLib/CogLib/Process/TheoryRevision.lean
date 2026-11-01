/-
Processes: learning by revising a theory at failed predictions, on the
decision cycle of `Process/ProblemSolving`.

A learner acts, predicts the response with its current theory, and changes
the theory when a prediction fails (Shrager 1987's instructionless
learning). That is the shape of the decision cycle with impasses and
repairs, so the loop is an instance of it, not a new control structure:

| learning by revision                   | decision cycle                      |
|----------------------------------------|-------------------------------------|
| learner state: theory, memory, the episodes still to explain | state |
| accept the theory's prediction         | operator `confirm`, whose precondition is that the prediction matches the observed response |
| a failed prediction                    | an impasse (`impasse_iff_fails`)     |
| revise the theory, prompted by a cue   | repair operator `revise c`           |
| which cues to consult                  | repair heuristics                    |
| not consulting a cue again for the same failure (if `once`) | a critic |

Nothing here says what a theory is, how it predicts, or how it is revised.
A `Reviser` supplies only: how a theory predicts the response to a
sequence of actions, how a cue revises a theory (any process, with any
memory, giving a distribution), and which cues an episode offers. One
instance is view application with retrieved views (`Process/ViewRevision`);
others can be added and inherit these results.

Main results, for any theories, actions, responses, cues and reviser:
* `impasse_iff_fails`: the learner is at an impasse exactly when the
  current theory's prediction of the next episode fails.
* `correct_theory_stable`: a theory that predicts every episode is never
  revised.
* `revise_adopts`: a revision that brings in `b` on every outcome records
  `b`; `mem_fixed`: if the reviser never changes memory, no operator does.
-/

import CogLib.Process.ProblemSolving

namespace Cog

open Dist

/-- An episode: the actions taken, and the response observed. -/
abbrev Episode (Act Resp : Type) := List Act × Resp

/-- What a learner by revision needs: prediction, revision and cues. A
revision gives the new theory, the new memory, and what it brought in
(`B`), with probabilities. The cues a failed episode offers may depend on
the current theory and on the episodes already explained (so that, for
instance, a conflict with an explained episode can prompt a different kind
of revision). -/
structure Reviser (Θ M Act Resp C B : Type) where
  predicts : Θ → List Act → Option Resp
  revise : C → Θ → M → Dist (Θ × M × B)
  cues : Θ → List (Episode Act Resp) → Episode Act Resp → List C
  once : Bool

/-- The learner's state: the theory, the memory, the episodes still to
explain, the cues tried on the current one, what each revision brought in,
in order, and the episodes already explained. -/
structure LState (Θ M Act Resp C B : Type) where
  theory : Θ
  mem : M
  todo : List (Episode Act Resp)
  tried : List C
  adopted : List B
  done : List (Episode Act Resp) := []

/-- The operators. -/
inductive LOp (C : Type) where
  | confirm
  | revise (c : C)

variable {Θ M Act Resp C B : Type} [DecidableEq Resp] [DecidableEq C]
  (G : Reviser Θ M Act Resp C B)

/-- Whether the theory predicts an episode's response. -/
def Reviser.fits (T : Θ) (e : Episode Act Resp) : Bool := G.predicts T e.1 == some e.2

/-- The problem space of learning by revision. -/
def Reviser.space : Space (LState Θ M Act Resp C B) (LOp C) where
  pre
    | .confirm, s => match s.todo with
      | [] => true
      | e :: _ => G.fits s.theory e
    | .revise _, _ => true
  apply
    | .confirm, s => Dist.pure { s with todo := s.todo.tail, tried := [], done := s.done ++ s.todo.take 1 }
    | .revise c, s => Dist.bind (G.revise c s.theory s.mem) fun r =>
        Dist.pure ⟨r.fst, r.snd.fst, s.todo, c :: s.tried, s.adopted ++ [r.snd.snd], s.done⟩

/-- Keep confirming while episodes remain. -/
def Reviser.procedure (_ : Reviser Θ M Act Resp C B) : Procedure (LState Θ M Act Resp C B) (LOp C) :=
  fun s => if s.todo.isEmpty then none else some .confirm

/-- Repairs: consult the cues the failing episode offers; if `once`, each
cue only once per failure. -/
def Reviser.repairer : Repairer (LState Θ M Act Resp C B) (LOp C) where
  heuristics _ s := match s.todo with
    | [] => []
    | e :: _ => (G.cues s.theory s.done e).map .revise
  critic o s := match o with
    | .revise c => G.once && s.tried.contains c
    | .confirm => false

/-- **A learning session**: at most `k` decision cycles. -/
def Reviser.session (k : Nat) (s : LState Θ M Act Resp C B) : Dist (LState Θ M Act Resp C B) :=
  run G.space G.procedure G.repairer k s

/-- The same, with its trace of confirmations and revisions. -/
def Reviser.sessionTrace (k : Nat) (s : LState Θ M Act Resp C B) :
    Dist (LState Θ M Act Resp C B × List (Event (LOp C))) :=
  runTrace G.space G.procedure G.repairer k s

/-- **An impasse is a failed prediction.** -/
theorem impasse_iff_fails (s : LState Θ M Act Resp C B) :
    AtImpasse G.space G.procedure s ↔ ∃ e es, s.todo = e :: es ∧ G.fits s.theory e = false := by
  unfold AtImpasse Reviser.procedure
  cases h : s.todo with
  | nil => simp
  | cons e es =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, Option.some.injEq,
      exists_eq_left', List.cons.injEq]
    simp [Reviser.space, h]

/-- **A correct theory is never revised.** If the theory predicts every
episode still to explain, every outcome of the session keeps it. -/
theorem correct_theory_stable (k : Nat) (s : LState Θ M Act Resp C B)
    (h : ∀ e ∈ s.todo, G.fits s.theory e = true) :
    ∀ x ∈ G.session k s, x.1.theory = s.theory := by
  induction k generalizing s with
  | zero => intro x hx; simp [Reviser.session, run, Dist.pure] at hx; rw [hx]
  | succ k ih =>
    cases ht : s.todo with
    | nil =>
      have hp : G.procedure s = none := by simp [Reviser.procedure, ht]
      intro x hx
      simp only [Reviser.session, run, step, hp, bind_pure_left] at hx
      simp [Dist.pure] at hx
      rw [hx]
    | cons e es =>
      have hp : G.procedure s = some LOp.confirm := by simp [Reviser.procedure, ht]
      have hpre : G.space.pre .confirm s = true := by
        simp only [Reviser.space, ht]; exact h e (by simp [ht])
      intro x hx
      simp only [Reviser.session, run, step, hp, hpre, ite_true] at hx
      simp only [Reviser.space, bind_pure_left] at hx
      exact ih { s with todo := s.todo.tail, tried := [], done := s.done ++ s.todo.take 1 } (by
        intro e' he'; simp only [ht, List.tail_cons] at he'; exact h e' (by simp [ht, he'])) x hx

/-- If the reviser never changes memory, no operator does. -/
theorem mem_fixed (hG : ∀ c T m, ∀ x ∈ G.revise c T m, x.1.2.1 = m) (o : LOp C)
    (s : LState Θ M Act Resp C B) : ∀ x ∈ G.space.apply o s, x.1.mem = s.mem := by
  cases o with
  | confirm => intro x hx; simp [Reviser.space, Dist.pure] at hx; rw [hx]
  | revise c =>
    intro x hx
    obtain ⟨y, hy, z, hz, hxz⟩ := mem_bind _ _ x hx
    simp [Dist.pure] at hz
    rw [hxz, hz]
    exact hG c s.theory s.mem y hy

/-- A revision that brings in `b` on every outcome records `b`. -/
theorem revise_adopts (c : C) (s : LState Θ M Act Resp C B) (b : B)
    (h : ∀ x ∈ G.revise c s.theory s.mem, x.1.2.2 = b) :
    ∀ x ∈ G.space.apply (.revise c) s, x.1.adopted = s.adopted ++ [b] := by
  intro x hx
  obtain ⟨y, hy, z, hz, hxz⟩ := mem_bind _ _ x hx
  simp [Dist.pure] at hz
  rw [hxz, hz, h y hy]

end Cog
