/-
Processes: learning a device by revising a theory at failed predictions,
on the decision cycle of `Process/ProblemSolving`.

Instructionless learning (Shrager 1987) alternates acting on a device,
predicting with the current theory, and changing the theory when a
prediction fails. That is the shape of the decision cycle with impasses
and repairs, so the loop is an instance of it, not a new control structure:

| learning a device                     | decision cycle                      |
|---------------------------------------|-------------------------------------|
| learner state: theory, memory, the episodes still to explain | state |
| accept the theory's prediction         | operator `confirm`, whose precondition is that the prediction matches the observation |
| a failed prediction                    | an impasse (`impasse_iff_fails`)     |
| change the theory by a view            | repair operator `revise c`: retrieve a view by cue `c` and apply it (`Process/ViewRetrieval`) |
| which cues to consult                  | repair heuristics (task data)        |
| not consulting a cue again for the same failure (if `once`) | a critic     |

The task supplies a `Learning` record: how to predict (`Process/TheoryExecution`),
what an episode offers as cues, how cues are coded, the memory, and the
views it stores. In this version memory is not changed by learning: a
revision retrieves but does not study.

Main results, for any device, views, cues and memory:
* `impasse_iff_fails`: the learner is at an impasse exactly when the
  current theory's prediction of the next episode fails.
* `correct_theory_stable`: a theory that predicts every episode is never
  revised.
* `revise_adopts`, `mem_fixed`: a revision by a cue that calls up `r` for
  certain adopts `r`, and no operator changes memory; with
  `view_of_determinate`, a determinate memory makes every revision by a
  given cue adopt the same view (perseveration).
-/

import CogLib.Process.ProblemSolving
import CogLib.Process.TheoryExecution
import CogLib.Process.ViewRetrieval

namespace Cog

open Dist

/-- An episode: the keys pressed, and what was observed. -/
abbrev Episode (A Obs : Type) := List A × Obs

/-- What a learner of a device needs. -/
structure Learning (A L C M St Obs : Type) where
  K : VAConfig L
  fnL : L
  den : Term A → St → Option St
  s0 : St
  out : St → Obs
  code : C → Item
  retrieve : M → Item → Dist (Option Item)
  viewOf : Item → Option (KNet A L)
  cues : Episode A Obs → List C
  once : Bool

/-- The learner's state: the theory, the memory, the episodes still to
explain, the cues tried on the current one, and what each revision called
up, in order. -/
structure LState (A L C M Obs : Type) where
  theory : KNet A L
  mem : M
  todo : List (Episode A Obs)
  tried : List C
  adopted : List (Option Item)

/-- The operators. -/
inductive LOp (C : Type) where
  | confirm
  | revise (c : C)

variable {A L C M St Obs : Type} [DecidableEq A] [DecidableEq L] [DecidableEq C] [DecidableEq Obs]
  (G : Learning A L C M St Obs)

/-- Whether the theory predicts an episode's observation. -/
def Learning.predicts (T : KNet A L) (e : Episode A Obs) : Bool :=
  (predict G.fnL G.den T e.1 G.s0).map G.out == some e.2

/-- The problem space of learning a device. -/
def Learning.space : Space (LState A L C M Obs) (LOp C) where
  pre
    | .confirm, s => match s.todo with
      | [] => true
      | e :: _ => G.predicts s.theory e
    | .revise _, _ => true
  apply
    | .confirm, s => Dist.pure { s with todo := s.todo.tail, tried := [] }
    | .revise c, s => Dist.bind (G.retrieve s.mem (G.code c)) fun r =>
        Dist.bind (applyOpt G.K (r.bind G.viewOf) s.theory) fun T' =>
          Dist.pure { s with theory := T', tried := c :: s.tried, adopted := s.adopted ++ [r] }

/-- Keep confirming while episodes remain. -/
def Learning.procedure (_ : Learning A L C M St Obs) : Procedure (LState A L C M Obs) (LOp C) :=
  fun s =>
  if s.todo.isEmpty then none else some .confirm

/-- Repairs: consult the cues the failing episode offers; if `once`, each
cue only once per failure. -/
def Learning.repairer : Repairer (LState A L C M Obs) (LOp C) where
  heuristics _ s := match s.todo with
    | [] => []
    | e :: _ => (G.cues e).map .revise
  critic o s := match o with
    | .revise c => G.once && s.tried.contains c
    | .confirm => false

/-- **A learning session**: at most `k` decision cycles. -/
def Learning.session (k : Nat) (s : LState A L C M Obs) : Dist (LState A L C M Obs) :=
  run G.space G.procedure G.repairer k s

/-- The same, with its trace of confirmations and revisions. -/
def Learning.sessionTrace (k : Nat) (s : LState A L C M Obs) :
    Dist (LState A L C M Obs × List (Event (LOp C))) :=
  runTrace G.space G.procedure G.repairer k s

/-- **An impasse is a failed prediction.** -/
theorem impasse_iff_fails (s : LState A L C M Obs) :
    AtImpasse G.space G.procedure s ↔ ∃ e es, s.todo = e :: es ∧ G.predicts s.theory e = false := by
  unfold AtImpasse Learning.procedure
  cases h : s.todo with
  | nil => simp
  | cons e es =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, Option.some.injEq,
      exists_eq_left', List.cons.injEq]
    simp [Learning.space, h]

/-- **A correct theory is never revised.** If the theory predicts every
episode still to explain, every outcome of the session keeps it. -/
theorem correct_theory_stable (k : Nat) (s : LState A L C M Obs)
    (h : ∀ e ∈ s.todo, G.predicts s.theory e = true) :
    ∀ x ∈ G.session k s, x.1.theory = s.theory := by
  induction k generalizing s with
  | zero => intro x hx; simp [Learning.session, run, Dist.pure] at hx; rw [hx]
  | succ k ih =>
    cases ht : s.todo with
    | nil =>
      have hp : G.procedure s = none := by simp [Learning.procedure, ht]
      intro x hx
      simp only [Learning.session, run, step, hp, bind_pure_left] at hx
      simp [Dist.pure] at hx
      rw [hx]
    | cons e es =>
      have hp : G.procedure s = some LOp.confirm := by simp [Learning.procedure, ht]
      have hpre : G.space.pre .confirm s = true := by
        simp only [Learning.space, ht]; exact h e (by simp [ht])
      intro x hx
      simp only [Learning.session, run, step, hp, hpre, ite_true] at hx
      simp only [Learning.space, bind_pure_left] at hx
      have := ih { s with todo := s.todo.tail, tried := [] } (by
        intro e' he'; simp only [ht, List.tail_cons] at he'; exact h e' (by simp [ht, he'])) x hx
      exact this

/-- No operator changes memory. -/
theorem mem_fixed (o : LOp C) (s : LState A L C M Obs) :
    ∀ x ∈ G.space.apply o s, x.1.mem = s.mem := by
  cases o with
  | confirm => intro x hx; simp [Learning.space, Dist.pure] at hx; rw [hx]
  | revise c =>
    intro x hx
    obtain ⟨y, _, z, hz, hxz⟩ := mem_bind _ _ x hx
    obtain ⟨w, _, u, hu, hzu⟩ := mem_bind _ _ z hz
    simp [Dist.pure] at hu
    rw [hxz, hzu, hu]

/-- A revision by a cue that calls up `r` for certain adopts `r`. -/
theorem revise_adopts (c : C) (s : LState A L C M Obs) (r : Option Item)
    (h : G.retrieve s.mem (G.code c) = Dist.pure r) :
    ∀ x ∈ G.space.apply (.revise c) s, x.1.adopted = s.adopted ++ [r] := by
  intro x hx
  simp only [Learning.space, h, bind_pure_left] at hx
  obtain ⟨w, _, u, hu, hzu⟩ := mem_bind _ _ x hx
  simp [Dist.pure] at hu
  rw [hzu, hu]

/-- **Perseveration, for every determinate memory.** In a state reachable by
study, a memory with the law of determinacy makes every revision by a cue
adopt one and the same retrieval, at every attempt and from every theory
(memory is never changed by the loop, `mem_fixed`). -/
theorem revise_same_of_determinate {S : Type} (R : Retriever S Item) (s0 : S) (U : List Item)
    (hd : Laws.Determinate R s0 U) (G : Learning A L C S St Obs) (hG : G.retrieve = R.retrieve)
    (m : S) (hm : Laws.Reachable R s0 U m) (c : C) :
    ∃ r : Option Item, ∀ s : LState A L C S Obs, s.mem = m →
      ∀ x ∈ G.space.apply (.revise c) s, x.1.adopted = s.adopted ++ [r] := by
  obtain ⟨r, hr⟩ := hd m hm (G.code c)
  exact ⟨r, fun s hs => revise_adopts G c s r (by rw [hG, hs, hr])⟩

end Cog
