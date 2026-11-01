/-
Processes: recognize a cue, retrieve a view, apply it.

Shrager (1987, §3.4.1) left open how a learner comes to apply one view
rather than another. Here the view is *retrieved*: a cue (a key's label, a
feature of the display) is coded as features, any memory (`retrieve`, as in
`Process/RecognizeRetrieve`) calls up a stored code, and the view stored
with that code is applied to the theory (`Process/ViewApplication`). If
nothing is called up, or the code has no view, the theory is unchanged.
This has the shape of recognize-then-retrieve: which view a cue brings in
is decided by memory, so memories can be swapped.

* `retrieveView`: the resulting distribution over theories.
* `vtrial`: the same, read as a trial with routes. A retrieved view's
  application gives an answer by the *whole* route (here: a prediction read
  off the revised theory); with nothing retrieved, the learner explores
  (the *backup* route).

Main results, for any memory, cue code, views and theory:
* `retrieveView_certain`: with certain recognition, the view is fixed by
  what is recognized.
* `confusion_gives_neighbours_view`: a cue confused, for certain, with
  another brings in exactly the other's view.
* `view_of_determinate`: with a memory that has the law of determinacy
  (`Laws.Determinate`), each cue brings in one view, the same at every
  attempt and for every theory. So a learner that keeps consulting the same
  cue keeps applying the same view: perseveration, for a class of memories.
* `view_confusion_pattern`: the confusion-error pattern of
  `Phenomena/ConfusionErrors`, stated for arithmetic, holds here too: a
  cue confused with one whose view answers it correctly gets that view's
  answers, all wrong for it, with the same (zero) exploration. Given the
  conditions named.
-/

import CogLib.Process.ViewApplication
import CogLib.Process.RecognizeRetrieve

namespace Cog

open Dist

variable {A L C Ans : Type} [DecidableEq A] [DecidableEq L]

/-- Apply a view if there is one; otherwise leave the theory unchanged. -/
def applyOpt (K : VAConfig L) : Option (KNet A L) → KNet A L → Dist (KNet A L)
  | none, T => Dist.pure T
  | some V, T => applyView K V T

/-- **Recognize a cue, retrieve a view, apply it.** -/
def retrieveView (K : VAConfig L) (code : C → Item) (retrieve : Item → Dist (Option Item))
    (viewOf : Item → Option (KNet A L)) (T : KNet A L) (c : C) : Dist (KNet A L) :=
  Dist.bind (retrieve (code c)) fun r => applyOpt K (r.bind viewOf) T

/-- **View retrieval as a trial.** An applied view gives an answer (read off
the revised theory) by the whole route; with no view, the learner explores
(the backup route). -/
def vtrial (K : VAConfig L) (code : C → Item) (retrieve : Item → Dist (Option Item))
    (viewOf : Item → Option (KNet A L)) (T : KNet A L) (answer : C → KNet A L → Ans)
    (explore : C → Dist Ans) (c : C) : Dist (Route × Ans) :=
  Dist.bind (retrieve (code c)) fun r => match r.bind viewOf with
    | none => Dist.bind (explore c) fun a => Dist.pure (.backup, a)
    | some V => Dist.bind (applyView K V T) fun T' => Dist.pure (.whole, answer c T')

variable (K : VAConfig L) (code : C → Item) (retrieve : Item → Dist (Option Item))
  (viewOf : Item → Option (KNet A L))

/-- With certain recognition, the view applied is fixed by what is recognized. -/
theorem retrieveView_certain (T : KNet A L) (c : C) (r : Option Item)
    (h : retrieve (code c) = Dist.pure r) :
    retrieveView K code retrieve viewOf T c = applyOpt K (r.bind viewOf) T := by
  rw [retrieveView, h, bind_pure_left]

/-- **A confused cue brings in its neighbour's view.** If `x` calls up `y` for
certain, and so does `q`, the two cues revise every theory identically. -/
theorem confusion_gives_neighbours_view (T : KNet A L) (x q : C) (y : Item)
    (hx : retrieve (code x) = Dist.pure (some y)) (hq : retrieve (code q) = Dist.pure (some y)) :
    retrieveView K code retrieve viewOf T x = retrieveView K code retrieve viewOf T q := by
  rw [retrieveView_certain K code retrieve viewOf T x _ hx,
    retrieveView_certain K code retrieve viewOf T q _ hq]

/-- **Perseveration, for every determinate memory.** In any state reachable
by study, a memory with the law of determinacy makes each cue bring in one
view: the same at every attempt and for every theory. -/
theorem view_of_determinate {S : Type} (R : Retriever S Item) (s0 : S) (U : List Item)
    (hd : Laws.Determinate R s0 U) (s : S) (hs : Laws.Reachable R s0 U s) (c : C) :
    ∃ r : Option Item, ∀ T : KNet A L,
      retrieveView K code (R.retrieve s) viewOf T c = applyOpt K (r.bind viewOf) T := by
  obtain ⟨r, hr⟩ := hd s hs (code c)
  exact ⟨r, fun T => retrieveView_certain K code (R.retrieve s) viewOf T c r hr⟩

/-- Events that agree on a distribution's support have the same probability. -/
theorem prob_congr_mem {α : Type} (d : Dist α) (e e' : α → Bool)
    (h : ∀ ap ∈ d, e ap.1 = e' ap.1) : prob d e = prob d e' := by
  induction d with
  | nil => rfl
  | cons ap d ih =>
    obtain ⟨a, p⟩ := ap
    simp only [prob]
    rw [h (a, p) (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- An event false on a distribution's support has probability 0. -/
theorem prob_zero_of_mem {α : Type} (d : Dist α) (e : α → Bool) (h : ∀ ap ∈ d, e ap.1 = false) :
    prob d e = 0 := by
  rw [prob_congr_mem d e (fun _ => false) h, prob_false]

/-- **The confusion-error pattern, for view retrieval.** Let cue `q` call up
`y` for certain, and `x` call up `y` too; let `y`'s view, applied to the
theory, answer `q` correctly and `x` wrongly, on every outcome of the
application. Then the trial has the pattern of `Phenomena.ConfusionErrorPattern`:
`q` is never answered wrongly by an applied view, every answer an applied
view gives `x` is wrong, and the two explore equally often (never). The
phenomenon is the one stated for arithmetic; the mechanism is different. -/
theorem view_confusion_pattern [DecidableEq Ans] (T : KNet A L) (answer : C → KNet A L → Ans)
    (explore : C → Dist Ans) (correct : C → Ans) (x q : C) (y : Item) (V : KNet A L)
    (hq : retrieve (code q) = Dist.pure (some y)) (hx : retrieve (code x) = Dist.pure (some y))
    (hv : viewOf y = some V)
    (hcq : ∀ ap ∈ applyView K V T, answer q ap.1 = correct q)
    (hwx : ∀ ap ∈ applyView K V T, answer x ap.1 ≠ correct x) :
    Phenomena.ConfusionErrorPattern (vtrial K code retrieve viewOf T answer explore)
      (RR.wholeWrong correct) RR.isWhole RR.isBackup x q := by
  have hs : ∀ c, retrieve (code c) = Dist.pure (some y) →
      vtrial K code retrieve viewOf T answer explore c =
        Dist.bind (applyView K V T) fun T' => Dist.pure (Route.whole, answer c T') := by
    intro c hc
    rw [vtrial, hc, bind_pure_left]
    simp only [Option.bind_some, hv]
  refine ⟨?_, ?_, ?_⟩
  · rw [hs q hq, prob_bind_pure]
    exact prob_zero_of_mem _ _ fun ap hap => by
      simp [RR.wholeWrong, RR.wholeSuch, hcq ap hap]
  · rw [hs x hx, prob_bind_pure, prob_bind_pure]
    exact prob_congr_mem _ _ _ fun ap hap => by
      simp [RR.wholeWrong, RR.wholeSuch, RR.isWhole, hwx ap hap]
  · rw [hs x hx, hs q hq, prob_bind_pure, prob_bind_pure,
      prob_zero_of_mem _ _ fun _ _ => by simp [RR.isBackup],
      prob_zero_of_mem _ _ fun _ _ => by simp [RR.isBackup]]

end Cog
