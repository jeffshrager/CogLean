/-
Phenomena: retrieval, the probabilistic form of recognition.

A *retriever* is what a theory of memory offers the phenomena of recognition
when retrieval may be noisy: studying a stimulus changes its state, and in
each state a probe calls up a stored stimulus, or nothing, with
probabilities. A deterministic learner is the special case in which a probe
calls up one thing for certain (`IncrementalLearner.toRetriever`). A memory
with noisy retrieval, such as ACT-R's declarative memory, is a retriever that
is not of that form.

Laws a retriever may have, stated theory-neutrally:
* `StableRetrieval`: studying one stimulus leaves unchanged the retrieval of
  another that was retrieved for certain (non-interference, for retrieval).
  All-or-none; the probabilistic laws are in `Phenomena/RetrievalLaws`, with
  how they relate to this one.
* `AgreesOn`: whatever a probe can call up agrees with it on given features.

Results:
* `stableRetrieval_of_nonInterference`: a deterministic learner with
  non-interference has stable retrieval.
* `confusion_preserves_of`: under `AgreesOn`, a confusion preserves whatever
  those features determine.
-/

import CogLib.Phenomena.Learning
import CogLib.Rep.Distribution
import CogLib.Rep.Features

namespace Cog

/-- A retriever: studying a stimulus changes its state, and in each state a
probe calls up a distribution of stored stimuli (`none`: nothing). -/
structure Retriever (State Stim : Type) where
  study : State → Stim → State
  retrieve : State → Stim → Dist (Option Stim)

/-- A deterministic learner retrieves what it recognizes, for certain. -/
def IncrementalLearner.toRetriever {State Stim : Type} (L : IncrementalLearner State Stim) :
    Retriever State Stim :=
  ⟨L.study, fun s x => Dist.pure (L.recognizedAs s x)⟩

namespace Phenomena

variable {State Stim : Type}

/-- **Stable retrieval.** Studying `x` leaves unchanged the retrieval of every
other stimulus that was retrieved as itself for certain. -/
def StableRetrieval (R : Retriever State Stim) : Prop :=
  ∀ s x y, R.retrieve s y = Dist.pure (some y) → y ≠ x → R.retrieve (R.study s x) y = R.retrieve s y

/-- **Agreement on features.** Whatever the probe `x` can call up agrees with
`x` on every feature in `fs`. This is a property of one state and one probe,
used as a hypothesis (by MultiDigit's near misses), not a law of a memory
family: it is EPAM's confusion lemma (`Net.confusion_agrees_on_path`) in
theory-neutral form. -/
def AgreesOn (retrieve : Item → Dist (Option Item)) (x : Item) (fs : List Feature) : Prop :=
  ∀ y, (retrieve x).Possible (some y) → ∀ f ∈ fs, x.feat f = y.feat f

theorem stableRetrieval_of_nonInterference (L : IncrementalLearner State Stim)
    (h : NonInterference L) : StableRetrieval L.toRetriever := by
  intro s x y hy hyx
  have hy' : L.recognizedAs s y = some y := Dist.pure_inj hy
  have h2 : L.recognizedAs (L.study s x) y = some y := h s x y hy' hyx
  simp only [IncrementalLearner.toRetriever]
  rw [h2, hy']

/-- **A confusion preserves what the agreed features determine.** If whatever
`code x` can call up agrees with it on `fs`, and `fs` determines `P`, then a
stored `code q` that `code x` can call up has `P q = P x`. -/
theorem confusion_preserves_of {α β : Type} (retrieve : Item → Dist (Option Item))
    (code : α → Item) (fs : List Feature) (P : α → β) (hD : Determines code fs P) (x q : α)
    (hagree : AgreesOn retrieve (code x) fs) (hx : (retrieve (code x)).Possible (some (code q))) :
    P x = P q :=
  hD x q (hagree _ hx)

end Phenomena
end Cog
