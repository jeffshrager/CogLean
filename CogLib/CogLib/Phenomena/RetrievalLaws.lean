/-
Phenomena: laws of retrieval, theory-neutral properties a memory may have or
lack.

A law is stated about a `Retriever` (study a stimulus; retrieve, for a probe,
a distribution over stored stimuli), relative to a starting state `s0` and a
set of stimuli `U` that may be studied. It names no mechanism. The laws are
probabilistic, and each is shown to separate memory families
(`CogMatrix/`): an all-or-none law can hold vacuously for a family in which
nothing is ever certain (`stableRetrieval_of_neverCertain`).

* `Certainty`: a stimulus just studied is retrieved, for certain.
* `Stability`: studying one stimulus leaves the chance of retrieving another
  (probed with itself) unchanged.
* `OrderFree`: swapping the last two study events doesn't change retrieval.
  It concerns only the last two events, and only retrieval must agree, not
  the memory state, so a swap in mid-history followed by more study is not
  covered.
* `Recency`: of two stimuli studied last, and equally similar to the probe,
  the later is retrieved more often.
* `StoredOnly`: nothing is retrieved that was not studied.

The laws are neutral about mechanism, not about representation: stimuli are
binary codes, similarity is a count of mismatching features (`mismatches`),
and stored-only compares codes for identity.

How they relate to the all-or-none `StableRetrieval` (`Phenomena/Retriever`):
* `stableRetrievalOn_of_stability`: for a deterministic retriever,
  `Stability` gives `StableRetrieval` on the reachable states.
* `stableRetrieval_of_neverCertain`: a retriever that never retrieves
  anything for certain has `StableRetrieval` trivially.
-/

import CogLib.Phenomena.Retriever
import CogLib.Rep.Distribution
import CogLib.Rep.Features

namespace Cog

/-- Study a list of stimuli, in order. -/
def Retriever.studyAll {S Stim : Type} (R : Retriever S Stim) (s : S) (xs : List Stim) : S :=
  xs.foldl R.study s

namespace Laws

open Dist

variable {S : Type}

/-- The chance that probe `x` retrieves `y`. -/
def pRet (R : Retriever S Item) (s : S) (x y : Item) : Rat := prob (R.retrieve s x) (· == some y)

/-- The states reached from `s0` by studying stimuli of `U`. -/
def Reachable (R : Retriever S Item) (s0 : S) (U : List Item) (s : S) : Prop :=
  ∃ xs : List Item, (∀ x ∈ xs, x ∈ U) ∧ R.studyAll s0 xs = s

/-- **Certainty.** A stimulus just studied is retrieved by itself, for
certain. -/
def Certainty (R : Retriever S Item) (s0 : S) (U : List Item) : Prop :=
  ∀ s, Reachable R s0 U s → ∀ y ∈ U, pRet R (R.study s y) y y = 1

/-- **Stability.** Studying `z` leaves the chance that `y` retrieves itself
unchanged. -/
def Stability (R : Retriever S Item) (s0 : S) (U : List Item) : Prop :=
  ∀ s, Reachable R s0 U s → ∀ y ∈ U, ∀ z ∈ U, z ≠ y → pRet R (R.study s z) y y = pRet R s y y

/-- **Order-freedom.** Studying `a` then `b` leaves memory retrieving exactly
as studying `b` then `a` does. -/
def OrderFree (R : Retriever S Item) (s0 : S) (U : List Item) : Prop :=
  ∀ s, Reachable R s0 U s → ∀ a ∈ U, ∀ b ∈ U, ∀ x,
    R.retrieve (R.study (R.study s a) b) x = R.retrieve (R.study (R.study s b) a) x

/-- **Recency.** If `a` and then `b`, neither studied before, are the last
stimuli studied, a probe equally similar to both (on the features `fs`)
retrieves `b` more often than `a`. -/
def Recency (fs : List Feature) (R : Retriever S Item) (s0 : S) (U : List Item) : Prop :=
  ∀ xs : List Item, (∀ x ∈ xs, x ∈ U) → ∀ a ∈ U, ∀ b ∈ U, a ≠ b → a ∉ xs → b ∉ xs →
    ∀ x, mismatches fs x a = mismatches fs x b →
      pRet R (R.studyAll s0 (xs ++ [a, b])) x a < pRet R (R.studyAll s0 (xs ++ [a, b])) x b

/-- **Stored-only retrieval.** From `s0`, a stimulus that was never studied is
never retrieved, by any probe. -/
def StoredOnly (R : Retriever S Item) (s0 : S) (U : List Item) : Prop :=
  ∀ xs : List Item, (∀ x ∈ xs, x ∈ U) → ∀ x y, y ∉ xs → pRet R (R.studyAll s0 xs) x y = 0


/-! ### The all-or-none laws, related to these -/

/-- Every retrieval is certain of its outcome. -/
def Deterministic (R : Retriever S Item) : Prop :=
  ∀ s x, ∃ r, R.retrieve s x = Dist.pure r

/-- Stable retrieval on the states reached from `s0`, for stimuli of `U`. -/
def StableRetrievalOn (R : Retriever S Item) (s0 : S) (U : List Item) : Prop :=
  ∀ s, Reachable R s0 U s → ∀ x ∈ U, ∀ y ∈ U,
    R.retrieve s y = Dist.pure (some y) → y ≠ x → R.retrieve (R.study s x) y = R.retrieve s y

theorem stableRetrievalOn_of_stableRetrieval (R : Retriever S Item) (s0 : S) (U : List Item)
    (h : Phenomena.StableRetrieval R) : StableRetrievalOn R s0 U :=
  fun s _ x _ y _ hy hyx => h s x y hy hyx

theorem pRet_pure (R : Retriever S Item) (s : S) (x y : Item) (r : Option Item)
    (h : R.retrieve s x = Dist.pure r) : pRet R s x y = if (r == some y) then 1 else 0 := by
  simp only [pRet, h, prob_pure]

/-- **For a deterministic retriever, stability gives stable retrieval.** -/
theorem stableRetrievalOn_of_stability (R : Retriever S Item) (s0 : S) (U : List Item)
    (hd : Deterministic R) (hs : Stability R s0 U) : StableRetrievalOn R s0 U := by
  intro s hr x hx y hyU hy hyx
  have h1 : pRet R s y y = 1 := by rw [pRet_pure R s y y _ hy]; simp
  have h2 := hs s hr y hyU x hx (Ne.symm hyx)
  rw [h1] at h2
  obtain ⟨r, hr'⟩ := hd (R.study s x) y
  rw [pRet_pure R _ y y r hr'] at h2
  have hry : r = some y := by
    cases h : (r == some y)
    · rw [h] at h2; simp at h2
    · simpa using h
  rw [hr', hy, hry]

/-- **Vacuous stable retrieval.** If nothing is ever retrieved for certain,
`StableRetrieval` holds trivially: its hypothesis is never met. -/
theorem stableRetrieval_of_neverCertain (R : Retriever S Item)
    (h : ∀ s x y, R.retrieve s x ≠ Dist.pure (some y)) : Phenomena.StableRetrieval R :=
  fun s _ y hy _ => absurd hy (h s y y)

end Laws
end Cog
