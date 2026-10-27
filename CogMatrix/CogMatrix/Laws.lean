/-
Laws of retrieval: theory-neutral properties a memory may have or lack.

A law is stated about a `Retriever` (study a stimulus; retrieve, for a probe,
a distribution over stored stimuli), relative to a starting state `s0` and a
set of stimuli `U` that may be studied. It names no mechanism. Each law is
graded, in that it constrains probabilities, or is shown to separate
families (see `Matrix.lean`): an all-or-none law can be vacuous for a family
in which nothing is ever certain.

* `Certainty`: a stimulus just studied is retrieved, for certain.
* `Stability`: studying one stimulus leaves the chance of retrieving another
  (probed with itself) unchanged.
* `OrderFree`: the order of study doesn't matter to retrieval.
* `Recency`: of two stimuli studied last, and equally similar to the probe,
  the later is retrieved more often.
* `StoredOnly`: nothing is retrieved that was not studied.
-/

import CogLib

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

end Laws
end Cog
