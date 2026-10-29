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

`not_recency_of_orderFree`: no memory is both order-free and recent, wherever
recency can be tested.

The laws are neutral about mechanism, not about representation: stimuli are
binary codes, similarity is a count of mismatching features (`mismatches`),
and stored-only compares codes for identity.

How they relate to the all-or-none `StableRetrieval` (`Phenomena/Retriever`):
* `stableRetrievalOn_of_stability`: for a deterministic retriever,
  `Stability` gives `StableRetrieval` on the reachable states.
* `stableRetrieval_of_neverCertain`: a retriever that never retrieves
  anything for certain has `StableRetrieval` trivially.

Determinate retrieval (`Determinate`: every retrieval has a single outcome),
and what follows for studied items:
* `studied_selfRetrieval`: with certainty and stability, every item of a
  study list retrieves itself with probability 1;
* `retrieve_of_pRet_pos`, `retrieve_of_pRet_one`: under determinacy, a
  positive chance, or a chance of 1, is certainty.
These are what the recognize-retrieve composition needs
(`Process/RecognizeRetrieve`, `RR.confident_errors_of_laws`).
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

/-! ### Determinate retrieval, and what studied items retrieve -/

/-- **Determinate retrieval.** In every reachable state, every probe's
retrieval has a single outcome. As stated, this is structural; a family lacks
it when some probe has two different outcomes, each with positive
probability (`not_determinate_of_two`), which fails any probabilistic version
too. -/
def Determinate (R : Retriever S Item) (s0 : S) (U : List Item) : Prop :=
  ∀ s, Reachable R s0 U s → ∀ x, ∃ r, R.retrieve s x = Dist.pure r

theorem determinate_of_deterministic (R : Retriever S Item) (s0 : S) (U : List Item)
    (h : Deterministic R) : Determinate R s0 U :=
  fun s _ x => h s x

/-- Under determinacy, a positive chance of retrieving `y` is certainty. -/
theorem retrieve_of_pRet_pos (R : Retriever S Item) (s0 : S) (U : List Item)
    (hd : Determinate R s0 U) (s : S) (hs : Reachable R s0 U s) (x y : Item)
    (h : 0 < pRet R s x y) : R.retrieve s x = Dist.pure (some y) := by
  obtain ⟨r, hr⟩ := hd s hs x
  rw [pRet_pure R s x y r hr] at h
  rw [hr]
  cases hb : (r == some y)
  · rw [hb] at h; exact absurd h (by decide)
  · have : r = some y := by simpa using hb
    rw [this]

theorem retrieve_of_pRet_one (R : Retriever S Item) (s0 : S) (U : List Item)
    (hd : Determinate R s0 U) (s : S) (hs : Reachable R s0 U s) (x y : Item)
    (h : pRet R s x y = 1) : R.retrieve s x = Dist.pure (some y) :=
  retrieve_of_pRet_pos R s0 U hd s hs x y (by rw [h]; decide)

/-- A family lacks determinacy when some probe, in some reachable state, has
two different outcomes with positive probability. -/
theorem not_determinate_of_two (R : Retriever S Item) (s0 : S) (U : List Item) (s : S)
    (hs : Reachable R s0 U s) (x y1 y2 : Item) (hne : y1 ≠ y2)
    (h1 : 0 < pRet R s x y1) (h2 : 0 < pRet R s x y2) : ¬ Determinate R s0 U := by
  intro hd
  have e1 := retrieve_of_pRet_pos R s0 U hd s hs x y1 h1
  have e2 := retrieve_of_pRet_pos R s0 U hd s hs x y2 h2
  rw [e1] at e2
  have := Dist.pure_inj e2
  simp only [Option.some.injEq] at this
  exact hne this

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

/-- **Studied items retrieve themselves.** With certainty and stability, after
studying a list without repeats, every item on it retrieves itself with
probability 1. -/
theorem studied_selfRetrieval (R : Retriever S Item) (s0 : S) (U : List Item)
    (hc : Certainty R s0 U) (hs : Stability R s0 U) (xs : List Item)
    (hU : ∀ x ∈ xs, x ∈ U) (hnd : xs.Nodup) (y : Item) (hy : y ∈ xs) :
    pRet R (R.studyAll s0 xs) y y = 1 := by
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
  rw [hsplit, show pre ++ y :: post = (pre ++ [y]) ++ post by simp,
    stable_after R s0 U hs y hyU post (pre ++ [y]) (by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hpre x h
      · simp at h; exact h ▸ hyU) hpost,
    studyAll_append]
  exact hc _ ⟨pre, hpre, rfl⟩ y hyU

/-- **An order-free memory lacks recency**, wherever recency can be tested:
two distinct stimuli of `U` and a probe equally similar to both. Studying
them in either order leaves the same retrieval, so neither order can favour
the later item. -/
theorem not_recency_of_orderFree (fs : List Feature) (R : Retriever S Item) (s0 : S)
    (U : List Item) (hof : OrderFree R s0 U) (a b x : Item) (ha : a ∈ U) (hb : b ∈ U)
    (hab : a ≠ b) (hx : mismatches fs x a = mismatches fs x b) : ¬ Recency fs R s0 U := by
  intro hrec
  have h1 := hrec [] (by simp) a ha b hb hab (by simp) (by simp) x hx
  have h2 := hrec [] (by simp) b hb a ha (Ne.symm hab) (by simp) (by simp) x hx.symm
  have e := hof s0 ⟨[], by simp, rfl⟩ a ha b hb x
  simp only [List.nil_append, Retriever.studyAll, List.foldl_cons, List.foldl_nil, pRet, e] at h1 h2
  grind

end Laws
end Cog
