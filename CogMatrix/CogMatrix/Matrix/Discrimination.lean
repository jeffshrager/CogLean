/-
The discrimination family (EPAM's nets) against the laws.

Regime: learning from an empty net, on a set of stimuli `U` that are pairwise
noticeably different (for `Certainty`), or any set (for `Stability`).

* `certainty`: has it. A stimulus just learned is recognized.
* `stability`: has it. Learning is local.
* `not_orderFree`: lacks it. The net depends on the order of learning.
* `not_recency`: lacks it. Nothing in a net records when learning happened.
* `storedOnly`: has it. A probe retrieves a stored image or nothing.
-/

import CogMatrix.Matrix.Common

namespace Cog.Matrix.Discrimination

open Laws Dist

variable (order : NoticingOrder)

theorem pRet_net (N : Net) (x y : Item) :
    pRet (netRetriever order) N x y = if N.select x == some y then 1 else 0 := by
  simp only [pRet, netRetriever, IncrementalLearner.toRetriever, netLearner, prob_pure]

theorem images_learnAll (xs : List Item) :
    ∀ N : Net, ∀ z ∈ (N.learnAll order xs).images, z ∈ N.images ∨ z ∈ xs := by
  induction xs with
  | nil => intro N z hz; left; simpa [Net.learnAll] using hz
  | cons a rest ih =>
    intro N z hz
    rcases ih (N.learn order a) z (by simpa [Net.learnAll] using hz) with h | h
    · rcases Net.images_learn_subset order N a z h with h' | h'
      · right; simp [h']
      · left; exact h'
    · right; simp [h]

/-- A net reached from the empty one is clean, and stores only stimuli of
`U`. -/
theorem reach (U : List Item) (N : Net) (hN : Reachable (netRetriever order) (Net.leaf none) U N) :
    Net.Clean N ∧ ∀ z ∈ N.images, z ∈ U := by
  obtain ⟨xs, hxs, rfl⟩ := hN
  refine ⟨Net.learnAll_clean order xs _ Net.clean_empty, fun z hz => ?_⟩
  rcases images_learnAll order xs _ z hz with h | h
  · simp [Net.images] at h
  · exact hxs z h

/-- **Discrimination has certainty**, on pairwise noticeable stimuli. -/
theorem certainty (U : List Item) (hU : PairwiseNoticeable order U) :
    Certainty (netRetriever order) (Net.leaf none) U := by
  intro N hN y hy
  obtain ⟨_, hsub⟩ := reach order U N hN
  have hr : (N.learn order y).select y = some y :=
    Net.learn_recognizes order N y fun z hz hzy => hU y hy z (hsub z hz) hzy
  show pRet _ (N.learn order y) y y = 1
  rw [pRet_net, hr]
  simp

/-- What a probe retrieves is a stored image. -/
theorem select_ne (N : Net) (y : Item) (hy : y ∉ N.images) : (N.select y == some y) = false := by
  cases h : N.select y with
  | none => rfl
  | some w =>
    have hw := Net.select_mem_images N y w h
    apply Bool.eq_false_iff.mpr
    intro hb
    have hwy : w = y := by simpa using hb
    rw [hwy] at hw
    exact hy hw

/-- **Discrimination has stability.** -/
theorem stability (U : List Item) : Stability (netRetriever order) (Net.leaf none) U := by
  intro N hN y _ z _ hzy
  obtain ⟨hc, _⟩ := reach order U N hN
  show pRet _ (N.learn order z) y y = pRet _ N y y
  rw [pRet_net, pRet_net]
  by_cases hyi : y ∈ N.images
  · have h1 : N.select y = some y := hc.2 y hyi
    have h2 : (N.learn order z).select y = some y := Net.learn_preserves order N z y h1 (Ne.symm hzy)
    rw [h1, h2]
  · have hyi' : y ∉ (N.learn order z).images := by
      intro h
      rcases Net.images_learn_subset order N z y h with h' | h'
      · exact hzy h'.symm
      · exact hyi h'
    rw [select_ne N y hyi, select_ne _ y hyi']

/-- The all-or-none stable retrieval follows, since nets retrieve
deterministically. -/
theorem stableRetrievalOn (U : List Item) :
    StableRetrievalOn (netRetriever order) (Net.leaf none) U :=
  stableRetrievalOn_of_stability _ _ _ (netRetriever_deterministic order) (stability order U)

/-- **Discrimination is not order-free.** After 000, learning 100 then 010
gives a different net from learning 010 then 100, and the probe 110 is
retrieved differently. -/
theorem not_orderFree : ¬ OrderFree (netRetriever F3) (Net.leaf none) U3 := by
  intro h
  have := h ((netRetriever F3).studyAll (Net.leaf none) [bits 0]) ⟨_, by decide, rfl⟩
    (bits 1) (by decide) (bits 2) (by decide) (bits 3)
  revert this
  decide +kernel

/-- **Discrimination lacks recency.** After learning 000 and then 110, the
probe 010, one bit from each, does not retrieve the later one more often. -/
theorem not_recency : ¬ Recency F3 (netRetriever F3) (Net.leaf none) U3 := by
  intro h
  have := h [] (by decide) (bits 0) (by decide) (bits 3) (by decide) (by decide) (by decide)
    (by decide) (bits 2) (by decide)
  revert this
  decide +kernel

/-- **Discrimination retrieves only what was learned.** -/
theorem storedOnly (U : List Item) : StoredOnly (netRetriever order) (Net.leaf none) U := by
  intro xs _ x y hy
  show pRet _ (Net.learnAll order (Net.leaf none) xs) x y = 0
  rw [pRet_net]
  cases h : (Net.learnAll order (Net.leaf none) xs).select x with
  | none => rfl
  | some w =>
    have hw := Net.select_mem_images _ x w h
    have hwx : w ∈ xs := by
      rcases images_learnAll order xs _ w hw with h' | h'
      · simp [Net.images] at h'
      · exact h'
    have hwy : w ≠ y := fun e => hy (e ▸ hwx)
    simp [hwy]

end Cog.Matrix.Discrimination
