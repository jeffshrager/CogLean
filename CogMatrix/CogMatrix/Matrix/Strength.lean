/-
The strength family (strength with sampling and a criterion) against the
laws.

* `orderFree`: has it, for every choice of parameters. Strengths only add.
* `not_certainty`, `not_stability`: lacks them. A similar stimulus competes
  for retrieval.
* `not_recency`: lacks it. Nothing records when study happened.
* `not_determinate`: lacks it. After 000 and 100, the probe 000 states each
  with positive probability.
* `storedOnly`: has it, for every choice of parameters. Only stimuli with
  strength are sampled, and only study gives strength.
-/

import CogMatrix.Matrix.Common
import CogMatrix.Families.Strength

namespace Cog.Matrix.Strength

open Laws Dist

theorem study_comm (P : StrParams) (s : StrState) (a b : Item) :
    Str.study P (Str.study P s a) b = Str.study P (Str.study P s b) a := by
  funext z
  simp only [Str.study]
  by_cases ha : z = a <;> by_cases hb : z = b <;> simp [ha, hb] <;> grind

/-- **Strength memory is order-free**, for every choice of parameters, from
every state. -/
theorem orderFree (P : StrParams) (s0 : StrState) (U : List Item) :
    OrderFree (strRetriever P) s0 U := by
  intro s _ a _ b _ x
  show Str.retrieve P (Str.study P (Str.study P s a) b) x =
    Str.retrieve P (Str.study P (Str.study P s b) a) x
  rw [study_comm]

/-- The instance for the counterexamples: all eight 3-bit codes, each
mismatch discounting by 3/4, increment 1, criterion 1/2, one search. -/
def P : StrParams := ⟨U3, F3, 3 / 4, 1, 1 / 2, 1⟩

/-- Nothing studied. -/
def s0 : StrState := fun _ => 0

/-- **Strength memory lacks certainty.** With 100 studied, 000 just studied
is retrieved by itself with probability 4/7: 100 competes. -/
theorem not_certainty : ¬ Certainty (strRetriever P) s0 U3 := by
  intro h
  have := h ((strRetriever P).studyAll s0 [bits 1]) ⟨_, by decide, rfl⟩ (bits 0) (by decide)
  revert this
  decide +kernel

/-- **Strength memory lacks stability.** Studying 100 lowers the chance that
000 retrieves itself from 1 to 4/7. -/
theorem not_stability : ¬ Stability (strRetriever P) s0 U3 := by
  intro h
  have := h ((strRetriever P).studyAll s0 [bits 0]) ⟨_, by decide, rfl⟩ (bits 0) (by decide)
    (bits 1) (by decide) (by decide)
  revert this
  decide +kernel

/-- **Strength memory lacks recency.** After 000 and then 110, the probe
010 retrieves each equally often. -/
theorem not_recency : ¬ Recency F3 (strRetriever P) s0 U3 := by
  intro h
  have := h [] (by decide) (bits 0) (by decide) (bits 3) (by decide) (by decide) (by decide)
    (by decide) (bits 2) (by decide)
  revert this
  decide +kernel

/-- **Strength memory is not determinate.** -/
theorem not_determinate : ¬ Determinate (strRetriever P) s0 U3 :=
  not_determinate_of_two _ _ _ _ ⟨[bits 0, bits 1], by decide, rfl⟩ (bits 0) (bits 0) (bits 1)
    (by decide) (by decide +kernel) (by decide +kernel)

theorem sum_zero (l : List Rat) (h : ∀ r ∈ l, r = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [List.sum_cons, h r (List.mem_cons_self ..),
      ih fun q hq => h q (List.mem_cons_of_mem r hq)]
    grind

/-- Search never states a stimulus with no strength. -/
theorem prob_search_zero (as : List Item) (w : Item → Rat) (cc : Rat) (y : Item) (hy : w y = 0)
    (e : Retrieval Item → Bool) (he : ∀ a k, a ≠ y → e (.stated a k) = false)
    (hex : e .exhausted = false) : ∀ n k, prob (search as w cc k n) e = 0 := by
  intro n
  induction n with
  | zero => intro k; simp [search, prob_pure, hex]
  | succ n ih =>
    intro k
    simp only [search]
    rw [prob_bind_sum]
    apply sum_zero
    intro r hr
    simp only [sample, List.map_map, List.mem_map, Function.comp] at hr
    obtain ⟨a, _, rfl⟩ := hr
    by_cases ha : a = y
    · subst ha; simp [hy, Rat.div_def]
    · by_cases hab : above w cc a = true
      · simp [hab, prob_pure, he a (k + 1) ha]
      · simp [hab, ih (k + 1)]

/-- Strength stays 0 for what is never studied. -/
theorem studyAll_unstudied (P : StrParams) (y : Item) :
    ∀ (xs : List Item) (s : StrState), y ∉ xs → (strRetriever P).studyAll s xs y = s y := by
  intro xs
  induction xs with
  | nil => intro s _; rfl
  | cons z xs ih =>
    intro s hy
    simp only [List.mem_cons, not_or] at hy
    show (strRetriever P).studyAll (Str.study P s z) xs y = s y
    rw [ih _ hy.2]
    simp [Str.study, Ne.symm hy.1, hy.1]

/-- **Strength memory retrieves only what was studied**, for every choice of
parameters. -/
theorem storedOnly (P : StrParams) (U : List Item) : StoredOnly (strRetriever P) s0 U := by
  intro xs _ x y hy
  have hzero : (strRetriever P).studyAll s0 xs y = 0 := studyAll_unstudied P y xs s0 hy
  show prob (Str.retrieve P _ x) _ = 0
  have hr : ∀ s : StrState, Str.retrieve P s x = Dist.bind (search P.items (Str.weight P s x) P.cc 0 P.n)
      fun r => Dist.pure (match r with | .stated a _ => some a | .exhausted => none) := by
    intro s
    unfold Str.retrieve
    congr
    funext r
    cases r <;> rfl
  rw [hr, prob_bind_pure]
  apply prob_search_zero
  · simp only [Str.weight]; rw [hzero]; exact Rat.zero_mul _
  · intro a k hak; simpa using hak
  · rfl

end Cog.Matrix.Strength
