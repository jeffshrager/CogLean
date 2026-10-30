/-
Control: a serial mechanism, and attention to anchor points.

* A serial mechanism does one thing at a time, and each learning cycle takes
  a substantial, fixed amount of time. So if a trial leaves time for at most
  one learning cycle, `n` things to learn take at least `n` trials.
* Anchor points (EPAM's M3): items with features of uniqueness are attended
  to first, then the items next to those already learned. Stated as a rule
  over any set of anchors (`before`, `attentionRank`): items nearer an anchor
  first, the earlier of two equally near first.

Results:
* `trials_at_least_items`: learning time grows with the amount to be learned.
* `rank_lt_of_before`: for any anchors, an item nearer an anchor is learned
  on an earlier trial.
* `anchorAttention_serialPosition`: with the list's ends as anchors, the rule
  produces the serial position effect (`Phenomena.SerialPositionEffect`), a
  bowed error curve. Its companions say where the bow's minimum and rises are.
* `isolation_effect`: with a distinctive mid-list item as a further anchor,
  the same rule has that item learned on the second trial, where without it
  it comes no earlier than the third (the von Restorff effect).
-/

import CogLib.Phenomena.SerialPosition

namespace Cog

open Phenomena

/-- **Serial mechanism, unit processing time.** If after `t` trials at most
`t` items are learned, then learning `n` items takes at least `n` trials. -/
theorem trials_at_least_items (learned : Nat → Nat) (n T : Nat)
    (hunit : ∀ t, learned t ≤ t) (hcrit : n ≤ learned T) : n ≤ T :=
  Nat.le_trans hcrit (hunit T)

/-! ### Anchor-point attention, as a rule -/

/-- How far position `i` is from position `a`. -/
def gap (a i : Nat) : Nat := if a ≤ i then i - a else a - i

/-- How far position `i` is from the nearest anchor (at most `n`). -/
def nearestDist (n : Nat) (anchors : List Nat) (i : Nat) : Nat :=
  anchors.foldr (fun a m => min (gap a i) m) n

/-- **The attention rule** (EPAM's M3): items nearer an anchor are attended to
first, and of two equally near, the earlier in the list. `before j i`: `j` is
taken before `i`. -/
def before (n : Nat) (anchors : List Nat) (j i : Nat) : Bool :=
  nearestDist n anchors j < nearestDist n anchors i ||
    (nearestDist n anchors j == nearestDist n anchors i && j < i)

/-- The trial on which the rule takes item `i`, one learning cycle per trial
(the serial mechanism): the number of items it takes first. -/
def attentionRank (n : Nat) (anchors : List Nat) (i : Nat) : Nat :=
  ((List.range n).filter fun j => before n anchors j i).length

/-- A filter by a weaker predicate is no longer; strictly shorter if some
element satisfies only the stronger one. -/
theorem filter_length_le {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x → q x) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.filter_cons]
    by_cases hp : p x
    · have hq := h x List.mem_cons_self hp
      simp [hp, hq]; omega
    · by_cases hq : q x <;> simp [hp, hq] <;> omega

theorem filter_length_lt {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x → q x)
    (x : α) (hx : x ∈ l) (hqx : q x = true) (hpx : p x = false) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    have hle := filter_length_le l p q (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.filter_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [hpx, hqx]; omega
    · have := ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) hx'
      by_cases hp : p y
      · have hq := h y List.mem_cons_self hp
        simp [hp, hq]; omega
      · by_cases hq : q y <;> simp [hp, hq] <;> omega

theorem before_trans (n : Nat) (an : List Nat) (a b c : Nat) (h1 : before n an a b = true)
    (h2 : before n an b c = true) : before n an a c = true := by
  simp only [before, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at *
  omega

theorem before_irrefl (n : Nat) (an : List Nat) (a : Nat) : before n an a a = false := by
  simp [before]

/-- **The rule orders learning by nearness, for any anchors**: an item taken
before another is learned on an earlier trial. -/
theorem rank_lt_of_before (n : Nat) (an : List Nat) (i j : Nat) (hj : i < n)
    (h : before n an i j = true) : attentionRank n an i < attentionRank n an j :=
  filter_length_lt _ _ _ (fun x _ hx => before_trans n an x i j hx h) i (List.mem_range.mpr hj) h
    (before_irrefl n an i)

/-- With the two ends as anchors, the nearest-anchor distance is the distance
from the nearer end. -/
theorem nearestDist_ends (n i : Nat) (hi : i < n) :
    nearestDist n [0, n - 1] i = distFromEnds n i := by
  simp only [nearestDist, List.foldr_cons, List.foldr_nil, gap, distFromEnds]
  split <;> split <;> omega

/-- The trial on which item `i` is learned, attention working inward from
both ends: the rule, with the ends as anchors. -/
def learnedOnTrial (n i : Nat) : Nat := attentionRank n [0, n - 1] i

/-- The rule reproduces the earlier closed-form schedule: learned on trial
`2 × distance from the nearer end`, plus one for the back item of a pair.
Checked for every list of up to 15 items (a bounded check, by evaluation). -/
theorem learnedOnTrial_closed_form : ∀ n, n < 16 → ∀ i, i < n →
    learnedOnTrial n i = 2 * distFromEnds n i + (if i ≤ n - 1 - i then 0 else 1) := by
  decide +kernel

/-- In serial anticipation the item at position `i` is wrong on every trial
before it is learned. -/
def errorsAt (n i : Nat) : Nat := learnedOnTrial n i

/-- An item further from its nearer end collects strictly more errors. -/
theorem errorsAt_lt_of_dist_lt (n i j : Nat) (hi : i < n) (hj : j < n)
    (h : distFromEnds n i < distFromEnds n j) : errorsAt n i < errorsAt n j := by
  apply rank_lt_of_before n _ i j hi
  simp only [before, nearestDist_ends n i hi, nearestDist_ends n j hj, Bool.or_eq_true,
    decide_eq_true_eq]
  exact Or.inl h

/-- **Anchor-point attention produces the serial position effect**: derived
from the attention rule, with the list's ends as its anchors. -/
theorem anchorAttention_serialPosition (n : Nat) : SerialPositionEffect n (errorsAt n) :=
  fun i j hi hj h => errorsAt_lt_of_dist_lt n i j hi hj h

/-- The first position has the fewest errors of all: nothing is taken before it. -/
theorem first_position_fewest_errors (n i : Nat) : errorsAt n 0 ≤ errorsAt n i := by
  have h0 : errorsAt n 0 = 0 := by
    simp only [errorsAt, learnedOnTrial, attentionRank, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro j _
    simp [before, nearestDist, gap]
  omega

/-- **The isolation effect** (von Restorff), from the same rule: an item made
distinctive, so an anchor too, is learned on the second trial, after the
first item, where without it it is learned no earlier than the third. -/
theorem isolation_effect (n m : Nat) (h0 : 0 < m) (h1 : m < n - 1) :
    attentionRank n [0, n - 1, m] m = 1 ∧ 2 ≤ attentionRank n [0, n - 1] m := by
  constructor
  · have hd : ∀ j, j < n → (nearestDist n [0, n - 1, m] j = 0 ↔ j = 0 ∨ j = n - 1 ∨ j = m) := by
      intro j hj
      simp only [nearestDist, List.foldr_cons, List.foldr_nil, gap]
      split <;> split <;> split <;> omega
    have hm : nearestDist n [0, n - 1, m] m = 0 := (hd m (by omega)).mpr (Or.inr (Or.inr rfl))
    have hf : ((List.range n).filter fun j => before n [0, n - 1, m] j m) = [0] := by
      have : ∀ j ∈ List.range n, before n [0, n - 1, m] j m = (j == 0) := by
        intro j hj
        have hj' := List.mem_range.mp hj
        simp only [before, hm, Nat.not_lt_zero, decide_false, Bool.false_or]
        by_cases hj0 : j = 0
        · subst hj0; simp [(hd 0 (by omega)).mpr (Or.inl rfl), h0]
        · have : ¬ (nearestDist n [0, n - 1, m] j = 0 ∧ j < m) := by
            rintro ⟨hz, hlt⟩
            rcases (hd j hj').mp hz with h | h | h <;> omega
          rw [show (j == 0) = false from by simp [hj0]]
          by_cases hz : nearestDist n [0, n - 1, m] j = 0
          · simp only [hz, beq_self_eq_true, Bool.true_and, decide_eq_false_iff_not]
            exact fun hlt => this ⟨hz, hlt⟩
          · simp [hz]
      rw [List.filter_congr this]
      cases n with
      | zero => omega
      | succ k => simp [List.range_succ_eq_map, List.filter_map]
    simp [attentionRank, hf]
  · have hm : 1 ≤ distFromEnds n m := by simp only [distFromEnds]; omega
    have h0' : before n [0, n - 1] 0 m = true := by
      simp only [before, nearestDist_ends n 0 (by omega), nearestDist_ends n m (by omega)]
      simp [distFromEnds]; omega
    have hlast : before n [0, n - 1] (n - 1) m = true := by
      simp only [before, nearestDist_ends n (n - 1) (by omega), nearestDist_ends n m (by omega)]
      simp [distFromEnds]; omega
    simp only [attentionRank]
    generalize hL : ((List.range n).filter fun j => before n [0, n - 1] j m) = L
    have ha : 0 ∈ L := by rw [← hL]; exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), h0'⟩
    have hb : n - 1 ∈ L := by rw [← hL]; exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), hlast⟩
    match L, ha, hb with
    | [x], ha, hb =>
      simp only [List.mem_singleton] at ha hb
      omega
    | _ :: _ :: _, _, _ => simp

/-- Errors rise from the front of the list toward the middle. -/
theorem errors_rise_toward_middle (n i j : Nat) (hj : j < n) (hij : i ≤ j) (hjm : j ≤ n - 1 - j) :
    errorsAt n i ≤ errorsAt n j := by
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact Nat.le_of_lt (rank_lt_of_before n _ i j (by omega) (by
      simp only [before, nearestDist_ends n i (by omega), nearestDist_ends n j hj, distFromEnds]
      simp; omega))
  · subst h; exact Nat.le_refl _

end Cog
