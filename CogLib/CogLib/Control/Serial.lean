/-
Control: a serial mechanism, and attention to anchor points.

* A serial mechanism does one thing at a time, and each learning cycle takes
  a substantial, fixed amount of time. So if a trial leaves time for at most
  one learning cycle, `n` things to learn take at least `n` trials.
* Anchor points: items with features of uniqueness are attended to first,
  then the items next to those already learned. In a serial list the two
  ends are the anchors, so attention works inward from both ends.

Results:
* `trials_at_least_items`: learning time grows with the amount to be learned.
* `anchorAttention_serialPosition`: inward attention from the ends produces
  the serial position effect (`Phenomena.SerialPositionEffect`), a bowed
  error curve. Its companions say where the bow's minimum and rises are.
-/

import CogLib.Phenomena.SerialPosition

namespace Cog

open Phenomena

/-- **Serial mechanism, unit processing time.** If after `t` trials at most
`t` items are learned, then learning `n` items takes at least `n` trials. -/
theorem trials_at_least_items (learned : Nat → Nat) (n T : Nat)
    (hunit : ∀ t, learned t ≤ t) (hcrit : n ≤ learned T) : n ≤ T :=
  Nat.le_trans hcrit (hunit T)

/-- Anchor-point attention: the trial on which the item at position `i` is
learned, attending to both ends first, then inward, one learning cycle per
trial. Positions at equal distance are taken front first. -/
def learnedOnTrial (n i : Nat) : Nat :=
  2 * distFromEnds n i + (if i ≤ n - 1 - i then 0 else 1)

/-- In serial anticipation the item at position `i` is wrong on every trial
before it is learned. -/
def errorsAt (n i : Nat) : Nat := learnedOnTrial n i

/-- An item further from its nearer anchor collects strictly more errors
(for any positions, not only those in the list). -/
theorem errorsAt_lt_of_dist_lt (n i j : Nat)
    (h : distFromEnds n i < distFromEnds n j) : errorsAt n i < errorsAt n j := by
  unfold errorsAt learnedOnTrial
  split <;> (try split) <;> omega

/-- **Anchor-point attention produces the serial position effect.** -/
theorem anchorAttention_serialPosition (n : Nat) : SerialPositionEffect n (errorsAt n) :=
  fun i j _ _ h => errorsAt_lt_of_dist_lt n i j h

/-- The first position has the fewest errors of all. -/
theorem first_position_fewest_errors (n i : Nat) : errorsAt n 0 ≤ errorsAt n i := by
  unfold errorsAt learnedOnTrial distFromEnds
  split <;> (try split) <;> omega

/-- Errors rise from the front of the list toward the middle. -/
theorem errors_rise_toward_middle (n i j : Nat) (hij : i ≤ j) (hj : j ≤ n - 1 - j) :
    errorsAt n i ≤ errorsAt n j := by
  unfold errorsAt learnedOnTrial distFromEnds
  split <;> (try split) <;> omega

/-- ...and fall again toward the back. -/
theorem errors_fall_toward_end (n i j : Nat) (hji : j ≤ i) (hi : i < n)
    (hj : n - 1 - j ≤ j) : errorsAt n i ≤ errorsAt n j := by
  unfold errorsAt learnedOnTrial distFromEnds
  split <;> (try split) <;> omega

end Cog
