/-
Phenomena of practice: the shape of a learning curve, stated theory-neutrally,
at graded levels of precision.

A learning curve `T : Nat → Rat` gives performance (a latency, say, or an error
rate) after `n` practice trials. "The power law of practice" is often reported
as one phenomenon, but it bundles claims of different strength. They are
stated here separately, over a range of trials `[lo, hi]`, so that a mechanism
can be shown to have some and not others:

* `Improves`: performance never gets worse.
* `DiminishingReturns`: each trial's gain is no larger than the last.
* `DiminishingRelativeReturns`: each trial's *proportional* gain is smaller
  than the last; the step ratio `T (n+1) / T n` rises. An exponential curve
  has constant proportional gains, so it lacks this; a power curve has it.
* `ScaleRatio k r`: `T (k n) = r · T n`. This is scale invariance, the form an
  exact power law `T n = a n^(-b)` takes with rationals: `r = k^(-b)`.
* `ApproxScaleRatio k r ε`: the same within relative error `ε`, i.e. close to
  some power law over the range.
* `ShiftRatio s`: `T (n+1) = s · T n`, an exponential curve.

None of these mentions a mechanism. Each is a target, which a mechanism may or
may not be proved to produce. Whether people's curves satisfy one is an
empirical, and statistical, question, which a deduction does not settle.

Results:
* `power_scaleRatio`, `power_diminishingRelative`: the power curve `a / n^m`
  is scale-invariant, with strictly diminishing relative returns.
* `exp_shiftRatio`; `shiftRatio_not_diminishingRelative`: an exponential
  curve has constant relative returns.
* `shiftRatio_not_scaleRatio`: no positive curve is both exponential (with
  ratio other than 1) and scale-invariant over a range containing `lo`,
  `lo + 1` and their doubles. So power and exponential are distinct
  phenomena, not two descriptions of one.
* `mix_diminishingRelative`, `mix_not_shiftRatio`: **an average of
  exponential learners is not exponential.** Mixing two exponential curves
  with different rates gives strictly diminishing relative returns, which is
  a signature of a power curve, although each learner is exactly exponential.
  This is the averaging artifact (Estes 1956; Heathcote, Brown & Mewhort
  2000), proved.
-/

import CogLib.Rep.Distribution

namespace Cog.Phenomena

/-- A learning curve: performance after `n` practice trials. -/
abbrev Curve := Nat → Rat

/-- **Improvement.** Over `[lo, hi]`, performance never gets worse. -/
def Improves (T : Curve) (lo hi : Nat) : Prop :=
  ∀ n, lo ≤ n → n < hi → T (n + 1) ≤ T n

/-- **Diminishing returns.** Over `[lo, hi]`, each trial's gain is at most
the previous trial's. -/
def DiminishingReturns (T : Curve) (lo hi : Nat) : Prop :=
  ∀ n, lo ≤ n → n + 2 ≤ hi → T (n + 1) - T (n + 2) ≤ T n - T (n + 1)

/-- **Diminishing relative returns.** Over `[lo, hi]`, each trial's
proportional gain is strictly smaller than the last: for a positive curve,
`T (n+1) / T n < T (n+2) / T (n+1)`, stated without division. -/
def DiminishingRelativeReturns (T : Curve) (lo hi : Nat) : Prop :=
  ∀ n, lo ≤ n → n + 2 ≤ hi → T (n + 1) * T (n + 1) < T n * T (n + 2)

/-- **Scale invariance**, an exact power law in rational form: over
`[lo, hi]`, multiplying practice by `k` multiplies performance by `r`. For
`T n = a n^(-b)`, `r = k^(-b)`. -/
def ScaleRatio (T : Curve) (k : Nat) (r : Rat) (lo hi : Nat) : Prop :=
  ∀ n, lo ≤ n → k * n ≤ hi → T (k * n) = r * T n

/-- **Approximately a power law**: scale invariance within relative error
`ε` over `[lo, hi]`. -/
def ApproxScaleRatio (T : Curve) (k : Nat) (r ε : Rat) (lo hi : Nat) : Prop :=
  ∀ n, lo ≤ n → k * n ≤ hi →
    (1 - ε) * (r * T n) ≤ T (k * n) ∧ T (k * n) ≤ (1 + ε) * (r * T n)

/-- **An exponential curve**: over `[lo, hi]`, each trial multiplies
performance by `s`. -/
def ShiftRatio (T : Curve) (s : Rat) (lo hi : Nat) : Prop :=
  ∀ n, lo ≤ n → n < hi → T (n + 1) = s * T n

/-- The power curve `a / n^m`. -/
def power (a : Rat) (m : Nat) : Curve := fun n => a / (n : Rat) ^ m

/-- The exponential curve `a · s^n`. -/
def expCurve (a s : Rat) : Curve := fun n => a * s ^ n

/-- The average of two exponential learners, `(a s^n + b t^n) / 2`. -/
def mix (a s b t : Rat) : Curve := fun n => (a * s ^ n + b * t ^ n) / 2

/-! ### Rational helpers -/

theorem div_lt_div_cross {a b c d : Rat} (hb : 0 < b) (hd : 0 < d) (h : a * d < c * b) :
    a / b < c / d := by
  have hb' : b ≠ 0 := by grind
  have hd' : d ≠ 0 := by grind
  have e1 : a / b = (a * d) * (b * d)⁻¹ := by grind
  have e2 : c / d = (c * b) * (b * d)⁻¹ := by grind
  rw [e1, e2]
  exact Rat.mul_lt_mul_of_pos_right h (Rat.inv_pos.mpr (Rat.mul_pos hb hd))

theorem natCast_pow_pos {n : Nat} (m : Nat) (h : 1 ≤ n) : (0 : Rat) < (n : Rat) ^ m :=
  Rat.pow_pos (by rw [show (0 : Rat) = ((0 : Nat) : Rat) from rfl, Rat.natCast_lt_natCast]; omega)

theorem mul_pow' (x y : Rat) (m : Nat) : (x * y) ^ m = x ^ m * y ^ m := by
  induction m with
  | zero => simp
  | succ m ih => simp only [Rat.pow_succ, ih]; grind

theorem pow_ne_zero' {s : Rat} (h : s ≠ 0) (m : Nat) : s ^ m ≠ 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Rat.pow_succ]; intro h0
    rcases Rat.mul_eq_zero.mp h0 with h1 | h1 <;> contradiction

/-! ### Power curves -/

/-- **The power curve is scale-invariant**, for every scale `k ≥ 1`, with
ratio `1 / k^m`. -/
theorem power_scaleRatio (a : Rat) (m k : Nat) (hk : 1 ≤ k) (hi : Nat) :
    ScaleRatio (power a m) k (1 / (k : Rat) ^ m) 1 hi := by
  intro n hn _
  have hk' := natCast_pow_pos m hk
  have hn' := natCast_pow_pos m hn
  simp only [power, Rat.natCast_mul, mul_pow']
  have : (k : Rat) ^ m ≠ 0 := by grind
  have : (n : Rat) ^ m ≠ 0 := by grind
  grind

/-- **The power curve has strictly diminishing relative returns**, for
`a > 0` and `m ≥ 1`. -/
theorem power_diminishingRelative (a : Rat) (m : Nat) (ha : 0 < a) (hm : 1 ≤ m) (hi : Nat) :
    DiminishingRelativeReturns (power a m) 1 hi := by
  intro n hn _
  have key : n ^ m * (n + 2) ^ m < (n + 1) ^ m * (n + 1) ^ m := by
    rw [← Nat.mul_pow, ← Nat.mul_pow]
    exact Nat.pow_lt_pow_left (by
      have : n * (n + 2) + 1 = (n + 1) * (n + 1) := by
        simp only [Nat.mul_add, Nat.add_mul]; omega
      omega) (by omega)
  have key' : ((n ^ m : Nat) : Rat) * (((n + 2) ^ m : Nat) : Rat) <
      (((n + 1) ^ m : Nat) : Rat) * (((n + 1) ^ m : Nat) : Rat) := by
    rw [← Rat.natCast_mul, ← Rat.natCast_mul, Rat.natCast_lt_natCast]; exact key
  have h0 : (0 : Rat) < ((n ^ m : Nat) : Rat) := by rw [Rat.natCast_pow]; exact natCast_pow_pos m hn
  have h1 : (0 : Rat) < (((n + 1) ^ m : Nat) : Rat) := by
    rw [Rat.natCast_pow]; exact natCast_pow_pos m (show 1 ≤ n + 1 by omega)
  have h2 : (0 : Rat) < (((n + 2) ^ m : Nat) : Rat) := by
    rw [Rat.natCast_pow]; exact natCast_pow_pos m (show 1 ≤ n + 2 by omega)
  have p : ∀ j, power a m j = a / ((j ^ m : Nat) : Rat) := by intro j; simp [power, Rat.natCast_pow]
  rw [p, p, p]
  generalize ((n ^ m : Nat) : Rat) = A at *
  generalize (((n + 1) ^ m : Nat) : Rat) = B at *
  generalize (((n + 2) ^ m : Nat) : Rat) = C at *
  have e1 : a / B * (a / B) = (a * a) / (B * B) := by
    have : B ≠ 0 := by grind
    grind
  have e2 : a / A * (a / C) = (a * a) / (A * C) := by
    have : A ≠ 0 := by grind
    have : C ≠ 0 := by grind
    grind
  rw [e1, e2]
  apply div_lt_div_cross (Rat.mul_pos h1 h1) (Rat.mul_pos h0 h2)
  exact Rat.mul_lt_mul_of_pos_left key' (Rat.mul_pos ha ha)

/-! ### Exponential curves -/

theorem exp_shiftRatio (a s : Rat) (lo hi : Nat) : ShiftRatio (expCurve a s) s lo hi := by
  intro n _ _
  simp only [expCurve, Rat.pow_succ]
  grind

/-- **An exponential curve lacks diminishing relative returns**: its
proportional gain is the same on every trial. -/
theorem shiftRatio_not_diminishingRelative (T : Curve) (s : Rat) (lo hi : Nat)
    (h : ShiftRatio T s lo hi) (hr : lo + 2 ≤ hi) : ¬ DiminishingRelativeReturns T lo hi := by
  intro hd
  have := hd lo (Nat.le_refl _) hr
  have h1 := h lo (Nat.le_refl _) (by omega)
  have h2 := h (lo + 1) (by omega) (by omega)
  rw [h2, h1] at this
  grind

/-- An exponential curve, iterated: `T (n + j) = s^j · T n` within the range. -/
theorem shiftRatio_iter (T : Curve) (s : Rat) (lo hi : Nat) (h : ShiftRatio T s lo hi) :
    ∀ j n, lo ≤ n → n + j ≤ hi → T (n + j) = s ^ j * T n := by
  intro j
  induction j with
  | zero => intro n _ _; simp
  | succ j ih =>
    intro n hn hj
    rw [show n + (j + 1) = (n + j) + 1 by omega, h (n + j) (by omega) (by omega),
      ih n hn (by omega), Rat.pow_succ]
    grind

/-- **Power and exponential are different phenomena.** No curve that is
positive over `[lo, hi]` is both exponential, with a ratio other than 1, and
scale-invariant at doubling over a range containing `lo`, `lo + 1` and their
doubles. -/
theorem shiftRatio_not_scaleRatio (T : Curve) (s r : Rat) (lo hi : Nat) (hlo : 1 ≤ lo)
    (hr : 2 * (lo + 1) ≤ hi) (hpos : ∀ n, lo ≤ n → n ≤ hi → 0 < T n) (hs : s ≠ 1)
    (he : ShiftRatio T s lo hi) : ¬ ScaleRatio T 2 r lo hi := by
  intro hp
  have it := shiftRatio_iter T s lo hi he
  have a0 := hp lo (Nat.le_refl _) (by omega)
  have a1 := hp (lo + 1) (by omega) hr
  rw [show 2 * lo = lo + lo by omega, it lo lo (Nat.le_refl _) (by omega)] at a0
  rw [show 2 * (lo + 1) = (lo + 1) + (lo + 1) by omega,
    it (lo + 1) (lo + 1) (by omega) (by omega)] at a1
  have p0 := hpos lo (Nat.le_refl _) (by omega)
  have p1 := hpos (lo + 1) (by omega) (by omega)
  -- r = s^lo and r = s^(lo+1)
  have r0 : r = s ^ lo := by
    have : (s ^ lo - r) * T lo = 0 := by grind
    rcases Rat.mul_eq_zero.mp this with h | h <;> grind
  have r1 : r = s ^ (lo + 1) := by
    have : (s ^ (lo + 1) - r) * T (lo + 1) = 0 := by grind
    rcases Rat.mul_eq_zero.mp this with h | h <;> grind
  have hs0 : s ≠ 0 := by
    intro h0
    have := he lo (Nat.le_refl _) (by omega)
    rw [h0] at this
    grind
  have : s ^ lo * (s - 1) = 0 := by rw [Rat.pow_succ] at r1; grind
  rcases Rat.mul_eq_zero.mp this with h | h
  · exact pow_ne_zero' hs0 lo h
  · grind

/-! ### Averaging exponential learners -/

/-- **An average of exponential learners has diminishing relative returns.**
For positive weights and distinct positive rates, the average of two
exponential curves has strictly diminishing relative returns at every trial,
a signature of a power curve, although each learner is exponential. -/
theorem mix_diminishingRelative (a s b t : Rat) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (ht : 0 < t) (hst : s ≠ t) (lo hi : Nat) :
    DiminishingRelativeReturns (mix a s b t) lo hi := by
  intro n _ _
  simp only [mix, Rat.pow_succ]
  have x0 : 0 < a * s ^ n := Rat.mul_pos ha (Rat.pow_pos hs)
  have y0 : 0 < b * t ^ n := Rat.mul_pos hb (Rat.pow_pos ht)
  have d0 : 0 < (s - t) * (s - t) := by
    by_cases h : s < t
    · rw [show (s - t) * (s - t) = (t - s) * (t - s) by grind]
      exact Rat.mul_pos (by grind) (by grind)
    · exact Rat.mul_pos (by grind) (by grind)
  have key := Rat.mul_pos (Rat.mul_pos x0 y0) d0
  have ex1 : a * (s ^ n * s) = a * s ^ n * s := by grind
  have ex2 : a * (s ^ n * s * s) = a * s ^ n * s * s := by grind
  have ey1 : b * (t ^ n * t) = b * t ^ n * t := by grind
  have ey2 : b * (t ^ n * t * t) = b * t ^ n * t * t := by grind
  rw [ex1, ex2, ey1, ey2]
  generalize a * s ^ n = x at *
  generalize b * t ^ n = y at *
  have e : (x + y) / 2 * ((x * s * s + y * t * t) / 2) -
      (x * s + y * t) / 2 * ((x * s + y * t) / 2) = x * y * ((s - t) * (s - t)) / 4 := by grind
  grind

/-- **So an average of exponential learners is not exponential.** -/
theorem mix_not_shiftRatio (a s b t : Rat) (ha : 0 < a) (hb : 0 < b) (hs : 0 < s)
    (ht : 0 < t) (hst : s ≠ t) (r : Rat) (lo hi : Nat) (hr : lo + 2 ≤ hi) :
    ¬ ShiftRatio (mix a s b t) r lo hi := fun h =>
  shiftRatio_not_diminishingRelative _ r lo hi h hr
    (mix_diminishingRelative a s b t ha hb hs ht hst lo hi)

end Cog.Phenomena
