/-
The learning-curve predicates over the reals, and their bridge to CogLib.

CogLib states a power law with exact rationals, as scale invariance
(`Phenomena.ScaleRatio`: `T (k n) = r · T n`), since `n^(-b)` is generally
irrational. This file, which uses Mathlib and so lives outside CogLib, shows
that the rational form says what it should about the real-valued one:

* `scaleRatio_iff_cast`: a rational curve is scale-invariant exactly when its
  real-valued copy is.
* `rpow_scaleRatio`: the power law `a · n^(-b)`, for any real `a` and `b`, is
  scale-invariant at every scale `k`, with ratio `k^(-b)`.
* `powerLaw_of_scaleRatio`: conversely, scale invariance at doubling with ratio
  `r > 0` is a power law on the doubling grid, `T (2^j) = T 1 · (2^j)^(-b)`
  with exponent `b = -log₂ r`.
* `power_cast`: CogLib's rational power curve `a / n^m` is the real power law
  with exponent `m`.
* `spaced_cast`: CogLib's ACT-R spaced-practice curve (decay 1) is the real
  curve `F / Σ_{k ≤ n} k^(-1)`, so the decay-`d` curve `spacedR` extends it.
-/

import Mathlib
import CogLib.Phenomena.LearningCurve
import CogLib.Process.Practice

namespace Cog.ACTR

open Cog.Phenomena

/-- Scale invariance of a real-valued curve over `[lo, hi]`. -/
def RScaleRatio (T : ℕ → ℝ) (k : ℕ) (r : ℝ) (lo hi : ℕ) : Prop :=
  ∀ n, lo ≤ n → k * n ≤ hi → T (k * n) = r * T n

/-- **The rational and real forms of scale invariance agree.** -/
theorem scaleRatio_iff_cast (T : Curve) (k : ℕ) (r : ℚ) (lo hi : ℕ) :
    ScaleRatio T k r lo hi ↔ RScaleRatio (fun n => (T n : ℝ)) k (r : ℝ) lo hi := by
  unfold ScaleRatio RScaleRatio
  constructor
  · intro h n h1 h2
    simp only [h n h1 h2]
    push_cast
    ring
  · intro h n h1 h2
    have := h n h1 h2
    simp only at this
    exact_mod_cast this

/-- **A power law is scale-invariant**: `a · n^(-b)` has ratio `k^(-b)` at
every scale `k`. -/
theorem rpow_scaleRatio (a b : ℝ) (k hi : ℕ) :
    RScaleRatio (fun n => a * (n : ℝ) ^ (-b)) k ((k : ℝ) ^ (-b)) 1 hi := by
  intro n _ _
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg n)]
  ring

/-- `(2^j)^(log₂ r) = r^j` for `r > 0`. -/
theorem two_pow_rpow_logb (r : ℝ) (hr : 0 < r) (j : ℕ) :
    (((2 ^ j : ℕ) : ℝ)) ^ (Real.logb 2 r) = r ^ j := by
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) hr, Real.rpow_natCast]

/-- **Scale invariance at doubling is a power law on the doubling grid**, with
exponent `b = -log₂ r`. -/
theorem powerLaw_of_scaleRatio (T : ℕ → ℝ) (r : ℝ) (hr : 0 < r) (hi : ℕ)
    (h : RScaleRatio T 2 r 1 hi) :
    ∀ j, 2 ^ j ≤ hi → T (2 ^ j) = T 1 * (((2 ^ j : ℕ) : ℝ)) ^ (-(-Real.logb 2 r)) := by
  intro j hj
  rw [neg_neg, two_pow_rpow_logb r hr]
  induction j with
  | zero => simp
  | succ j ih =>
    have h2 : 2 ^ j ≤ hi := le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ j)) hj
    have := h (2 ^ j) Nat.one_le_two_pow (by rw [pow_succ] at hj; linarith)
    rw [pow_succ, mul_comm (2 ^ j) 2, this, ih h2, pow_succ]
    ring

/-- **CogLib's rational power curve is the real power law** with exponent `m`. -/
theorem power_cast (a : ℚ) (m n : ℕ) :
    ((power a m n : ℚ) : ℝ) = (a : ℝ) * (n : ℝ) ^ (-(m : ℝ)) := by
  simp only [power]
  push_cast
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast]
  ring

/-! ### ACT-R's base level with any decay -/

/-- `e^B` after spaced practice (uses at `0 … n-1`, tested at `n`) with decay
`d`: `Σ_{k=1}^{n} k^(-d)`. -/
noncomputable def baseSpaced (d : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) ^ (-d)

/-- Latency after spaced practice with decay `d`. -/
noncomputable def spacedR (F d : ℝ) (n : ℕ) : ℝ := F / baseSpaced d n

theorem harmonic_cast (n : ℕ) :
    ((Act.harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ)⁻¹ := by
  induction n with
  | zero => simp [Act.harmonic]
  | succ n ih =>
    rw [Act.harmonic, Finset.sum_range_succ, ← ih]
    push_cast
    ring

/-- **At decay 1, the real curve is CogLib's**: `spacedR F 1` is the cast of
`Act.spaced F`. -/
theorem spaced_cast (F : ℚ) (n : ℕ) :
    ((Act.spaced F n : ℚ) : ℝ) = spacedR (F : ℝ) 1 n := by
  rw [Act.spaced_eq, spacedR, baseSpaced]
  push_cast
  rw [harmonic_cast]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.rpow_neg_one]
  push_cast
  ring

end Cog.ACTR
