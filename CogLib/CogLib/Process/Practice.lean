/-
Practice curves from ACT-R's base-level learning.

A chunk's base-level activation sums a decaying trace for each use, and its
retrieval time falls as activation rises (`Act.latency`, `F · e^{-A}`). With
decay 1, the only decay with rational values, `e^B = Σ 1/(age of each use)`.
Two practice schedules give curves of different shape from the *same*
mechanism:

* **Massed practice, tested after a delay.** All `n` uses at time 0, tested
  at lag `L`: latency is `F L / n`, an exact power law with exponent 1
  (`massed_eq_power`, `massed_scaleRatio`).
* **Spaced practice, tested after each trial.** One use per trial at times
  `0 … n-1`, tested at time `n`: `e^B` is the harmonic number `H n`, and
  latency is `F / H n` (`spaced_eq`). It improves, with diminishing returns
  and diminishing relative returns (`spaced_improves`, `spaced_diminishing`,
  `spaced_diminishingRelative`): every qualitative signature of a power law.
  But it is **not** approximately a power law over long ranges, for any
  exponent (`spaced_not_powerLaw`): the doubling ratio `T (2n) / T n` tends
  to 1, so a fitted exponent falls toward 0. The curve is logarithmic. Yet
  over trials 1 to 8 it is within 7.5% of a power law with exponent about
  0.47 (`spaced_looks_like_powerLaw`, a witness at one setting).

So with decay 1, whether ACT-R's base level "produces the power law of
practice" depends on the schedule, a condition, not on the mechanism alone;
and a curve can have every qualitative signature of a power law without
being one. ACT-R's usual decay, 0.5, needs real powers (a Mathlib bridge),
and gives approximately a power law with exponent `1 - d` under spaced
practice; that is not proved here.

The postulates are the base level (`Act.baseWeight`) and the latency rule
(`Act.latency`). The schedule and the test time are conditions. The curve
shapes are the phenomena of `Phenomena/LearningCurve`.
-/

import CogLib.Memory.Activation
import CogLib.Phenomena.LearningCurve

namespace Cog.Act

open Phenomena

/-- The harmonic numbers, `H n = 1 + 1/2 + … + 1/n`. -/
def harmonic : Nat → Rat
  | 0 => 0
  | n + 1 => harmonic n + 1 / ((n + 1 : Nat) : Rat)

/-- The latency after `n` spaced trials (one use per trial, at times
`0 … n-1`), tested at time `n`. -/
def spaced (F : Rat) : Curve := fun n => latency F n (List.range n)

/-- The latency after `n` massed uses at time 0, tested at lag `L`. -/
def massed (F : Rat) (L : Nat) : Curve := fun n => latency F L (List.replicate n 0)

theorem cast_nonneg (n : Nat) : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg

theorem cast_le {a b : Nat} (h : a ≤ b) : (a : Rat) ≤ (b : Rat) := Rat.natCast_le_natCast.mpr h

/-! ### The base level under the two schedules -/

/-- Advancing the clock and every use together leaves the base level alone. -/
theorem baseWeight_shift (now : Nat) (uses : List Nat) :
    baseWeight (now + 1) (uses.map Nat.succ) = baseWeight now uses := by
  simp only [baseWeight, List.map_map]
  congr 2
  funext t
  simp [Nat.succ_sub_succ]

theorem baseWeight_spaced (n : Nat) : baseWeight n (List.range n) = harmonic n := by
  induction n with
  | zero => simp [baseWeight, harmonic]
  | succ n ih =>
    rw [List.range_succ_eq_map]
    have e : baseWeight (n + 1) (0 :: (List.range n).map Nat.succ) =
        1 / ((n + 1 - 0 : Nat) : Rat) + baseWeight (n + 1) ((List.range n).map Nat.succ) := by
      simp [baseWeight]
    rw [e, baseWeight_shift, ih, harmonic, Nat.sub_zero]
    grind

theorem baseWeight_massed (L n : Nat) :
    baseWeight L (List.replicate n 0) = (n : Rat) * (1 / (L : Rat)) := by
  induction n with
  | zero => simp [baseWeight]
  | succ n ih =>
    simp only [baseWeight, List.replicate_succ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.sub_zero, Rat.natCast_add]
    grind

theorem spaced_eq (F : Rat) (n : Nat) : spaced F n = F / harmonic n := by
  simp [spaced, latency, baseWeight_spaced]

/-! ### Harmonic numbers -/

theorem harmonic_succ (n : Nat) : harmonic (n + 1) = harmonic n + 1 / ((n : Rat) + 1) := by
  simp [harmonic, Rat.natCast_add]

theorem inv_succ_pos (n : Nat) : (0 : Rat) < 1 / ((n : Rat) + 1) := by
  have : (0 : Rat) < (n : Rat) + 1 := by
    have := cast_nonneg (n); grind
  rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr this

theorem harmonic_lt_succ (n : Nat) : harmonic n < harmonic (n + 1) := by
  rw [harmonic_succ]; have := inv_succ_pos n; grind

theorem harmonic_pos (n : Nat) (h : 1 ≤ n) : 0 < harmonic n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [harmonic] <;> grind
    · have := ih h0; have := harmonic_lt_succ n; grind

/-- `1/(m+1) ≤ 1/(j+1)` for `j ≤ m`. -/
theorem inv_succ_anti {j m : Nat} (h : j ≤ m) : 1 / ((m : Rat) + 1) ≤ 1 / ((j : Rat) + 1) := by
  have hj : (0 : Rat) < (j : Rat) + 1 := by have := cast_nonneg (j); grind
  have hm : (0 : Rat) < (m : Rat) + 1 := by have := cast_nonneg (m); grind
  apply Dist.div_le_div_cross hm hj
  have : (j : Rat) ≤ (m : Rat) := Rat.natCast_le_natCast.mpr h
  grind

/-- Each of the `i` terms after `H m` is at most `1/(m+1)`. -/
theorem harmonic_add_le (m i : Nat) :
    harmonic (m + i) ≤ harmonic m + (i : Rat) * (1 / ((m : Rat) + 1)) := by
  induction i with
  | zero => simp <;> grind
  | succ i ih =>
    rw [show m + (i + 1) = (m + i) + 1 by omega, harmonic_succ]
    have := inv_succ_anti (show m ≤ m + i by omega)
    simp only [Rat.natCast_add] at this ⊢
    grind

/-- Each of the first `m` terms after `H m` is at least `1/(2m)`. -/
theorem harmonic_add_ge (m i : Nat) (hm : 1 ≤ m) (hi : i ≤ m) :
    harmonic m + (i : Rat) * (1 / (2 * (m : Rat))) ≤ harmonic (m + i) := by
  induction i with
  | zero => simp <;> grind
  | succ i ih =>
    rw [show m + (i + 1) = (m + i) + 1 by omega, harmonic_succ]
    have ih := ih (by omega)
    have h2m : (0 : Rat) < 2 * (m : Rat) := by
      have : (1 : Rat) ≤ (m : Rat) := by
        have := cast_le hm; simpa using this
      grind
    have hs : (0 : Rat) < ((m + i : Nat) : Rat) + 1 := by
      have := cast_nonneg (m + i); grind
    have step : 1 / (2 * (m : Rat)) ≤ 1 / (((m + i : Nat) : Rat) + 1) := by
      apply Dist.div_le_div_cross h2m hs
      have : ((m + i : Nat) : Rat) + 1 ≤ 2 * (m : Rat) := by
        have := cast_le (show m + i + 1 ≤ 2 * m by omega)
        simpa [Rat.natCast_add, Rat.natCast_mul] using this
      grind
    simp only [Rat.natCast_add] at step ih ⊢
    grind

/-- Doubling adds at most 1: `H (2m) ≤ H m + 1`. -/
theorem harmonic_double_le (m : Nat) : harmonic (2 * m) ≤ harmonic m + 1 := by
  have h := harmonic_add_le m m
  rw [show m + m = 2 * m by omega] at h
  have : (m : Rat) * (1 / ((m : Rat) + 1)) ≤ 1 := by
    have hm : (0 : Rat) < (m : Rat) + 1 := by have := cast_nonneg (m); grind
    have e : (m : Rat) * (1 / ((m : Rat) + 1)) = (m : Rat) / ((m : Rat) + 1) := by grind
    rw [e]
    have := Dist.div_le_div_cross (a := (m : Rat)) (c := 1) hm (show (0 : Rat) < 1 by decide)
      (by grind)
    grind
  grind

/-- Doubling adds at least 1/2: `H m + 1/2 ≤ H (2m)`. -/
theorem harmonic_double_ge (m : Nat) (hm : 1 ≤ m) : harmonic m + 1 / 2 ≤ harmonic (2 * m) := by
  have h := harmonic_add_ge m m hm (Nat.le_refl _)
  rw [show m + m = 2 * m by omega] at h
  have : (m : Rat) * (1 / (2 * (m : Rat))) = 1 / 2 := by
    have : (m : Rat) ≠ 0 := by
      have := cast_le hm; simp at this; grind
    grind
  grind

/-- **The harmonic numbers are unbounded**: `H (2^j) ≥ j/2`. -/
theorem harmonic_pow_two (j : Nat) : (j : Rat) / 2 ≤ harmonic (2 ^ j) := by
  induction j with
  | zero => simp [harmonic] <;> grind
  | succ j ih =>
    rw [Nat.pow_succ, Nat.mul_comm]
    have := harmonic_double_ge (2 ^ j) (Nat.one_le_two_pow)
    simp only [Rat.natCast_add] at ih ⊢
    grind

/-! ### Spaced practice: every qualitative signature of a power law -/

/-- **Spaced practice improves**, at every trial. -/
theorem spaced_improves (F : Rat) (hF : 0 < F) (hi : Nat) : Improves (spaced F) 1 hi := by
  intro n hn _
  rw [spaced_eq, spaced_eq]
  have h0 := harmonic_pos n hn
  have h1 := harmonic_lt_succ n
  apply Dist.div_le_div_cross (by grind) h0
  exact Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt h1) (Rat.le_of_lt hF)

/-- The gain of trial `n+1`: `F / ((n+1) H n H (n+1))`. -/
theorem spaced_gain (F : Rat) (n : Nat) (hn : 1 ≤ n) :
    spaced F n - spaced F (n + 1) =
      F / (((n : Rat) + 1) * (harmonic n * harmonic (n + 1))) := by
  rw [spaced_eq, spaced_eq, harmonic_succ]
  have h0 := harmonic_pos n hn
  have hs : (0 : Rat) < (n : Rat) + 1 := by have := cast_nonneg (n); grind
  have : harmonic n + 1 / ((n : Rat) + 1) ≠ 0 := by have := inv_succ_pos n; grind
  have : harmonic n ≠ 0 := by grind
  have : (n : Rat) + 1 ≠ 0 := by grind
  grind

theorem mul_le_mul_pos {a b c d : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) :
    a * c ≤ b * d :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hcd ha)
    (Rat.mul_le_mul_of_nonneg_right hab (Rat.le_trans hc hcd))

/-- **Spaced practice has diminishing returns.** -/
theorem spaced_diminishing (F : Rat) (hF : 0 < F) (hi : Nat) :
    DiminishingReturns (spaced F) 1 hi := by
  intro n hn _
  rw [spaced_gain F n hn, spaced_gain F (n + 1) (by omega)]
  have h0 := harmonic_pos n hn
  have h1 := harmonic_lt_succ n
  have h2 := harmonic_lt_succ (n + 1)
  have hs : (0 : Rat) < (n : Rat) + 1 := by have := cast_nonneg (n); grind
  have c1 : ((n + 1 : Nat) : Rat) + 1 = (n : Rat) + 1 + 1 := by simp [Rat.natCast_add]
  rw [c1]
  have p0 : 0 < ((n : Rat) + 1) * (harmonic n * harmonic (n + 1)) :=
    Rat.mul_pos hs (Rat.mul_pos h0 (by grind))
  apply Dist.div_le_div_cross (Rat.mul_pos (by grind) (Rat.mul_pos (by grind) (by grind))) p0
  apply Rat.mul_le_mul_of_nonneg_left _ (Rat.le_of_lt hF)
  apply mul_le_mul_pos (Rat.le_of_lt hs) (by grind)
    (Rat.le_of_lt (Rat.mul_pos h0 (by grind)))
  exact mul_le_mul_pos (Rat.le_of_lt h0) (Rat.le_of_lt h1) (by grind) (Rat.le_of_lt h2)

/-- **Spaced practice has diminishing relative returns**: `H` is strictly
log-concave, so the step ratio `H n / H (n+1)` rises. -/
theorem spaced_diminishingRelative (F : Rat) (hF : 0 < F) (hi : Nat) :
    DiminishingRelativeReturns (spaced F) 1 hi := by
  intro n hn _
  rw [spaced_eq, spaced_eq, spaced_eq]
  have h0 := harmonic_pos n hn
  have hA := harmonic_succ n
  have hB := harmonic_succ (n + 1)
  generalize harmonic (n + 1) = B at *
  generalize harmonic (n + 2) = C at *
  generalize harmonic n = A at *
  have u0 := inv_succ_pos n
  have v0 := inv_succ_pos (n + 1)
  have uv := inv_succ_anti (show n ≤ n + 1 by omega)
  have huv : 1 / (((n + 1 : Nat) : Rat) + 1) < 1 / ((n : Rat) + 1) := by
    have hs : (0 : Rat) < (n : Rat) + 1 := by have := cast_nonneg (n); grind
    apply div_lt_div_cross (by have := cast_nonneg (n + 1); grind) hs
    simp [Rat.natCast_add]; grind
  generalize 1 / ((n : Rat) + 1) = u at *
  generalize 1 / (((n + 1 : Nat) : Rat) + 1) = v at *
  -- A = B - u, C = B + v, and A C = B² - B (u - v) - u v < B².
  have hB0 : 0 < B := by grind
  have p := Rat.mul_pos hB0 (show 0 < u - v by grind)
  have q := Rat.mul_pos u0 v0
  have key : A * C < B * B := by
    have : A * C = B * B - B * (u - v) - u * v := by grind
    grind
  have e1 : F / B * (F / B) = (F * F) / (B * B) := by
    have : B ≠ 0 := by grind
    grind
  have e2 : F / A * (F / C) = (F * F) / (A * C) := by
    have : A ≠ 0 := by grind
    have : C ≠ 0 := by grind
    grind
  rw [e1, e2]
  apply div_lt_div_cross (Rat.mul_pos hB0 hB0) (Rat.mul_pos h0 (by grind))
  exact Rat.mul_lt_mul_of_pos_left key (Rat.mul_pos hF hF)

/-! ### …but not a power law -/

/-- Some trial past `lo` has `H n > K`, for any bound `K`. -/
theorem harmonic_unbounded (K : Rat) (lo : Nat) : ∃ n, lo ≤ n ∧ 1 ≤ n ∧ K < harmonic n := by
  let j := max lo ((2 * K).ceil.toNat + 1)
  refine ⟨2 ^ j, ?_, Nat.one_le_two_pow, ?_⟩
  · exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_lt Nat.lt_two_pow_self)
  · have h := harmonic_pow_two j
    have hj : (2 * K).ceil.toNat + 1 ≤ j := Nat.le_max_right _ _
    have c1 : 2 * K ≤ (((2 * K).ceil.toNat : Nat) : Rat) := by
      have := Rat.le_ceil (x := 2 * K)
      have h2 : (2 * K).ceil ≤ (((2 * K).ceil.toNat : Nat) : Int) := Int.self_le_toNat _
      have h3 : (((2 * K).ceil : Int) : Rat) ≤ ((((2 * K).ceil.toNat : Nat) : Int) : Rat) :=
        Rat.intCast_le_intCast.mpr h2
      rw [Rat.intCast_natCast] at h3
      grind
    have c2 : (((2 * K).ceil.toNat : Nat) : Rat) + 1 ≤ (j : Rat) := by
      have := cast_le hj
      simpa [Rat.natCast_add] using this
    grind

/-- **Spaced practice is not a power law.** For any ratio `c < 1`, beyond
any trial there is an `n` with `T (2n) > c · T n`: doubling practice
eventually shrinks latency by less than any fixed factor. -/
theorem spaced_doubling (F : Rat) (hF : 0 < F) (c : Rat) (hc : c < 1) (lo : Nat) :
    ∃ n, lo ≤ n ∧ 1 ≤ n ∧ c * spaced F n < spaced F (2 * n) := by
  by_cases hc0 : c ≤ 0
  · refine ⟨max lo 1, Nat.le_max_left _ _, Nat.le_max_right _ _, ?_⟩
    have h1 := harmonic_pos (2 * max lo 1) (by omega)
    have : 0 < spaced F (2 * max lo 1) := by
      rw [spaced_eq, Rat.div_def]; exact Rat.mul_pos hF (Rat.inv_pos.mpr h1)
    have h0 := harmonic_pos (max lo 1) (Nat.le_max_right _ _)
    have : 0 ≤ spaced F (max lo 1) := by
      rw [spaced_eq]; exact Dist.div_nonneg' (Rat.le_of_lt hF) (Rat.le_of_lt h0)
    have : c * spaced F (max lo 1) ≤ 0 := by
      have := Rat.mul_le_mul_of_nonneg_right hc0 this; simpa using this
    grind
  · have hc0 : 0 < c := by grind
    obtain ⟨n, hlo, hn, hK⟩ := harmonic_unbounded (c / (1 - c)) lo
    refine ⟨n, hlo, hn, ?_⟩
    rw [spaced_eq, spaced_eq]
    have h0 := harmonic_pos n hn
    have h2 := harmonic_pos (2 * n) (by omega)
    have hd := harmonic_double_le n
    -- c H(2n) ≤ c (H n + 1) < H n, since H n (1 - c) > c
    have k1 : c < harmonic n * (1 - c) := by
      have := Rat.mul_lt_mul_of_pos_right hK (show 0 < 1 - c by grind)
      have e : c / (1 - c) * (1 - c) = c := by
        have : 1 - c ≠ 0 := by grind
        grind
      grind
    have k2 : c * harmonic (2 * n) < harmonic n := by
      have := Rat.mul_le_mul_of_nonneg_left hd (Rat.le_of_lt hc0)
      grind
    have e : c * (F / harmonic n) = (c * F) / harmonic n := by grind
    rw [e]
    apply div_lt_div_cross h0 h2
    have := Rat.mul_lt_mul_of_pos_left k2 hF
    grind

/-- **So no power law fits spaced practice over long ranges**: for any
ratio `r` and tolerance `ε` with `(1 + ε) r < 1`, i.e. any exponent above 0
fitted to within `ε`, the curve is not approximately scale-invariant over
`[lo, hi]` once `hi` is large enough. -/
theorem spaced_not_powerLaw (F : Rat) (hF : 0 < F) (r ε : Rat) (h : (1 + ε) * r < 1)
    (lo : Nat) : ∃ hi, ¬ ApproxScaleRatio (spaced F) 2 r ε lo hi := by
  obtain ⟨n, hlo, _, hlt⟩ := spaced_doubling F hF ((1 + ε) * r) h lo
  refine ⟨2 * n, fun hA => ?_⟩
  have := (hA n hlo (Nat.le_refl _)).2
  grind

/-- **Over a short range it looks like a power law.** A witness at one
setting (`F = 1`): over trials 1 to 8, the spaced curve is within 7.5% of
scale invariance with ratio `18/25` at doubling, a power law with exponent
about 0.47, although `spaced_not_powerLaw` shows that no power law fits it
over long ranges. -/
theorem spaced_looks_like_powerLaw : ApproxScaleRatio (spaced 1) 2 (18 / 25) (3 / 40) 1 8 := by
  intro n h1 h2
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> decide +kernel

/-! ### Massed practice: an exact power law -/

theorem massed_eq_power (F : Rat) (L : Nat) (hL : 1 ≤ L) (n : Nat) (hn : 1 ≤ n) :
    massed F L n = power (F * L) 1 n := by
  simp only [massed, latency, baseWeight_massed, power, Rat.pow_one]
  have : (L : Rat) ≠ 0 := by
    have := cast_le hL; simp at this; grind
  have : (n : Rat) ≠ 0 := by
    have := cast_le hn; simp at this; grind
  grind

/-- **Massed practice, tested after a delay, gives an exact power law**, with
exponent 1: multiplying practice by `k` divides latency by `k`. -/
theorem massed_scaleRatio (F : Rat) (L : Nat) (hL : 1 ≤ L) (k : Nat) (hk : 1 ≤ k) (hi : Nat) :
    ScaleRatio (massed F L) k (1 / (k : Rat) ^ 1) 1 hi := by
  intro n hn hkn
  rw [massed_eq_power F L hL n hn,
    massed_eq_power F L hL (k * n) (Nat.le_trans hn (Nat.le_mul_of_pos_left n hk))]
  exact power_scaleRatio (F * L) 1 k hk hi n hn hkn

end Cog.Act
