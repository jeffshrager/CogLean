/-
ACT-R's base level with decay `0 < d < 1`: spaced practice is asymptotically a
power law with exponent `1 - d`.

With decay `d`, after spaced practice (one use per trial, tested after the
last), `e^B = Σ_{k=1}^{n} k^(-d)` (`baseSpaced`), and latency is `F / e^B`
(`spacedR`). The sum lies between integrals of `x^(-d)`, so it grows like
`n^(1-d) / (1-d)`, and the doubling ratio of latency tends to `2^(-(1-d))`:

* `baseSpaced_div_tendsto`: `Σ_{k ≤ n} k^(-d) / (n+1)^(1-d) → 1 / (1-d)`.
* `spacedR_doubling_tendsto`: `T (2n) / T n → 2^(-(1-d))`.
* `spacedR_approx_powerLaw`: **so for every tolerance `ε > 0` there is a trial
  beyond which the curve is within `ε` of scale invariance at doubling with
  ratio `2^(-(1-d))`**: approximately a power law with exponent `1 - d`.

This is Anderson's account of the power law of practice in ACT-R, made
checkable. At decay 1 the same mechanism gives a logarithmic curve instead
(`Act.spaced_not_powerLaw` in CogLib), so the exponent, and whether there is
a power law at all, depends on the decay.
-/

import ACTR.PowerLaw

namespace Cog.ACTR

open Filter Topology MeasureTheory intervalIntegral

variable {d : ℝ}

theorem rpow_neg_antitoneOn (hd : 0 ≤ d) (b : ℝ) :
    AntitoneOn (fun x : ℝ => x ^ (-d)) (Set.Icc 1 b) := by
  intro x hx y hy hxy
  exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)

/-- `∫_1^{1+n} x^(-d) = ((1+n)^(1-d) - 1) / (1-d)`. -/
theorem integral_rpow_neg (hd : d < 1) (n : ℕ) :
    ∫ x in (1 : ℝ)..(1 + n), x ^ (-d) = ((1 + n : ℝ) ^ (1 - d) - 1) / (1 - d) := by
  rw [integral_rpow (Or.inl (by linarith))]
  rw [show -d + 1 = 1 - d by ring, Real.one_rpow]

/-- **The sum lies between integrals.** -/
theorem baseSpaced_bounds (hd0 : 0 ≤ d) (hd : d < 1) (n : ℕ) :
    ((1 + n : ℝ) ^ (1 - d) - 1) / (1 - d) ≤ baseSpaced d n ∧
      baseSpaced d n ≤ 1 + ((1 + n : ℝ) ^ (1 - d) - 1) / (1 - d) := by
  have anti := rpow_neg_antitoneOn hd0 (1 + n)
  have lower := AntitoneOn.integral_le_sum (x₀ := 1) (a := n) anti
  have upper := AntitoneOn.sum_le_integral (x₀ := 1) (a := n) anti
  rw [integral_rpow_neg hd] at lower upper
  have e1 : baseSpaced d n = ∑ i ∈ Finset.range n, (1 + (i : ℝ)) ^ (-d) := by
    unfold baseSpaced
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  refine ⟨by rw [e1]; exact lower, ?_⟩
  -- baseSpaced d n ≤ baseSpaced d (n+1) = 1 + Σ_{i<n} (1 + (i+1))^(-d)
  have e2 : baseSpaced d (n + 1) = 1 + ∑ i ∈ Finset.range n, (1 + ((i : ℝ) + 1)) ^ (-d) := by
    unfold baseSpaced
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, zero_add, Real.one_rpow]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring_nf
  have mono : baseSpaced d n ≤ baseSpaced d (n + 1) := by
    unfold baseSpaced
    rw [Finset.sum_range_succ]
    have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (-d) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  push_cast at upper
  linarith

theorem tendsto_rpow_succ (hd : d < 1) :
    Tendsto (fun n : ℕ => (1 + n : ℝ) ^ (1 - d)) atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (1 + n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_atTop (by linarith)).comp h1

/-- **The sum grows like `(n+1)^(1-d) / (1-d)`.** -/
theorem baseSpaced_div_tendsto (hd0 : 0 ≤ d) (hd : d < 1) :
    Tendsto (fun n : ℕ => baseSpaced d n / (1 + n : ℝ) ^ (1 - d)) atTop (𝓝 (1 / (1 - d))) := by
  have hp : 0 < 1 - d := by linarith
  have hinv : Tendsto (fun n : ℕ => ((1 + n : ℝ) ^ (1 - d))⁻¹) atTop (𝓝 0) :=
    (tendsto_rpow_succ hd).inv_tendsto_atTop
  -- lower and upper bounds, divided by (1+n)^(1-d)
  have lo : Tendsto (fun n : ℕ => 1 / (1 - d) - ((1 + n : ℝ) ^ (1 - d))⁻¹ / (1 - d)) atTop
      (𝓝 (1 / (1 - d))) := by
    have := (hinv.div_const (1 - d)).const_sub (1 / (1 - d))
    simpa using this
  have hi : Tendsto (fun n : ℕ => 1 / (1 - d) + (1 - 1 / (1 - d)) * ((1 + n : ℝ) ^ (1 - d))⁻¹)
      atTop (𝓝 (1 / (1 - d))) := by
    have := (hinv.const_mul (1 - 1 / (1 - d))).const_add (1 / (1 - d))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le lo hi (fun n => ?_) (fun n => ?_)
  · have hpos : 0 < (1 + n : ℝ) ^ (1 - d) := Real.rpow_pos_of_pos (by positivity) _
    have hb := (baseSpaced_bounds hd0 hd n).1
    rw [le_div_iff₀ hpos]
    have : (1 / (1 - d) - ((1 + n : ℝ) ^ (1 - d))⁻¹ / (1 - d)) * (1 + n : ℝ) ^ (1 - d) =
        ((1 + n : ℝ) ^ (1 - d) - 1) / (1 - d) := by
      field_simp
    linarith
  · have hpos : 0 < (1 + n : ℝ) ^ (1 - d) := Real.rpow_pos_of_pos (by positivity) _
    have hb := (baseSpaced_bounds hd0 hd n).2
    rw [div_le_iff₀ hpos]
    have : (1 / (1 - d) + (1 - 1 / (1 - d)) * ((1 + n : ℝ) ^ (1 - d))⁻¹) * (1 + n : ℝ) ^ (1 - d) =
        1 + ((1 + n : ℝ) ^ (1 - d) - 1) / (1 - d) := by
      field_simp
      ring
    linarith

/-- **The doubling ratio of latency tends to `2^(-(1-d))`.** -/
theorem spacedR_doubling_tendsto (F : ℝ) (hF : F ≠ 0) (hd0 : 0 ≤ d) (hd : d < 1) :
    Tendsto (fun n : ℕ => spacedR F d (2 * n) / spacedR F d n) atTop
      (𝓝 ((2 : ℝ) ^ (-(1 - d)))) := by
  have hp : 0 < 1 - d := by linarith
  have A := baseSpaced_div_tendsto hd0 hd
  have B : Tendsto (fun n : ℕ => baseSpaced d (2 * n) / (1 + ((2 * n : ℕ) : ℝ)) ^ (1 - d)) atTop
      (𝓝 (1 / (1 - d))) :=
    A.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  -- ((1+n)/(1+2n))^(1-d) → (1/2)^(1-d)
  have C : Tendsto (fun n : ℕ => ((1 + (n : ℝ)) / (1 + ((2 * n : ℕ) : ℝ))) ^ (1 - d)) atTop
      (𝓝 ((1 / 2 : ℝ) ^ (1 - d))) := by
    have r : Tendsto (fun n : ℕ => (1 + (n : ℝ)) / (1 + ((2 * n : ℕ) : ℝ))) atTop (𝓝 (1 / 2)) := by
      have e : ∀ n : ℕ, (1 + (n : ℝ)) / (1 + ((2 * n : ℕ) : ℝ)) =
          (1 / 2 : ℝ) + (1 / 2) * (1 / (1 + 2 * (n : ℝ))) := by
        intro n
        push_cast
        field_simp
        ring
      simp_rw [e]
      have : Tendsto (fun n : ℕ => 1 / (1 + 2 * (n : ℝ))) atTop (𝓝 0) := by
        apply Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_left _ _
          (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
      simpa using (this.const_mul (1 / 2 : ℝ)).const_add (1 / 2 : ℝ)
    exact r.rpow_const (Or.inr hp.le)
  have hne : (1 / (1 - d)) ≠ 0 := by positivity
  have key := (A.div B hne).mul C
  rw [show 1 / (1 - d) / (1 / (1 - d)) * (1 / 2 : ℝ) ^ (1 - d) = (2 : ℝ) ^ (-(1 - d)) by
    rw [div_self (by positivity), one_mul, Real.rpow_neg (by norm_num), Real.div_rpow
      (by norm_num) (by norm_num), Real.one_rpow, one_div]] at key
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : 0 < baseSpaced d n := by
    have := (baseSpaced_bounds hd0 hd n).1
    have : 1 < (1 + n : ℝ) ^ (1 - d) :=
      Real.one_lt_rpow (by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                           linarith) hp
    have : 0 < ((1 + n : ℝ) ^ (1 - d) - 1) / (1 - d) := div_pos (by linarith) hp
    linarith
  have h2 : 0 < baseSpaced d (2 * n) := by
    have := (baseSpaced_bounds hd0 hd (2 * n)).1
    have : 1 < (1 + ((2 * n : ℕ) : ℝ)) ^ (1 - d) :=
      Real.one_lt_rpow (by have : (1 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega)
                           linarith) hp
    have : 0 < ((1 + ((2 * n : ℕ) : ℝ)) ^ (1 - d) - 1) / (1 - d) := div_pos (by linarith) hp
    linarith
  have p1 : 0 < (1 + (n : ℝ)) ^ (1 - d) := Real.rpow_pos_of_pos (by positivity) _
  have p2 : 0 < (1 + ((2 * n : ℕ) : ℝ)) ^ (1 - d) := Real.rpow_pos_of_pos (by positivity) _
  simp only [spacedR, Pi.div_apply]
  rw [Real.div_rpow (by positivity) (by positivity)]
  field_simp

/-- **Approximately a power law with exponent `1 - d`.** For every tolerance
`ε > 0`, beyond some trial, doubling practice multiplies latency by
`2^(-(1-d))` to within relative error `ε`. -/
theorem spacedR_approx_powerLaw (F : ℝ) (hF : 0 < F) (hd0 : 0 ≤ d) (hd : d < 1) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n →
      (1 - ε) * ((2 : ℝ) ^ (-(1 - d)) * spacedR F d n) ≤ spacedR F d (2 * n) ∧
        spacedR F d (2 * n) ≤ (1 + ε) * ((2 : ℝ) ^ (-(1 - d)) * spacedR F d n) := by
  set r := (2 : ℝ) ^ (-(1 - d))
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have T := spacedR_doubling_tendsto F hF.ne' hd0 hd
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp T (ε * r) (by positivity)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have h := hN n (le_trans (le_max_left _ _) hn)
  rw [Real.dist_eq, abs_lt] at h
  have hb : 0 < baseSpaced d n := by
    have := (baseSpaced_bounds hd0 hd n).1
    have : 1 < (1 + n : ℝ) ^ (1 - d) :=
      Real.one_lt_rpow (by have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
                           linarith) (by linarith)
    have : 0 < ((1 + n : ℝ) ^ (1 - d) - 1) / (1 - d) := div_pos (by linarith) (by linarith)
    linarith
  have hT : 0 < spacedR F d n := div_pos hF hb
  have e : spacedR F d (2 * n) = (spacedR F d (2 * n) / spacedR F d n) * spacedR F d n := by
    field_simp
  constructor
  · rw [e]; nlinarith
  · rw [e]; nlinarith

end Cog.ACTR
