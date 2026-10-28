/-
The counterbalanced experiment (`Counterbalanced.lean`), run with four
memories.

Design `E1`: no prior list; `a = 000`, `b = 110`; probe `x = 010`, one feature
from each. Design `E2`: prior list `[000]`; `a = 100`, `b = 010`; probe
`x = 110`, one feature from each.

| Memory | Δ on `E1` | Δ on `E2` | Why |
|---|---|---|---|
| Activation (ACT-R) | 10/17 > 0 | | recency (`Activation.recency`), so Δ > 0 by `recency_delta_pos` |
| Strength (DOA) | 0 | 0 | order-free (`Strength.orderFree`), so Δ = 0 by `orderFree_delta_zero` |
| Global matching (MINERVA 2) | 0 | 0 | order-free (`Minerva.orderFree`) |
| Discrimination (EPAM) | 0 | −2 | neither law: computed |

EPAM's order effect comes from the shape of the net, not from time. From an
empty net, both orders grow the same test, so there is no effect. After 000,
whichever of `a` and `b` is learned first is tested against 000 and decides
the net's test; the probe then always retrieves the first-learned item. That
is the most extreme primacy possible, Δ = −2, the opposite of recency.

Under forced choice, ACT-R's two orders leave the same chance of retrieving
neither item, so its reported order effect is 10/17 for every guessing bias,
not only for unbiased guessing (`act_report_any_bias`).
-/

import Experiments.Counterbalanced

namespace Cog.Exp.OrderEffect

open Laws Matrix

def E1 : ABBA := ⟨[], bits 0, bits 3, bits 2⟩
def E2 : ABBA := ⟨[bits 0], bits 1, bits 2, bits 3⟩

theorem valid1 : E1.Valid F3 U3 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide +kernel⟩

theorem valid2 : E2.Valid F3 U3 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide +kernel⟩

/-! ### ACT-R: recency, so Δ > 0 -/

def act := actRetriever Activation.P

theorem act_delta_pos : 0 < E1.delta act Activation.empty :=
  recency_delta_pos act _ U3 Activation.P.fs
    (Activation.recency Activation.P U3 (by decide +kernel) (by decide +kernel)) E1 valid1

theorem act_delta : E1.delta act Activation.empty = 10 / 17 := by decide +kernel

/-- Both orders leave the same chance of retrieving neither item, so the
reported order effect is 10/17 whatever the guessing bias. -/
theorem act_report_any_bias (γ : Rat) : E1.deltaRep γ act Activation.empty = 10 / 17 := by
  rw [delta_report _ _ E1 γ valid1.hab, act_delta]
  have h : E1.neither act (E1.memAB act Activation.empty) =
      E1.neither act (E1.memBA act Activation.empty) := by decide +kernel
  rw [h]
  grind

/-! ### Strength and MINERVA: order-free, so Δ = 0 -/

def str := strRetriever Strength.P
def minerva := minRetriever Minerva.P

theorem str_delta (E : ABBA) (hv : E.Valid F3 U3) : E.delta str Strength.s0 = 0 :=
  orderFree_delta_zero str _ U3 F3 (Strength.orderFree Strength.P Strength.s0 U3) E hv

theorem minerva_delta (E : ABBA) (hv : E.Valid F3 U3) : E.delta minerva [] = 0 :=
  orderFree_delta_zero minerva _ U3 F3 (Minerva.orderFree Minerva.P [] U3) E hv

theorem str_minerva_both : E1.delta str Strength.s0 = 0 ∧ E2.delta str Strength.s0 = 0 ∧
    E1.delta minerva [] = 0 ∧ E2.delta minerva [] = 0 :=
  ⟨str_delta E1 valid1, str_delta E2 valid2, minerva_delta E1 valid1, minerva_delta E2 valid2⟩

/-! ### EPAM: neither law, computed -/

def epam := netRetriever F3

theorem epam_delta : E1.delta epam (.leaf none) = 0 ∧ E2.delta epam (.leaf none) = -2 := by
  decide +kernel

end Cog.Exp.OrderEffect
