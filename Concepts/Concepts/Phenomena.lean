/-
The selective modification model's predictions, for every prototype and
every choice of parameters satisfying the stated conditions.

* `conjunction_effect`: an instance with the adjective's value is more
  typical of the combination than of the noun (pp. 493–494).
* `reverse_conjunction_effect`: an instance with another value is less
  typical of it.
* `attribute_not_value`: an instance's typicality in "red apple" equals
  a brown one's in "brown apple": what matters is the attribute, not the
  value (p. 495).
* `overExtends_binary`, `member_mono`: over-extension. Under yes/no
  membership at some criterion, and under any nondecreasing graded
  membership (H1), the instance is never less a member of the combination
  than of the noun.

Conditions: the instance's votes on the selected attribute number the
prototype's total there (SO2), `T > 0`; the attribute is diagnostic,
`d > 0`; votes are nonnegative; the boost is at least 1. Strictness needs
something to change: the boost exceeds 1, or the noun's votes were not
all on the value already.
-/

import Concepts.Postulates

namespace Concepts

open Cog

variable {A V : Type} [DecidableEq A] [DecidableEq V]

theorem min_of_le {x y : Rat} (h : x ≤ y) : min x y = x := by
  rw [Rat.min_def]; simp [h]

/-- The contrast on the selected attribute after modification, for an
instance with all `T` votes on value `w`. -/
theorem modified_contrast (K : Contrast) (vs : List V) (hvs : vs.Nodup) (v0 w : V)
    (hv0 : v0 ∈ vs) (hw : w ∈ vs) (T : Rat) (hT : 0 ≤ T) :
    attrContrast K vs (fun v => if v = v0 then T else 0) (fun v => if v = w then T else 0) =
      if w = v0 then K.a * T else -(K.b * T) - K.c * T := by
  rw [attrContrast_pure K vs _ (fun v => by split <;> grind) w T hvs hw, votesOn_pure vs v0 T hvs hv0]
  by_cases h : w = v0
  · simp only [h, ite_true, min_of_le (Rat.le_refl (a := T))]; grind
  · simp only [h, ite_false]
    have : min (0 : Rat) T = 0 := by rw [Rat.min_def]; simp [hT]
    rw [this]; grind

/-- **The conjunction effect.** -/
theorem conjunction_effect (Q : Params) (S : Schema A V) (hnd : S.attrs.Nodup) (i0 : A)
    (hi : i0 ∈ S.attrs) (v0 : V) (hvs : (S.vals i0).Nodup) (hv0 : v0 ∈ S.vals i0)
    (P : Proto A V) (hp : ∀ v, 0 ≤ P.votes i0 v) (hd : 0 < P.diag i0)
    (ha : 0 < Q.K.a) (hb : 0 ≤ Q.K.b) (hc : 0 ≤ Q.K.c) (hboost : 1 ≤ Q.boost)
    (hT : 0 < votesOn (S.vals i0) (P.votes i0))
    (hchange : 1 < Q.boost ∨ P.votes i0 v0 < votesOn (S.vals i0) (P.votes i0))
    (I : Inst A V) (hI : I i0 = fun v => if v = v0 then votesOn (S.vals i0) (P.votes i0) else 0) :
    ConjunctionEffect Q.K S (combine Q S i0 v0 P) P I := by
  unfold ConjunctionEffect combine
  rw [sim_modify Q.K S hnd Q.boost i0 hi v0 P I, hI]
  generalize hTdef : votesOn (S.vals i0) (P.votes i0) = T at *
  rw [modified_contrast Q.K _ hvs v0 v0 hv0 hv0 T (Rat.le_of_lt hT)]
  rw [attrContrast_pure Q.K _ _ hp v0 T hvs hv0, hTdef]
  have hle : P.votes i0 v0 ≤ T := hTdef ▸ le_votesOn _ _ hp v0 hv0
  rw [min_of_le hle]
  simp only [ite_true]
  -- with p = votes on v0 and d the diagnosticity: d·(a·p − (b+c)(T − p)) < boost·d·(a·T)
  generalize P.votes i0 v0 = p at *
  generalize P.diag i0 = d at *
  have h1 : 0 ≤ Q.K.b * (T - p) := Rat.mul_nonneg hb (by grind)
  have h2 : 0 ≤ Q.K.c * (T - p) := Rat.mul_nonneg hc (by grind)
  have h3 : Q.K.a * p ≤ Q.K.a * T := Rat.mul_le_mul_of_nonneg_left hle (Rat.le_of_lt ha)
  have h4 : 0 < Q.K.a * T := Rat.mul_pos ha hT
  have hX : Q.K.a * p - Q.K.b * (T - p) - Q.K.c * (T - p) < Q.boost * (Q.K.a * T) := by
    rcases hchange with hk | hlt
    · have : 0 < (Q.boost - 1) * (Q.K.a * T) := Rat.mul_pos (by grind) h4
      grind
    · have : Q.K.a * p < Q.K.a * T := (Rat.mul_lt_mul_left ha).mpr hlt
      have : 0 ≤ (Q.boost - 1) * (Q.K.a * T) := Rat.mul_nonneg (by grind) (Rat.le_of_lt h4)
      grind
  have := (Rat.mul_lt_mul_left hd).mpr hX
  grind

/-- **The reverse conjunction effect.** -/
theorem reverse_conjunction_effect (Q : Params) (S : Schema A V) (hnd : S.attrs.Nodup) (i0 : A)
    (hi : i0 ∈ S.attrs) (v0 w : V) (hw0 : w ≠ v0) (hvs : (S.vals i0).Nodup)
    (hv0 : v0 ∈ S.vals i0) (hw : w ∈ S.vals i0)
    (P : Proto A V) (hp : ∀ v, 0 ≤ P.votes i0 v) (hd : 0 < P.diag i0)
    (ha : 0 ≤ Q.K.a) (hbc : 0 < Q.K.b + Q.K.c)
    (hboost : 1 ≤ Q.boost) (hT : 0 < votesOn (S.vals i0) (P.votes i0))
    (hchange : 1 < Q.boost ∨ 0 < P.votes i0 w)
    (I : Inst A V) (hI : I i0 = fun v => if v = w then votesOn (S.vals i0) (P.votes i0) else 0) :
    ReverseConjunctionEffect Q.K S (combine Q S i0 v0 P) P I := by
  unfold ReverseConjunctionEffect combine
  rw [sim_modify Q.K S hnd Q.boost i0 hi v0 P I, hI]
  generalize hTdef : votesOn (S.vals i0) (P.votes i0) = T at *
  rw [modified_contrast Q.K _ hvs v0 w hv0 hw T (Rat.le_of_lt hT)]
  rw [attrContrast_pure Q.K _ _ hp w T hvs hw, hTdef]
  have hle : P.votes i0 w ≤ T := hTdef ▸ le_votesOn _ _ hp w hw
  rw [min_of_le hle]
  simp only [hw0, ite_false]
  have hp0 : 0 ≤ P.votes i0 w := hp w
  generalize P.votes i0 w = p at *
  generalize P.diag i0 = d at *
  -- boost·d·(−(b+c)·T) < d·(a·p − (b+c)(T − p))
  have h1 : 0 ≤ Q.K.a * p := Rat.mul_nonneg ha hp0
  have h4 : 0 < (Q.K.b + Q.K.c) * T := Rat.mul_pos hbc hT
  have hX : Q.boost * (-(Q.K.b * T) - Q.K.c * T) <
      Q.K.a * p - Q.K.b * (T - p) - Q.K.c * (T - p) := by
    have e1 : Q.boost * (-(Q.K.b * T) - Q.K.c * T) = -(Q.boost * ((Q.K.b + Q.K.c) * T)) := by
      grind
    have e2 : Q.K.b * (T - p) + Q.K.c * (T - p) = (Q.K.b + Q.K.c) * T - (Q.K.b + Q.K.c) * p := by
      grind
    rcases hchange with hk | hpos
    · have : 0 < (Q.boost - 1) * ((Q.K.b + Q.K.c) * T) := Rat.mul_pos (by grind) h4
      have : 0 ≤ (Q.K.b + Q.K.c) * p := Rat.mul_nonneg (by grind) hp0
      grind
    · have : 0 < (Q.K.b + Q.K.c) * p := Rat.mul_pos hbc hpos
      have : 0 ≤ (Q.boost - 1) * ((Q.K.b + Q.K.c) * T) :=
        Rat.mul_nonneg (by grind) (Rat.le_of_lt h4)
      grind
  have := (Rat.mul_lt_mul_left hd).mpr hX
  grind

/-- **What matters is the attribute, not the value.** An instance with value
`v` is as typical of "`v` noun" as one with value `w`, otherwise the same,
is of "`w` noun", for every choice of parameters. -/
theorem attribute_not_value (Q : Params) (S : Schema A V) (hnd : S.attrs.Nodup) (i0 : A)
    (hi : i0 ∈ S.attrs) (v w : V) (hvs : (S.vals i0).Nodup) (hv : v ∈ S.vals i0)
    (hw : w ∈ S.vals i0) (P : Proto A V) (hp : ∀ u, 0 ≤ P.votes i0 u)
    (I J : Inst A V) (hIJ : ∀ i, i ≠ i0 → I i = J i)
    (hI : I i0 = fun u => if u = v then votesOn (S.vals i0) (P.votes i0) else 0)
    (hJ : J i0 = fun u => if u = w then votesOn (S.vals i0) (P.votes i0) else 0) :
    typicality Q S (combine Q S i0 v P) I = typicality Q S (combine Q S i0 w P) J := by
  unfold typicality combine
  rw [sim_modify Q.K S hnd Q.boost i0 hi v P I, sim_modify Q.K S hnd Q.boost i0 hi w P J, hI, hJ]
  have hT := votesOn_nonneg (S.vals i0) (P.votes i0) hp
  rw [modified_contrast Q.K _ hvs v v hv hv _ hT, modified_contrast Q.K _ hvs w w hw hw _ hT]
  have hsum : sim Q.K S P I = sim Q.K S P J +
      (P.diag i0 * attrContrast Q.K (S.vals i0) (P.votes i0) (I i0) -
        P.diag i0 * attrContrast Q.K (S.vals i0) (P.votes i0) (J i0)) := by
    unfold sim
    exact sum_map_update S.attrs hnd i0 hi _ _ (fun i hne => by rw [hIJ i hne])
  rw [hsum, hI, hJ]
  simp only [ite_true]
  grind

/-- **Over-extension, yes/no**: at some criterion, an instance with the
adjective's value is judged a member of the combination and not of the noun. -/
theorem overExtends_binary (Q : Params) (S : Schema A V) (hnd : S.attrs.Nodup) (i0 : A)
    (hi : i0 ∈ S.attrs) (v0 : V) (hvs : (S.vals i0).Nodup) (hv0 : v0 ∈ S.vals i0)
    (P : Proto A V) (hp : ∀ v, 0 ≤ P.votes i0 v) (hd : 0 < P.diag i0)
    (ha : 0 < Q.K.a) (hb : 0 ≤ Q.K.b) (hc : 0 ≤ Q.K.c) (hboost : 1 ≤ Q.boost)
    (hT : 0 < votesOn (S.vals i0) (P.votes i0))
    (hchange : 1 < Q.boost ∨ P.votes i0 v0 < votesOn (S.vals i0) (P.votes i0))
    (I : Inst A V) (hI : I i0 = fun v => if v = v0 then votesOn (S.vals i0) (P.votes i0) else 0) :
    ∃ θ, OverExtendsBinary θ Q.K S (combine Q S i0 v0 P) P I :=
  overExtends_binary_of_conjunctionEffect _ _ _ _ _
    (conjunction_effect Q S hnd i0 hi v0 hvs hv0 P hp hd ha hb hc hboost hT hchange I hI)

/-- **Never under-extended**: under any nondecreasing membership, such an
instance is at least as much a member of the combination as of the noun. -/
theorem member_mono (Q : Params) (m : Rat → Rat) (hm : Nondecreasing m) (S : Schema A V)
    (hnd : S.attrs.Nodup) (i0 : A) (hi : i0 ∈ S.attrs) (v0 : V) (hvs : (S.vals i0).Nodup)
    (hv0 : v0 ∈ S.vals i0) (P : Proto A V) (hp : ∀ v, 0 ≤ P.votes i0 v) (hd : 0 < P.diag i0)
    (ha : 0 < Q.K.a) (hb : 0 ≤ Q.K.b) (hc : 0 ≤ Q.K.c) (hboost : 1 ≤ Q.boost)
    (hT : 0 < votesOn (S.vals i0) (P.votes i0))
    (hchange : 1 < Q.boost ∨ P.votes i0 v0 < votesOn (S.vals i0) (P.votes i0))
    (I : Inst A V) (hI : I i0 = fun v => if v = v0 then votesOn (S.vals i0) (P.votes i0) else 0) :
    m (sim Q.K S P I) ≤ m (sim Q.K S (combine Q S i0 v0 P) I) :=
  member_mono_of_conjunctionEffect m hm _ _ _ _ _
    (conjunction_effect Q S hnd i0 hi v0 hvs hv0 P hp hd ha hb hc hboost hT hchange I hI)

end Concepts
