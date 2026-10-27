/-
What the further problem features (M1a-M1c) predict about confusions.

Every theorem holds for any encoding satisfying the law in question, and any
net, strengths, criterion, search length and backup. Each says that a
confused problem agrees with what it is confused with on whatever the
features its path tests determine (`Net.confusion_preserves`).

* Zeros: `confusion_keeps_zeros`; `round_confusion_exact`,
  `round_confusion_harmless`: a problem confused with a round one, by a net
  that tests the zeros of the tens and units and the hundreds digits, is that
  round problem.
* Magnitude: `confusion_same_side`, `confusion_within_gap`: a confused digit
  lies between the same tested thresholds as the true one, so the error in
  it is less than the gap between them.
* Column facts: `facts_same_sum`, `facts_tested_harmless`: with all three
  column facts tested, a confusion costs nothing; `facts_mod_100`, `facts_mod_10`: with only the
  low columns' facts tested, the error is a multiple of 100 (of 10).
* `round_confusion_exact_learned`, `facts_same_sum_learned`: the
  same, with no hypothesis on the net, for every net EPAM learns from an
  empty one.
-/

import MultiDigit.Features
import MultiDigit.Learning
import MultiDigit.Columns

namespace MD

open Cog Dist

variable {E : Encoding} (N : Net) (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat)
  (backup : Problem → Dist Nat)

/-! ### Zeros (M1a) -/

/-- **Confusions keep zeros.** If `x`'s path tests whether a digit is 0, `x`
has a 0 there exactly when `q` does. -/
theorem confusion_keeps_zeros (Z : Zeros E) (x q : Problem) (i : Addend) (j : Place)
    (hnd : N.images.Nodup) (hq : N.select (E.code q) = some (E.code q))
    (hx : N.select (E.code x) = some (E.code q)) (hcover : Z.zero i j ∈ N.path (E.code x)) :
    x.digit i j = 0 ↔ q.digit i j = 0 := by
  have := Net.confusion_preserves N E.code _ _ (Z.determines i j) x q hnd hq hx
    (by simpa using hcover)
  have hb : (x.digit i j == 0) = (q.digit i j == 0) := this
  constructor
  · intro h
    have h' : (q.digit i j == 0) = true := by rw [← hb]; simp [h]
    simpa using h'
  · intro h
    have h' : (x.digit i j == 0) = true := by rw [hb]; simp [h]
    simpa using h'

/-- A problem is fixed by its digits. -/
theorem Problem.eq_of_digits (x q : Problem) (h : ∀ i j, x.digit i j = q.digit i j)
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) : x = q := by
  have h1 := h .first .hundreds; have h2 := h .first .tens; have h3 := h .first .units
  have h4 := h .second .hundreds; have h5 := h .second .tens; have h6 := h .second .units
  simp only [Problem.digit, Problem.addend, digitOf] at h1 h2 h3 h4 h5 h6
  cases x; cases q
  simp only [Problem.mk.injEq] at *
  omega

/-- **Confusion with a round problem is exact.** Let `q` be round, and let
`x`'s path test the zeros of both addends' tens and units, and both hundreds
digits. Then a problem confused with `q` is `q`. -/
theorem round_confusion_exact (Z : Zeros E) (x q : Problem) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hround : q.Round)
    (hz : ∀ i, ∀ j, j ≠ Place.hundreds → Z.zero i j ∈ N.path (E.code x))
    (hh : ∀ i, ∀ f ∈ E.features i .hundreds, f ∈ N.path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) : x = q := by
  obtain ⟨⟨t1, t2⟩, ⟨u1, u2⟩⟩ := hround
  apply Problem.eq_of_digits x q _ hxa hxb hqa hqb
  intro i j
  cases j with
  | hundreds => exact confused_digit E N x q i .hundreds hnd hq hx (hh i)
  | tens =>
    have := confusion_keeps_zeros N Z x q i .tens hnd hq hx (hz i .tens (by decide))
    cases i <;> simp_all
  | units =>
    have := confusion_keeps_zeros N Z x q i .units hnd hq hx (hz i .units (by decide))
    cases i <;> simp_all

/-- So such a confusion is harmless: whole-problem retrieval errs on `x`
exactly as often as on `q`. -/
theorem round_confusion_harmless (Z : Zeros E) (x q : Problem) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hround : q.Round)
    (hz : ∀ i, ∀ j, j ≠ Place.hundreds → Z.zero i j ∈ N.path (E.code x))
    (hh : ∀ i, ∀ f ∈ E.features i .hundreds, f ∈ N.path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    prob (trial E N str as cc n backup x) (wholeWrong x) =
      prob (trial E N str as cc n backup q) (wholeWrong q) := by
  rw [round_confusion_exact N Z x q hnd hq hx hround hz hh hxa hxb hqa hqb]

/-! ### Magnitude (M1b) -/

/-- **Confusions keep the side of a tested threshold.** -/
theorem confusion_same_side (M : Magnitude E) (x q : Problem) (i : Addend) (j : Place) (k : Nat)
    (hnd : N.images.Nodup) (hq : N.select (E.code q) = some (E.code q))
    (hx : N.select (E.code x) = some (E.code q)) (hk : k < 9)
    (hcover : M.above i j k ∈ N.path (E.code x)) :
    k < x.digit i j ↔ k < q.digit i j := by
  have := Net.confusion_preserves N E.code _ _ (M.determines i j k hk) x q hnd hq hx
    (by simpa using hcover)
  simpa [decide_eq_decide] using this

/-- **Errors within the gap.** If `x`'s path tests thresholds `lo` and `hi` (each below 9),
and `q`'s digit lies above `lo` and at most `hi`, so does `x`'s; the two
digits differ by less than `hi - lo`. -/
theorem confusion_within_gap (M : Magnitude E) (x q : Problem) (i : Addend) (j : Place)
    (lo hi : Nat) (hnd : N.images.Nodup) (hq : N.select (E.code q) = some (E.code q))
    (hx : N.select (E.code x) = some (E.code q))
    (hlo9 : lo < 9) (hhi9 : hi < 9)
    (hlo : M.above i j lo ∈ N.path (E.code x)) (hhi : M.above i j hi ∈ N.path (E.code x))
    (hql : lo < q.digit i j) (hqh : q.digit i j ≤ hi) :
    lo < x.digit i j ∧ x.digit i j ≤ hi ∧
      x.digit i j - q.digit i j + (q.digit i j - x.digit i j) < hi - lo := by
  have h1 := (confusion_same_side N M x q i j lo hnd hq hx hlo9 hlo).2 hql
  have h2 := confusion_same_side N M x q i j hi hnd hq hx hhi9 hhi
  have h3 : x.digit i j ≤ hi := Nat.le_of_not_lt fun h => absurd (h2.1 h) (by omega)
  omega

/-! ### Column facts (M1c) -/

theorem confused_colSum (C : ColumnFacts E) (x q : Problem) (j : Place) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hcover : ∀ f ∈ C.fact j, f ∈ N.path (E.code x)) : x.colSum j = q.colSum j :=
  Net.confusion_preserves N E.code _ _ (C.determines j) x q hnd hq hx hcover

/-- An addend's last two digits, in terms of its tens and units. -/
theorem addend_mod_100 (p : Problem) (i : Addend) :
    p.addend i % 100 = 10 * p.digit i .tens + p.digit i .units := by
  simp only [Problem.digit, digitOf]
  omega

theorem addend_mod_10 (p : Problem) (i : Addend) : p.addend i % 10 = p.digit i .units := by
  simp only [Problem.digit, digitOf]

theorem sum_mod_100 (p : Problem) :
    p.sum % 100 = (10 * p.colSum .tens + p.colSum .units) % 100 := by
  have h1 := addend_mod_100 p .first
  have h2 := addend_mod_100 p .second
  simp only [Problem.addend] at h1 h2
  simp only [Problem.sum, Problem.colSum, Nat.add_mod p.a p.b, h1, h2]
  omega

theorem sum_mod_10 (p : Problem) : p.sum % 10 = p.colSum .units % 10 := by
  have h1 := addend_mod_10 p .first
  have h2 := addend_mod_10 p .second
  simp only [Problem.addend] at h1 h2
  simp only [Problem.sum, Problem.colSum, Nat.add_mod p.a p.b, h1, h2]

/-- **With every column's fact tested, a confused problem has the right
sum.** -/
theorem facts_same_sum (C : ColumnFacts E) (x q : Problem) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hcover : ∀ j, ∀ f ∈ C.fact j, f ∈ N.path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    x.sum = q.sum := by
  have h1 := confused_colSum N C x q .hundreds hnd hq hx (hcover _)
  have h2 := confused_colSum N C x q .tens hnd hq hx (hcover _)
  have h3 := confused_colSum N C x q .units hnd hq hx (hcover _)
  simp only [Problem.colSum] at h1 h2 h3
  rw [sum_place_value x hxa hxb, sum_place_value q hqa hqb, h1, h2, h3]

/-- **So the confusion costs nothing**: whole-problem retrieval errs on `x`
exactly as often as on `q`. -/
theorem facts_tested_harmless (C : ColumnFacts E) (x q : Problem) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hcover : ∀ j, ∀ f ∈ C.fact j, f ∈ N.path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    prob (trial E N str as cc n backup x) (wholeWrong x) =
      prob (trial E N str as cc n backup q) (wholeWrong q) :=
  same_sum_confusion_harmless E N str as cc n backup x q hq hx
    (facts_same_sum N C x q hnd hq hx hcover hxa hxb hqa hqb)

/-- **With the tens' and units' facts tested, the error is a multiple of
100.** -/
theorem facts_mod_100 (C : ColumnFacts E) (x q : Problem) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hcover : ∀ j, j ≠ Place.hundreds → ∀ f ∈ C.fact j, f ∈ N.path (E.code x)) :
    x.sum % 100 = q.sum % 100 := by
  rw [sum_mod_100, sum_mod_100,
    confused_colSum N C x q .tens hnd hq hx (hcover _ (by decide)),
    confused_colSum N C x q .units hnd hq hx (hcover _ (by decide))]

/-- **With the units' fact tested, the error is a multiple of 10.** -/
theorem facts_mod_10 (C : ColumnFacts E) (x q : Problem) (hnd : N.images.Nodup)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hcover : ∀ f ∈ C.fact .units, f ∈ N.path (E.code x)) :
    x.sum % 10 = q.sum % 10 := by
  rw [sum_mod_10, sum_mod_10, confused_colSum N C x q .units hnd hq hx hcover]

/-! ### For nets EPAM learns -/

/-- `round_confusion_exact` for every net EPAM learns from an empty one. -/
theorem round_confusion_exact_learned (Z : Zeros E) (order : NoticingOrder) (xs : List Item)
    (x q : Problem)
    (hx : (Net.learnAll order (Net.leaf none) xs).select (E.code x) = some (E.code q))
    (hround : q.Round)
    (hz : ∀ i, ∀ j, j ≠ Place.hundreds →
      Z.zero i j ∈ (Net.learnAll order (Net.leaf none) xs).path (E.code x))
    (hh : ∀ i, ∀ f ∈ E.features i .hundreds,
      f ∈ (Net.learnAll order (Net.leaf none) xs).path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) : x = q := by
  have hc := Net.learnAll_clean order xs _ Net.clean_empty
  exact round_confusion_exact _ Z x q hc.1 (clean_target hc hx) hx hround hz hh hxa hxb hqa hqb

/-- `facts_same_sum` for every net EPAM learns from an empty one. -/
theorem facts_same_sum_learned (C : ColumnFacts E) (order : NoticingOrder)
    (xs : List Item) (x q : Problem)
    (hx : (Net.learnAll order (Net.leaf none) xs).select (E.code x) = some (E.code q))
    (hcover : ∀ j, ∀ f ∈ C.fact j, f ∈ (Net.learnAll order (Net.leaf none) xs).path (E.code x))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    x.sum = q.sum := by
  have hc := Net.learnAll_clean order xs _ Net.clean_empty
  exact facts_same_sum _ C x q hc.1 (clean_target hc hx) hx hcover hxa hxb hqa hqb

end MD
