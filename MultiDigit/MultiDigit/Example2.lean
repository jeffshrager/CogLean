/-
A concrete case of the further features (M1a-M1c), as a check that the laws
can be met and that they change which confusions occur. It is not evidence:
every number here is chosen for illustration.

* Encoding (`rich`), 360 features:
  - for each digit of each addend, a zero flag and nine thresholds
    ("exceeds k", a thermometer code);
  - for each column, a one-hot code of its unordered pair of digits, at
    index min * 10 + max, so 3 + 4 and 4 + 3 are the same fact.

  It satisfies M1 (the thresholds determine the digit), `Zeros`, `Magnitude`
  and `ColumnFacts`.
* Noticing order: the zero flags first, then the thresholds, hundreds first,
  then the column facts.

Two nets, each learned by EPAM from two familiar problems:

* 100 + 100 and 120 + 100 differ first in a zero flag, so the net tests it.
  150 + 100, which BCD's net took for 100 + 100 (`Example.lean`), is now
  taken for 120 + 100: a zero tested keeps it off the round problem
  (`zeros_example`).
* 700 + 100 and 800 + 100. Under thresholds, 600 + 100 is taken for its
  neighbour 700 + 100 (off by 100). Under BCD, 7 = 0111 and 8 = 1000 differ
  first in bit 0, and 600 + 100 is taken for 800 + 100 (off by 200)
  (`magnitude_example`).
-/

import MultiDigit.Features
import MultiDigit.Example

namespace MD.Example2

open Cog MD MD.Example

/-- The first feature of digit `j` of addend `i`: its zero flag. Its nine
thresholds follow. -/
def digitBase (i : Addend) (j : Place) : Nat := (addIdx i * 3 + placeIdx j) * 10

/-- The index of a column's unordered fact. -/
def factIdx (p : Problem) (j : Place) : Nat :=
  min (p.digit .first j) (p.digit .second j) * 10 + max (p.digit .first j) (p.digit .second j)

def factBase (j : Place) : Nat := 60 + placeIdx j * 100

/-- The value of feature `f` of problem `p`. -/
def richFeat (p : Problem) (f : Nat) : Bool :=
  if f < 60 then
    let d := p.digit (addOf (f / 30)) (placeOf (f % 30 / 10))
    if f % 10 = 0 then d == 0 else decide (f % 10 - 1 < d)
  else factIdx p (placeOf ((f - 60) / 100)) == (f - 60) % 100

def richCode (p : Problem) : Item := (List.range 360).map (richFeat p)

theorem feat_richCode (p : Problem) (f : Nat) (hf : f < 360) :
    (richCode p).feat f = richFeat p f := by
  simp only [Item.feat, richCode, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hf, Option.map_some, Option.getD_some]

theorem digitBase_lt (i : Addend) (j : Place) : digitBase i j + 9 < 60 := by
  cases i <;> cases j <;> decide

theorem addOf_digitBase (i : Addend) (j : Place) (k : Nat) (hk : k < 10) :
    addOf ((digitBase i j + k) / 30) = i := by
  revert k; cases i <;> cases j <;> decide

theorem placeOf_digitBase (i : Addend) (j : Place) (k : Nat) (hk : k < 10) :
    placeOf ((digitBase i j + k) % 30 / 10) = j := by
  revert k; cases i <;> cases j <;> decide

theorem richFeat_digit (p : Problem) (i : Addend) (j : Place) (k : Nat) (hk : k < 10) :
    richFeat p (digitBase i j + k) =
      if k = 0 then p.digit i j == 0 else decide (k - 1 < p.digit i j) := by
  have hlt := digitBase_lt i j
  have hmod : (digitBase i j + k) % 10 = k := by
    revert hk; cases i <;> cases j <;> simp only [digitBase, addIdx, placeIdx] <;> omega
  simp only [richFeat, show digitBase i j + k < 60 by omega, ite_true, hmod,
    addOf_digitBase i j k hk, placeOf_digitBase i j k hk]

/-- The thresholds determine the digit. -/
theorem thresholds_determine : ∀ d, d < 10 → ∀ e, e < 10 →
    (∀ k, k < 9 → decide (k < d) = decide (k < e)) → d = e := by
  decide

def thresholds (i : Addend) (j : Place) : List Feature :=
  (List.range 9).map fun k => digitBase i j + 1 + k

theorem reads_above (p : Problem) (i : Addend) (j : Place) (k : Nat) (hk : k < 9) :
    (richCode p).feat (digitBase i j + 1 + k) = decide (k < p.digit i j) := by
  have hlt := digitBase_lt i j
  rw [feat_richCode p _ (by omega), show digitBase i j + 1 + k = digitBase i j + (k + 1) by omega,
    richFeat_digit p i j (k + 1) (by omega)]
  simp

/-- M1: the thresholds of each digit determine it. -/
def rich : Encoding where
  code := richCode
  features := thresholds
  determines := by
    intro p q i j h
    apply thresholds_determine _ (digit_lt p i j) _ (digit_lt q i j)
    intro k hk
    rw [← reads_above p i j k hk, ← reads_above q i j k hk]
    exact h _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)

/-- M1a. -/
def richZeros : Zeros rich where
  zero := digitBase
  reads := by
    intro p i j
    have hlt := digitBase_lt i j
    show (richCode p).feat (digitBase i j) = _
    rw [feat_richCode p _ (by omega)]
    have := richFeat_digit p i j 0 (by decide)
    simpa using this

/-- M1b. -/
def richMagnitude : Magnitude rich where
  above i j k := digitBase i j + 1 + k
  reads := fun p i j k hk => reads_above p i j k hk

theorem factIdx_lt (p : Problem) (j : Place) : factIdx p j < 100 := by
  have := digit_lt p .first j
  have := digit_lt p .second j
  simp only [factIdx]
  omega

theorem richFeat_fact (p : Problem) (j : Place) (m : Nat) (hm : m < 100) :
    richFeat p (factBase j + m) = (factIdx p j == m) := by
  have hj : placeOf ((factBase j + m - 60) / 100) = j := by
    have : (factBase j + m - 60) / 100 = placeIdx j := by
      cases j <;> simp only [factBase, placeIdx] <;> omega
    rw [this]; cases j <;> rfl
  have hm' : (factBase j + m - 60) % 100 = m := by
    cases j <;> simp only [factBase, placeIdx] <;> omega
  simp only [richFeat, show ¬ factBase j + m < 60 by simp only [factBase]; omega, ite_false, hj, hm']

theorem factBase_lt (j : Place) (m : Nat) (hm : m < 100) : factBase j + m < 360 := by
  cases j <;> simp only [factBase, placeIdx] <;> omega

/-- M1c: a column's fact determines its sum. -/
def richFacts : ColumnFacts rich where
  fact j := (List.range 100).map (factBase j + ·)
  determines := by
    intro j p q h
    have hp := factIdx_lt p j
    have hf := h (factBase j + factIdx p j) (List.mem_map.mpr ⟨_, List.mem_range.mpr hp, rfl⟩)
    have hcode : ∀ r : Problem, rich.code r = richCode r := fun _ => rfl
    rw [hcode, hcode, feat_richCode p _ (factBase_lt j _ hp),
      feat_richCode q _ (factBase_lt j _ hp), richFeat_fact p j _ hp,
      richFeat_fact q j _ hp] at hf
    simp only [beq_self_eq_true] at hf
    have heq : factIdx q j = factIdx p j := by simpa using hf.symm
    have := digit_lt p .first j; have := digit_lt p .second j
    have := digit_lt q .first j; have := digit_lt q .second j
    simp only [factIdx] at heq
    simp only [Problem.colSum]
    omega

/-- Zero flags first, then thresholds, hundreds first, then column facts. -/
def richOrder : NoticingOrder :=
  ([Place.hundreds, .tens, .units].flatMap fun j =>
      [Addend.first, .second].map fun i => digitBase i j) ++
    ([Place.hundreds, .tens, .units].flatMap fun j =>
      [Addend.first, .second].flatMap fun i => (List.range 9).map (digitBase i j + 1 + ·)) ++
    ([Place.hundreds, .tens, .units].flatMap fun j => (List.range 100).map (factBase j + ·))

def learn2 (E : Encoding) (order : NoticingOrder) (p q : Problem) : Net :=
  ((Net.leaf none).learn order (E.code p)).learn order (E.code q)

def r1 : Problem := ⟨100, 100⟩
def r2 : Problem := ⟨120, 100⟩

/-- **A zero tested keeps 150 + 100 off the round problem.** The net learned
from 100 + 100 and 120 + 100 tests the first addend's tens zero flag, and
takes 150 + 100 for 120 + 100, not 100 + 100. -/
theorem zeros_example :
    (learn2 rich richOrder r1 r2).path (rich.code x) = [digitBase .first .tens] ∧
      (learn2 rich richOrder r1 r2).select (rich.code x) = some (rich.code r2) := by
  decide +kernel

def n7 : Problem := ⟨700, 100⟩
def n8 : Problem := ⟨800, 100⟩
def n6 : Problem := ⟨600, 100⟩

/-- **Thresholds make neighbours confusable; BCD does not.** From 700 + 100
and 800 + 100: under thresholds, 600 + 100 is taken for 700 + 100 (off by
100); under BCD, for 800 + 100 (off by 200). -/
theorem magnitude_example :
    (learn2 rich richOrder n7 n8).select (rich.code n6) = some (rich.code n7) ∧
      (learn2 bcd order n7 n8).select (bcd.code n6) = some (bcd.code n8) := by
  decide +kernel

end MD.Example2
