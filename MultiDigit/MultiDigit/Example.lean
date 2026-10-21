/-
A concrete case, as a check that the general theorems apply. It is not
evidence: every number here is chosen for illustration.

* Encoding: each digit of each addend in four bits (binary-coded decimal),
  24 features in all. This satisfies M1 (`bcd`).
* Net: EPAM learns two familiar problems, 100 + 100 and 100 + 200, from an
  empty net, scanning the hundreds digits first. They differ only in the
  second addend's hundreds digit, so that is all the net tests.
* Associations: each familiar problem's correct sum has strength .90, and
  every other answer .01; criterion .50.

The unfamiliar 150 + 100 agrees with 100 + 100 on the one feature tested,
and is recognized as it. Whole-problem retrieval answers 200, never 250
(`confusion_gives_neighbours_answer`), and every retrieval trial on it is an
error, while backup use is as low as on 100 + 100 itself
(`confident_errors`). With search length 1, it is answered 200 with
probability 45/46.
-/

import MultiDigit.Phenomena
import MultiDigit.Columns

namespace MD.Example

open Cog Dist MD

def addIdx : Addend → Nat
  | .first => 0
  | .second => 1

def placeIdx : Place → Nat
  | .hundreds => 0
  | .tens => 1
  | .units => 2

/-- Feature number of bit `k` of digit `j` of addend `i`. -/
def featIdx (i : Addend) (j : Place) (k : Nat) : Nat := addIdx i * 12 + placeIdx j * 4 + k

def bit (d k : Nat) : Bool := d / 2 ^ k % 2 == 1

def addOf (m : Nat) : Addend := if m = 0 then .first else .second

def placeOf (m : Nat) : Place := if m = 0 then .hundreds else if m = 1 then .tens else .units

def bcdCode (p : Problem) : Item :=
  (List.range 24).map fun f => bit (p.digit (addOf (f / 12)) (placeOf (f % 12 / 4))) (f % 4)

def bcdFeatures (i : Addend) (j : Place) : List Feature := (List.range 4).map (featIdx i j)

theorem feat_bcdCode (p : Problem) (i : Addend) (j : Place) (k : Nat) (hk : k < 4) :
    (bcdCode p).feat (featIdx i j k) = bit (p.digit i j) k := by
  have h24 : featIdx i j k < 24 := by
    cases i <;> cases j <;> simp [featIdx, addIdx, placeIdx] <;> omega
  simp only [Item.feat, bcdCode, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range h24, Option.map_some, Option.getD_some]
  have hk' : featIdx i j k % 4 = k := by
    cases i <;> cases j <;> simp [featIdx, addIdx, placeIdx] <;> omega
  have ha' : featIdx i j k / 12 = addIdx i := by
    cases i <;> cases j <;> simp only [featIdx, addIdx, placeIdx] <;> omega
  have hp' : featIdx i j k % 12 / 4 = placeIdx j := by
    cases i <;> cases j <;> simp only [featIdx, addIdx, placeIdx] <;> omega
  have ha : addOf (featIdx i j k / 12) = i := by
    rw [ha']; cases i <;> rfl
  have hp : placeOf (featIdx i j k % 12 / 4) = j := by
    rw [hp']; cases j <;> rfl
  rw [hk', ha, hp]

theorem digit_lt (p : Problem) (i : Addend) (j : Place) : p.digit i j < 10 := by
  cases j <;> simp only [Problem.digit, digitOf] <;> exact Nat.mod_lt _ (by decide)

theorem bits_determine : ∀ d, d < 10 → ∀ e, e < 10 → (∀ k, k < 4 → bit d k = bit e k) → d = e := by
  decide

/-- Binary-coded decimal satisfies M1. -/
def bcd : Encoding where
  code := bcdCode
  features := bcdFeatures
  determines := by
    intro p q i j h
    apply bits_determine _ (digit_lt p i j) _ (digit_lt q i j)
    intro k hk
    rw [← feat_bcdCode p i j k hk, ← feat_bcdCode q i j k hk]
    exact h _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)

/-- Scan the hundreds digits first, then tens, then units. -/
def order : NoticingOrder :=
  [Place.hundreds, .tens, .units].flatMap fun j =>
    [Addend.first, .second].flatMap fun i => (List.range 4).map (featIdx i j)

def q1 : Problem := ⟨100, 100⟩
def q2 : Problem := ⟨100, 200⟩
def x : Problem := ⟨150, 100⟩

/-- The net after learning the two familiar problems. -/
def net : Net := ((Net.leaf none).learn order (bcd.code q1)).learn order (bcd.code q2)

theorem net_facts :
    net.images.Nodup ∧ net.select (bcd.code q1) = some (bcd.code q1) ∧
      net.select (bcd.code q2) = some (bcd.code q2) ∧
      net.select (bcd.code x) = some (bcd.code q1) := by
  decide +kernel

def str (y : Item) (a : Nat) : Rat :=
  if y = bcd.code q1 then (if a = 200 then 9 / 10 else 1 / 100)
  else (if a = 300 then 9 / 10 else 1 / 100)

def answers : List Nat := [200, 250, 300]

def backup (p : Problem) : Dist Nat := Dist.pure p.sum

theorem sharp_q1 : Sharp str (1 / 2) (bcd.code q1) q1 := by
  intro a ha
  simp only [above, str, ite_true] at ha
  by_cases h : a = 200
  · exact h
  · simp only [h, ite_false] at ha; exact absurd ha (by decide +kernel)

theorem total_ne (y : Item) : total answers (str y) ≠ 0 := by
  unfold str
  by_cases h : y = bcd.code q1 <;> simp only [h, ite_true, ite_false] <;> decide +kernel

theorem mass_backup (p : Problem) : mass (backup p) = 1 := by
  simp [mass, backup, prob_pure]

/-- 150 + 100 is answered as 100 + 100: by the general theorem, every
whole-problem retrieval on it errs, it never errs on 100 + 100, and backup
use is the same on both. -/
theorem example_confident_errors (n : Nat) :
    prob (trial bcd net str answers (1 / 2) n backup q1) (wholeWrong q1) = 0 ∧
      prob (trial bcd net str answers (1 / 2) n backup x) (wholeWrong x) =
        prob (trial bcd net str answers (1 / 2) n backup x) isWhole ∧
      prob (trial bcd net str answers (1 / 2) n backup x) isColumns =
        prob (trial bcd net str answers (1 / 2) n backup q1) isColumns :=
  confident_errors bcd net str answers (1 / 2) n backup x q1 total_ne (mass_backup x)
    (mass_backup q1) net_facts.2.1 net_facts.2.2.2 sharp_q1 (by decide)

/-- With search length 1: 150 + 100 is answered 200 by whole-problem
retrieval with probability 45/46, and correctly (250, by columns) with
probability 1/46. -/
theorem example_values :
    prob (trial bcd net str answers (1 / 2) 1 backup x) (wholeSuch (· == 200)) = 45 / 46 ∧
      prob (trial bcd net str answers (1 / 2) 1 backup x) (fun o => o.2 == 250) = 1 / 46 := by
  decide +kernel

/-- The column algorithm with exact single-digit facts, carrying: 234 + 578. -/
theorem example_columns :
    columns (fun d e => Dist.pure (d + e)) ⟨234, 578⟩ = Dist.pure 812 := by
  decide +kernel

end MD.Example
