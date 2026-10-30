/-
Number concepts, where membership has a truth to compare against.

* Attributes computed from a number: parity, last digit, digit sum mod 3,
  number of digits (for numbers below 1000).
* The truth, proved: divisible by 6 iff even and divisible by 3; the
  digit-sum test for 3 and the last-digit test for 2, below 1000.
* A concept's prototype is built from experience, not chosen: its votes
  on each value count the exemplars the learner has seen with that value.
  *multiple of 3* is learned from 3, 6, …, 30. Every diagnosticity is 1.
* *even multiple of 3* is *multiple of 3* modified by *even* (SO4).

Theorems:
* `even_more_typical`: for every even number below 1000, multiple of 3
  or not, the general conjunction effect applies: it is more typical of
  *even multiple of 3* than of *multiple of 3*. So at some criterion each
  even non-multiple of 3 is judged an even multiple of 3 and not a multiple
  of 3 (`even_overExtends`): incoherent, and false.
* `fourteen`: with `a = b = c = 1`, boost 2 and Hampton bounds −50 and 0
  (chosen for illustration), 14 is an *even multiple of 3* to degree
  497/625 (about .80) and a *multiple of 3* to degree 81/1250 (about .06):
  an over-extension (fuzzy logic's min rule would cap the first at the
  second). And 14 is not a multiple of 3. Meanwhile 9, a multiple of 3, is a
  *multiple of 3* only to degree 721/1250 (about .58).
-/

import Concepts.Phenomena

namespace Concepts.Numbers

open Cog

inductive Attr | parity | lastDigit | digitSum3 | size
  deriving DecidableEq

def digitSum3 (n : Nat) : Nat := (n / 100 + n / 10 % 10 + n % 10) % 3

def size (n : Nat) : Nat := if n < 10 then 1 else if n < 100 then 2 else 3

/-- The value of each attribute of `n`. -/
def val (n : Nat) : Attr → Nat
  | .parity => n % 2
  | .lastDigit => n % 10
  | .digitSum3 => digitSum3 n
  | .size => size n

def S : Schema Attr Nat where
  attrs := [.parity, .lastDigit, .digitSum3, .size]
  vals
    | .parity => [0, 1]
    | .lastDigit => List.range 10
    | .digitSum3 => [0, 1, 2]
    | .size => [1, 2, 3]

/-! ### The truth -/

theorem div6_iff (n : Nat) : n % 6 = 0 ↔ n % 2 = 0 ∧ n % 3 = 0 := by omega

theorem digitSum_test : ∀ n, n < 1000 → (digitSum3 n = 0 ↔ n % 3 = 0) := by
  decide +kernel

theorem lastDigit_test (n : Nat) : n % 2 = n % 10 % 2 := by omega

/-! ### Concepts from experience -/

/-- A prototype from exemplars: the votes on each value count the exemplars
with that value. -/
def protoOf (exs : List Nat) : Proto Attr Nat where
  diag _ := 1
  votes i v := ((exs.filter fun e => val e i == v).length : Rat)

/-- The exemplars of *multiple of 3*: 3, 6, …, 30. -/
def exemplars : List Nat := (List.range 10).map fun k => 3 * (k + 1)

def mult3 : Proto Attr Nat := protoOf exemplars

def Q : Params := ⟨⟨1, 1, 1⟩, 2, -50, 0⟩

def evenMult3 : Proto Attr Nat := combine Q S .parity 0 mult3

/-- A number as an instance: on each attribute, all ten votes on its value. -/
def inst (n : Nat) : Inst Attr Nat := Inst.pure (val n) fun _ => 10

theorem parity_total : votesOn (S.vals .parity) (mult3.votes .parity) = 10 := by decide +kernel

/-- **Every even number is more typical of *even multiple of 3* than of
*multiple of 3***, whether or not it is a multiple of 3: the general
conjunction effect, applied. -/
theorem even_more_typical (n : Nat) (he : n % 2 = 0) :
    ConjunctionEffect Q.K S evenMult3 mult3 (inst n) := by
  apply conjunction_effect Q S (by decide) .parity (by decide) 0 (by decide) (by decide) mult3
    (fun v => by simp only [mult3, protoOf]; exact Rat.natCast_nonneg)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by rw [parity_total]; decide +kernel) (Or.inl (by decide +kernel))
  funext v
  simp only [inst, Inst.pure, val, he, parity_total]

/-- **Over-extension, and error**: every even number that is not a multiple
of 3 is, at some criterion, judged an even multiple of 3 and not a multiple
of 3. -/
theorem even_overExtends (n : Nat) (he : n % 2 = 0) (_h3 : n % 3 ≠ 0) :
    ∃ θ, OverExtendsBinary θ Q.K S evenMult3 mult3 (inst n) :=
  overExtends_binary_of_conjunctionEffect _ _ _ _ _ (even_more_typical n he)

/-- **14, worked**: typicality −41 and −16; membership .06 and .80. 14 is
not a multiple of 3. 9 is, and is a *multiple of 3* to degree .58. -/
theorem fourteen :
    typicality Q S mult3 (inst 14) = -41 ∧ typicality Q S evenMult3 (inst 14) = -16 ∧
      membership Q S mult3 (inst 14) = 81 / 1250 ∧
      membership Q S evenMult3 (inst 14) = 497 / 625 ∧
      14 % 3 ≠ 0 ∧ membership Q S mult3 (inst 9) = 721 / 1250 := by
  decide +kernel

end Concepts.Numbers
