/-
The worked case of `Example.lean`, with ACT-R's declarative memory in place
of EPAM's net: where the two memories predict differently.

Everything but M2 is as in `Example.lean`: the binary-coded encoding, the
associations (.90 on the correct sum, .01 elsewhere), criterion .50, search
length 1, and an exact backup. The memory studies 100 + 100 and then
100 + 200 (`Cog.actRetriever`, decay 1 and temperature 1). Partial matching
compares all 24 features, each mismatch halving a chunk's weight
(`μ = 1/2`), and the failure weight is `θ = 1/10`.

| | EPAM (`Example.lean`) | ACT-R (here) |
|---|---|---|
| 150 + 100 answered 200 (the neighbour's sum) | 45/46 | 225/529 |
| 150 + 100 answered 300 (a problem differing on a tested digit) | 0 | 225/1058 |
| 150 + 100 answered correctly (by the columns) | 1/46 | 383/1058 |
| errors on the practiced 100 + 100 | 0 | 225/782 |
| the same, after also studying 100 + 300 | 0 (Prediction 7) | 3375/5842 |

* Confusion is graded: 150 + 100 can retrieve either stored problem, the
  closer and more recent weighted more (`act_values`).
* No problem is retrieved for certain, not even a practiced one
  (`act_practiced_not_certain`), so the certain-retrieval predictions
  (2-5, 7) never apply.
* `AgreesOn` fails (`act_not_agreesOn`): 150 + 100 can retrieve 100 + 200,
  which differs from it on the second addend's hundreds digit.
* Practiced problems do not stay practiced (`act_interference`): studying
  100 + 300 raises the errors on 100 + 100.

The numbers are for illustration. The contrasts are what the memories
predict for every choice of them: EPAM's by the theorems of
`Phenomena.lean`, ACT-R's by `Act.retrieve_not_certain`.
-/

import MultiDigit.Example
import MultiDigit.AnyMemory

namespace MD.ExampleACTR

open Cog Dist MD MD.Example

/-- Partial matching over all 24 features, `μ = 1/2`, `θ = 1/10`. -/
def P : ActParams := ⟨List.range 24, 1 / 2, 1 / 10⟩

/-- Memory after studying 100 + 100 and then 100 + 200. -/
def mem : ActState := Act.study (Act.study ⟨0, []⟩ (bcd.code q1)) (bcd.code q2)

/-- A further problem to study. -/
def z : Problem := ⟨100, 300⟩

/-- A trial with ACT-R's memory in state `s`. -/
def actTrial (s : ActState) (p : Problem) : Dist (Route × Nat) :=
  trialWith ((actRetriever P).retrieve s) bcd str answers (1 / 2) 1 backup p

/-- **Graded confusion.** 150 + 100 retrieves 100 + 100 with probability
10/23 and 100 + 200 with probability 5/23, and fails with probability 8/23.
It is answered 200 with probability 225/529, 300 with probability 225/1058,
and correctly with probability 383/1058. -/
theorem act_values :
    prob ((actRetriever P).retrieve mem (bcd.code x)) (· == some (bcd.code q1)) = 10 / 23 ∧
      prob ((actRetriever P).retrieve mem (bcd.code x)) (· == some (bcd.code q2)) = 5 / 23 ∧
      prob (actTrial mem x) (wholeSuch (· == 200)) = 225 / 529 ∧
      prob (actTrial mem x) (wholeSuch (· == 300)) = 225 / 1058 ∧
      prob (actTrial mem x) (fun o => o.2 == 250) = 383 / 1058 := by
  decide +kernel

/-- **Not even a practiced problem is retrieved for certain**: 100 + 100
retrieves itself with probability 10/17, and is answered wrongly with
probability 225/782. -/
theorem act_practiced_not_certain :
    prob ((actRetriever P).retrieve mem (bcd.code q1)) (· == some (bcd.code q1)) = 10 / 17 ∧
      prob (actTrial mem q1) (wholeWrong q1) = 225 / 782 := by
  decide +kernel

/-- **`AgreesOn` fails.** 150 + 100 can retrieve 100 + 200, which differs from
it on the second addend's hundreds digit. -/
theorem act_not_agreesOn :
    ¬ Phenomena.AgreesOn ((actRetriever P).retrieve mem) (bcd.code x)
      (bcd.features .second .hundreds) := by
  intro h
  have hpos : ((actRetriever P).retrieve mem (bcd.code x)).Possible (some (bcd.code q2)) :=
    ⟨5 / 23, by decide +kernel, by decide +kernel⟩
  have := h _ hpos (featIdx .second .hundreds 0) (by decide)
  revert this
  decide +kernel

/-- **Interference.** Studying 100 + 300 raises the errors on the practiced
100 + 100 from 225/782 to 3375/5842. EPAM's net predicts no change
(`learning_preserves_trial`). -/
theorem act_interference :
    prob (actTrial mem q1) (wholeWrong q1) = 225 / 782 ∧
      prob (actTrial ((actRetriever P).study mem (bcd.code z)) q1) (wholeWrong q1) =
        3375 / 5842 := by
  decide +kernel

/-- The column-use prediction for any memory applies: here it is the average,
over what 150 + 100 retrieves, of 1 (failure) and `1 - R` (a stored
problem, `R` = 45/46). -/
theorem act_columns :
    prob (actTrial mem x) isColumns =
      (((actRetriever P).retrieve mem (bcd.code x)).map fun rp =>
        rp.2 * AnyMemory.columnsAfter str answers (1 / 2) 1 rp.1).sum :=
  AnyMemory.columns_prob _ bcd str answers (1 / 2) 1 backup x (mass_backup x) total_ne

end MD.ExampleACTR
