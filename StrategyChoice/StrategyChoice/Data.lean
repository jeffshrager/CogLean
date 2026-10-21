/-
Associative strengths for six problems, and what the model predicts from
them.

The strengths are rows of the chapter's Fig. 9.2A (p. 241): the proportion of
trials on which 4-year-olds gave each answer when told not to use their
fingers or count (p. 239, fn. 3). These six rows are reproduced in the ACT-R
tutorial (unit 5, `siegler.lisp`, `*siegler-data*`), which fits them with a
different theory; the full 25-problem matrix is not yet transcribed. Columns
are the answers 0 to 8 and "other" (here `99`, never a correct answer).

The predictions use the chapter's closed form (p. 250), over its twelve
confidence criteria and search lengths 1 to 6 (p. 250). They are computed
exactly, and `analysis/closed_form.py` computes the same numbers.
-/

import StrategyChoice.Phenomena

namespace SC.Data

open Cog SC

/-- The answers of Fig. 9.2A's columns; `99` is "other". -/
def answers : List Answer := [0, 1, 2, 3, 4, 5, 6, 7, 8, 99]

/-- A row of strengths, in hundredths, as a strength function. -/
def row (ws : List Nat) (a : Answer) : Rat :=
  match (answers.zip ws).find? (fun x => x.1 == a) with
  | some (_, w) => (w : Rat) / 100
  | none => 0

def s11 := row [0, 5, 86, 0, 2, 0, 2, 0, 0, 6]
def s12 := row [0, 4, 7, 75, 4, 0, 2, 0, 0, 9]
def s13 := row [0, 2, 0, 10, 75, 5, 1, 3, 0, 6]
def s22 := row [2, 0, 4, 5, 80, 4, 0, 5, 0, 0]
def s23 := row [0, 0, 7, 9, 25, 45, 8, 1, 1, 6]
def s33 := row [4, 0, 0, 5, 21, 9, 48, 0, 2, 11]

/-- Predicted overt strategy use, averaged over the twelve criteria and the
search lengths 1 to 6. -/
def meanOvertAll (s : Answer → Rat) : Rat :=
  ([1, 2, 3, 4, 5, 6].map (meanOvert answers s)).foldl (· + ·) 0 / 6

/-- **Predicted overt strategy use, by problem**: least on 1+1, then 2+2,
1+2, 1+3, 3+3, and most on 2+3. Peaks: .86, .80, .75, .75, .48, .45; the two
flattest distributions are the two that most often send the child to her
fingers. -/
theorem predicted_overt_order :
    meanOvertAll s11 < meanOvertAll s22 ∧ meanOvertAll s22 < meanOvertAll s12 ∧
      meanOvertAll s12 < meanOvertAll s13 ∧ meanOvertAll s13 < meanOvertAll s33 ∧
      meanOvertAll s33 < meanOvertAll s23 := by
  decide +kernel

/-- The predicted values exactly, as `analysis/closed_form.py` computes them. -/
theorem predicted_overt_values :
    meanOvertAll s11 = 2418068001407 / 12738241807212 ∧
      meanOvertAll s12 = 923629402424 / 3184560451803 ∧
      meanOvertAll s13 = 23649284852287 / 81083694187008 ∧
      meanOvertAll s22 = 8789 / 31250 ∧
      meanOvertAll s23 = 1319806163587 / 2384814534912 ∧
      meanOvertAll s33 = 13131720963317 / 24000000000000 := by
  decide +kernel

/-- **On 2+2, retrieval never errs**: at every one of the twelve criteria, no
wrong answer's strength exceeds the criterion while the correct one's does
(.80; the largest wrong strength is .05, not above the lowest criterion). -/
theorem retrieval_never_errs_2_2 :
    criteria.all (fun cc => aboveShare answers s22 cc (fun a => a != 4) == 0) = true := by
  decide +kernel

/-- On 2+3, retrieval at the lowest criterion errs more often than not: the
wrong answers hold 11/20 of the strength above .05 (.55 of the 1.00 there). -/
theorem retrieval_errs_2_3 : aboveShare answers s23 (5/100) (fun a => a != 5) = 11 / 20 := by
  decide +kernel

end SC.Data
