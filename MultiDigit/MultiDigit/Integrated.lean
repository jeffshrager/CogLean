/-
The integrated model: every route computes its answer.

`Example.lean` checks the general theorems with a backup handed the correct
sum (`Dist.pure p.sum`). Here nothing is handed the sum. The model is a
composition of existing parts, with no new arithmetic:

1. **Recognition**: an EPAM discrimination net (`Cog.Net`, learned in
   `Example.net`).
2. **Whole-problem retrieval**: DOA sampling from the recognized problem's
   associations (`Cog.search`, inside `MD.trial`).
3. **Retrieval failure invokes the solver**: `MD.trial`'s backup slot is the
   column problem solver.
4. **Each column** is a single-digit DOA trial (`MD.doaFact`, wrapping
   `SC.trial`: retrieval, fingers, counting fingers).
5. **Carrying and column order** come from CogLib's decision cycle
   (`Cog.run`) over the problem space `Solver.space`, with the procedure
   `Solver.full`.

What each result rests on:

| Kind | Results |
|---|---|
| **Consequence of the composition** (every encoding, net, strength set and DOA parameter set) | `solverBackup_eq_columns`, `mass_solverBackup`, `whole_independent_of_solver`, `columnsSuch_prob`, `solver_error_is_doa_error` |
| **Conditional**, given the conditions named in its docstring | `integrated_confident_errors` (given confusion, sharp associations, proper DOA strengths), `errors_two_sources` (the same), `solver_exact_of_exact` (given exact facts, which DOA sampling does not supply) |
| **The illustrative setting** (chosen numbers) | `setting_*`, including `setting_actr_x` with ACT-R's memory in place of the net |

Conditions, and where they stand:
* *x is confused with q, and q recognized as itself*: a property of the net,
  here derived from EPAM learning (`Example.net_facts`, by evaluation).
* *Sharp associations for q*: an empirical premise still awaiting
  explanation (`notes/EXPLANATORY_AUDIT.md`).
* *Proper strengths* (positive totals): well-formedness, not a phenomenon.

No phenomenon is a hypothesis of any theorem here. Confident errors, and the
column route's own errors, are derived from the mechanisms under the
conditions above.

The illustrative setting reuses `Example`'s encoding, net, whole-problem
strengths, criterion 1/2 and search length 1. Every digit pair gets the same
single-digit associations: its sum 4/5, the next number in the counting
sequence 3/25, and every other answer from 0 to 19 1/100. The DOA criterion
is 1/10, the search length 1, the elaboration 1/20, and the skip and
double-count rates 1/20 (the `Sims` defaults). These are chosen, not
grounded in data (OPEN_ISSUES #18).

Where correct knowledge enters: only in the single-digit associations, which
are peaked on each pair's sum (the learner's single-digit facts, as in DOA),
and in the procedure's knowledge of carrying. No route is given a
multi-digit answer; 250 for 150 + 100 is assembled by the solver from three
DOA trials and a carry rule, and it is never certain.

Exact values are computed with merged distributions (`SC.trialMerged`,
`Dist.merge`), proved to be the same distributions (`same_fastBackup`), so
each value is a probability of the model itself.
-/

import MultiDigit.Example
import MultiDigit.ExampleACTR
import MultiDigit.Solver
import StrategyChoice.Exact

namespace MD.Integrated

open Cog Dist MD

/-- The single-digit DOA process's parameters: answers, associations per
digit pair, backup strategies, criterion and search length. -/
structure Facts where
  as : List Nat
  s : SC.Problem → Nat → Rat
  bk : SC.Backup
  cc : Rat
  n : Nat

/-- A column's addition: the single-digit DOA trial. -/
def Facts.fact (F : Facts) : Nat → Nat → Dist Nat := doaFact F.as F.s F.bk F.cc F.n

/-- **The solver backup**: the column problem solver, on CogLib's decision
cycle, adding each column by a DOA trial. -/
def solverBackup (F : Facts) (p : Problem) : Dist Nat :=
  Solver.answers F.fact Solver.full Solver.lenient p

/-- **An integrated trial**: recognize, retrieve the whole answer, and on
failure solve column by column. -/
def itrial (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat)
    (F : Facts) (x : Problem) : Dist (Route × Nat) :=
  trial E N str as cc n (solverBackup F) x

/-- Strengths with positive totals, plain and elaborated on the fingers. -/
def Facts.Proper (F : Facts) : Prop :=
  ∀ d e, total F.as (F.s ⟨d, e⟩) ≠ 0 ∧ total F.as (SC.elaborate (F.s ⟨d, e⟩) (d + e) F.bk.e) ≠ 0

/-! ### Consequences of the composition -/

/-- The solver answers as the column backup `columns` does, with DOA facts
(`Solver.bridge`). So every theorem about `columns` holds of the solver. -/
theorem solverBackup_eq_columns (F : Facts) (p : Problem) :
    solverBackup F p = columns F.fact p :=
  Solver.bridge _ p

/-- With proper strengths, the solver is a proper distribution of answers. -/
theorem mass_solverBackup (F : Facts) (hF : F.Proper) (p : Problem) : mass (solverBackup F p) = 1 := by
  rw [solverBackup_eq_columns]
  exact mass_columns _ (fun d e => mass_doaFact _ _ _ _ _ d e (hF d e).1 (hF d e).2) p

/-- **Whole-problem answers do not depend on the solver.** Once `x` is
recognized as `y`, the chance of a whole-problem answer with property `P` is
that of retrieval on `y`'s associations, whatever the backup. A better solver
cannot change a whole-problem error. -/
theorem whole_independent_of_solver (E : Encoding) (N : Net) (str : Item → Nat → Rat)
    (as : List Nat) (cc : Rat) (n : Nat) (F : Facts) (backup : Problem → Dist Nat)
    (x : Problem) (P : Nat → Bool) :
    prob (itrial E N str as cc n F x) (wholeSuch P) =
      prob (trial E N str as cc n backup x) (wholeSuch P) := by
  unfold itrial
  cases h : N.select (E.code x) with
  | none =>
    simp only [trial, h]
    rw [prob_bind_pure, prob_bind_pure]
    simp [wholeSuch, prob_false]
  | some y =>
    rw [whole_depends_only_on_route E N str as cc n _ x y P h,
      whole_depends_only_on_route E N str as cc n _ x y P h]

/-- A column-route answer with property `P`. -/
def columnsSuch (P : Nat → Bool) (o : Route × Nat) : Bool := o.1 == .columns && P o.2

/-- **The column route, factored.** When `x` is recognized as `y`, an answer
with property `P` comes by the column route with probability: the chance
that retrieval is exhausted, times the chance that the backup gives such an
answer. -/
theorem columnsSuch_prob (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat)
    (cc : Rat) (n : Nat) (backup : Problem → Dist Nat) (x : Problem) (y : Item) (P : Nat → Bool)
    (h : N.select (E.code x) = some y) (hT : total as (str y) ≠ 0) :
    prob (trial E N str as cc n backup x) (columnsSuch P) =
      (1 - reach as (str y) cc) ^ n * prob (backup x) P := by
  simp only [trial, h]
  rw [prob_bind_split _ _ _ (fun _ => false) Retrieval.isExhausted (prob (backup x) P)]
  · rw [prob_false, prob_exhausted as (str y) cc hT]; grind
  · intro r
    cases r with
    | stated a k => simp [prob_pure, columnsSuch, Retrieval.isExhausted]; grind
    | exhausted =>
      simp only [Retrieval.isExhausted]
      rw [prob_bind_pure]
      simp [columnsSuch]; grind

/-- **A solver error is a single-digit DOA error, moved to its place.** If two
columns' DOA trials are certain, the solver is wrong exactly as often as the
DOA trial on the third column's digits (`column_error_is_doa_error`, through
the bridge). -/
theorem solver_error_is_doa_error (F : Facts) (p : Problem) (ha : p.a < 1000) (hb : p.b < 1000)
    (j : Place) (hex : ∀ j', j' ≠ j → Exact F.fact (p.digit .first j') (p.digit .second j')) :
    prob (solverBackup F p) (fun ans => ans != p.sum) =
      prob (SC.trial F.as (F.s ⟨p.digit .first j, p.digit .second j⟩) F.bk F.cc F.n
        ⟨p.digit .first j, p.digit .second j⟩)
        (fun o => o.2 != p.digit .first j + p.digit .second j) := by
  rw [solverBackup_eq_columns]
  exact column_error_is_doa_error F.as F.s F.bk F.cc F.n p ha hb j hex

/-! ### Conditional results -/

/-- **Confident errors, with the solver as backup.** Given that the net
recognizes `q` as itself and confuses `x` with it, that `q`'s associations
are sharp, and that the DOA strengths are proper:
* whole-problem retrieval never errs on `q`;
* every whole-problem answer to `x` is wrong;
* the solver is used on `x` exactly as often as on `q`.
The general theorem (`MD.confident_errors`) with the computed backup. -/
theorem integrated_confident_errors (E : Encoding) (N : Net) (str : Item → Nat → Rat)
    (as : List Nat) (cc : Rat) (n : Nat) (F : Facts) (hF : F.Proper) (x q : Problem)
    (hT : ∀ y, total as (str y) ≠ 0)
    (hq : N.select (E.code q) = some (E.code q)) (hx : N.select (E.code x) = some (E.code q))
    (hs : Sharp str cc (E.code q) q) (hne : x.sum ≠ q.sum) :
    prob (itrial E N str as cc n F q) (wholeWrong q) = 0 ∧
      prob (itrial E N str as cc n F x) (wholeWrong x) =
        prob (itrial E N str as cc n F x) isWhole ∧
      prob (itrial E N str as cc n F x) isColumns =
        prob (itrial E N str as cc n F q) isColumns :=
  confident_errors E N str as cc n (solverBackup F) x q hT (mass_solverBackup F hF x)
    (mass_solverBackup F hF q) hq hx hs hne

/-- **Two sources of error on a confused problem.** Under the same conditions,
`x` is answered wrongly by whole-problem retrieval whenever that route is
taken, and wrongly by the column route with probability: the chance that
retrieval on `q`'s associations is exhausted, times the solver's own error
rate on `x`, which comes from the single-digit DOA trials. -/
theorem errors_two_sources (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat)
    (cc : Rat) (n : Nat) (F : Facts) (x q : Problem) (hT : ∀ y, total as (str y) ≠ 0)
    (hx : N.select (E.code x) = some (E.code q)) (hs : Sharp str cc (E.code q) q)
    (hne : x.sum ≠ q.sum) :
    prob (itrial E N str as cc n F x) (wholeWrong x) = prob (itrial E N str as cc n F x) isWhole ∧
      prob (itrial E N str as cc n F x) (columnsSuch fun a => a != x.sum) =
        (1 - reach as (str (E.code q)) cc) ^ n *
          prob (columns F.fact x) (fun a => a != x.sum) := by
  refine ⟨wrong_eq_whole_of_sharp E N str as cc n _ x q _ (hT _) hx hs hne, ?_⟩
  unfold itrial
  rw [columnsSuch_prob E N str as cc n _ x _ _ hx (hT _), solverBackup_eq_columns]

/-- Given exact single-digit facts in every column, the solver is exact. DOA
sampling does not supply this condition: its trials can err, so the column
route can err (see the setting below). -/
theorem solver_exact_of_exact (F : Facts) (p : Problem) (ha : p.a < 1000) (hb : p.b < 1000)
    (hex : ∀ j, Exact F.fact (p.digit .first j) (p.digit .second j)) :
    solverBackup F p = Dist.pure p.sum := by
  rw [solverBackup_eq_columns]
  exact columns_exact _ p ha hb (hex _) (hex _) (hex _)

/-! ### Exact evaluation

The same distributions, with equal outcomes merged, for computation. -/

/-- A column's DOA trial, merged. -/
def Facts.fastFact (F : Facts) (d e : Nat) : Dist Nat :=
  merge (Dist.bind (SC.trialMerged F.as (F.s ⟨d, e⟩) F.bk F.cc F.n ⟨d, e⟩) fun o => Dist.pure o.2)

/-- The solver's answers, merged. -/
def fastBackup (F : Facts) (p : Problem) : Dist Nat := merge (columns F.fastFact p)

theorem same_fastFact (F : Facts) (d e : Nat) : Same (F.fastFact d e) (F.fact d e) := by
  intro h
  rw [Facts.fastFact, same_merge]
  exact same_bind (SC.same_trialMerged _ _ _ _ _ _) (fun _ => Same.refl _) h

theorem same_fastBackup (F : Facts) (p : Problem) : Same (fastBackup F p) (solverBackup F p) := by
  intro h
  rw [fastBackup, same_merge, solverBackup_eq_columns]
  exact same_bind (same_fastFact F _ _) (fun _ => same_bind (same_fastFact F _ _) fun _ =>
    same_bind (same_fastFact F _ _) fun _ => Same.refl _) h

/-- A trial's probabilities depend on its backup only as a distribution. -/
theorem prob_trial_same (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat)
    (cc : Rat) (n : Nat) (b b' : Problem → Dist Nat) (x : Problem) (hb : Same (b x) (b' x))
    (e : Route × Nat → Bool) :
    prob (trial E N str as cc n b x) e = prob (trial E N str as cc n b' x) e := by
  apply Same.prob
  have hk : Same (Dist.bind (b x) fun r => Dist.pure (Route.columns, r))
      (Dist.bind (b' x) fun r => Dist.pure (Route.columns, r)) :=
    same_bind hb fun _ => Same.refl _
  unfold trial
  split
  · exact hk
  · exact same_bind (Same.refl _) fun r => by cases r <;> first | exact Same.refl _ | exact hk

/-- The same, for a trial with any memory. -/
theorem prob_trialWith_same (retrieve : Item → Dist (Option Item)) (E : Encoding)
    (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat) (b b' : Problem → Dist Nat)
    (x : Problem) (hb : Same (b x) (b' x)) (e : Route × Nat → Bool) :
    prob (trialWith retrieve E str as cc n b x) e = prob (trialWith retrieve E str as cc n b' x) e := by
  apply Same.prob
  have hk : Same (Dist.bind (b x) fun r => Dist.pure (Route.columns, r))
      (Dist.bind (b' x) fun r => Dist.pure (Route.columns, r)) :=
    same_bind hb fun _ => Same.refl _
  unfold trialWith
  refine same_bind (Same.refl _) fun r => ?_
  cases r with
  | none => exact hk
  | some y => exact same_bind (Same.refl _) fun o => by cases o <;> first | exact Same.refl _ | exact hk

theorem prob_itrial_fast (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat)
    (cc : Rat) (n : Nat) (F : Facts) (x : Problem) (e : Route × Nat → Bool) :
    prob (itrial E N str as cc n F x) e = prob (trial E N str as cc n (fastBackup F) x) e :=
  prob_trial_same E N str as cc n _ _ x (fun h => (same_fastBackup F x h).symm) e

/-! ### The illustrative setting -/

open Example

/-- Single-digit associations, the same rule for every digit pair: the sum
4/5, the next number counted 3/25, every other answer 1/100. -/
def colStr (p : SC.Problem) (a : Nat) : Rat :=
  if a = p.a + p.b then 4 / 5 else if a = p.a + p.b + 1 then 3 / 25 else 1 / 100

/-- The setting's DOA parameters. -/
def F0 : Facts := ⟨List.range 20, colStr, ⟨1 / 20, 1 / 20, 1 / 20⟩, 1 / 10, 1⟩

/-- The integrated trial in the setting. -/
abbrev it (p : Problem) : Dist (Route × Nat) := itrial bcd net str answers (1 / 2) 1 F0 p

theorem setting_mass : mass (solverBackup F0 x) = 1 ∧ mass (solverBackup F0 q1) = 1 := by
  rw [mass, mass, ← (same_fastBackup F0 x).prob, ← (same_fastBackup F0 q1).prob]
  decide +kernel

/-- **Confident errors in the setting**: the conditional theorem, its
conditions met by the net EPAM learned and the chosen strengths. -/
theorem setting_confident_errors :
    prob (it q1) (wholeWrong q1) = 0 ∧ prob (it x) (wholeWrong x) = prob (it x) isWhole ∧
      prob (it x) isColumns = prob (it q1) isColumns :=
  confident_errors bcd net str answers (1 / 2) 1 (solverBackup F0) x q1 total_ne setting_mass.1
    setting_mass.2 net_facts.2.1 net_facts.2.2.2 sharp_q1 (by decide)

/-- **150 + 100, recognized as 100 + 100.** Whole-problem retrieval answers 200
with probability 45/46, as with the given backup of `Example`; the solver is
invoked with probability 1/46. -/
theorem setting_routes :
    prob (it x) (wholeSuch (· == 200)) = 45 / 46 ∧ prob (it x) isColumns = 1 / 46 := by
  rw [whole_independent_of_solver bcd net str answers (1 / 2) 1 F0 backup x, prob_itrial_fast]
  decide +kernel

/-- **The solver on 150 + 100**: 250 with probability about .656. Its errors
are single-digit DOA errors in place: 260 (5 + 0 answered 6, about .099),
350 (1 + 1 answered 3, about .097), 251 (0 + 0 answered 1, about .095). -/
theorem setting_solver_x :
    prob (solverBackup F0 x) (· == 250) = 4991328328911197 / 7604375000000000 ∧
      prob (solverBackup F0 x) (· == 260) = 301333536893991 / 3041750000000000 ∧
      prob (solverBackup F0 x) (· == 350) = 491023435049232501 / 5060711562500000000 ∧
      prob (solverBackup F0 x) (· == 251) = 360329293149189 / 3802187500000000 := by
  simp only [← (same_fastBackup F0 x).prob]
  decide +kernel

/-- **150 + 100 overall**: answered 200 with probability about .978 (almost
all by whole-problem retrieval), and correctly, 250, only by the solver,
with probability (1/46) × the solver's .656. -/
theorem setting_overall_x :
    prob (it x) (fun o => o.2 == 200) = 1821856162746747614607 / 1862341855000000000000 ∧
      prob (it x) (fun o => o.2 == 250) = 4991328328911197 / 349801250000000000 := by
  simp only [prob_itrial_fast]
  decide +kernel

/-- **100 + 100 overall**: correct with probability about .993, by retrieval
(45/46) and by the solver (1/46 × about .664). -/
theorem setting_overall_q1 :
    prob (solverBackup F0 q1) (· == 200) = 12616212077 / 19010937500 ∧
      prob (it q1) (fun o => o.2 == 200) = 868108399577 / 874503125000 := by
  rw [← (same_fastBackup F0 q1).prob, prob_itrial_fast]
  decide +kernel

/-- **With ACT-R's memory in place of the net** (`ExampleACTR`): the same
application with one part swapped. 150 + 100 is answered 200 by retrieval
with probability 225/529, as before; it reaches the solver with probability
383/1058, and is answered correctly, 250, with probability 383/1058 × the
solver's .656, about .238. -/
theorem setting_actr_x :
    prob (trialWith ((actRetriever ExampleACTR.P).retrieve ExampleACTR.mem) bcd str answers (1 / 2) 1
        (solverBackup F0) x) (wholeSuch (· == 200)) = 225 / 529 ∧
      prob (trialWith ((actRetriever ExampleACTR.P).retrieve ExampleACTR.mem) bcd str answers (1 / 2) 1
        (solverBackup F0) x) isColumns = 383 / 1058 ∧
      prob (trialWith ((actRetriever ExampleACTR.P).retrieve ExampleACTR.mem) bcd str answers (1 / 2) 1
        (solverBackup F0) x) (fun o => o.2 == 250) = 1911678749972988451 / 8045428750000000000 := by
  simp only [prob_trialWith_same _ bcd str answers (1 / 2) 1 (solverBackup F0) (fastBackup F0) x
    (fun h => (same_fastBackup F0 x h).symm)]
  decide +kernel

end MD.Integrated
