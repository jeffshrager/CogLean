/-
What the combined model predicts with any memory in place of EPAM's net.

M2 is left open: `retrieve` says what a problem's code calls up, a stored
code or nothing, with probabilities. Every theorem here holds for any
retrieval, encoding, strengths, criterion, search length and backup, and
says which law of memory, if any, it needs. `Phenomena.lean` derives the
EPAM versions, with a discrimination net's retrieval.

The trial is an instance of CogLib's general composition,
`Cog.recognizeRetrieve` (recognize, then retrieve, else back up). The
theorems that don't mention digits are proved there, for any problems and
answers, and carried here by `prob_trialWith`.

With no law of memory:
* `columns_prob` (strategy nesting): the chance of using the columns is the
  average, over what the code calls up, of `1` (nothing) and `(1 - R_y)^n`
  (a stored `y`).
* `whole_prob`: the chance of a whole-problem answer with a property is the
  average, over the stored codes called up, of retrieval's chance of stating
  one.
* For a code that calls up a stored `y` for certain: `columns_prob_certain`,
  `whole_depends_only_on_route`, `confusion_gives_neighbours_answer`,
  `confident_errors`, `same_sum_confusion_harmless`,
  `commuted_confusion_harmless`.

With a law of memory:
* `confused_digit`, `near_miss_200`, `near_miss_20` need `AgreesOn`: what a
  code calls up agrees with it on the features of the digits concerned.
* `learning_preserves_trial` needs `StableRetrieval`: studying one problem
  leaves the retrieval of another, retrieved as itself for certain,
  unchanged.
-/

import MultiDigit.Postulates

namespace MD

open Cog Dist

/-- The column backup, as part of a trial, makes every outcome a column
outcome. -/
theorem prob_backup_part (backup : Problem → Dist Nat) (x : Problem) (e : Route × Nat → Bool) :
    prob (Dist.bind (backup x) fun r => Dist.pure (Route.columns, r)) e =
      prob (backup x) (fun r => e (.columns, r)) :=
  prob_bind_pure _ _ _

/-- The stored problem `q`'s associations are *sharp* at criterion `cc`: no
answer but `q`'s sum clears it. -/
def Sharp (str : Item → Nat → Rat) (cc : Rat) (y : Item) (q : Problem) : Prop :=
  ∀ a, above (str y) cc a = true → a = q.sum

theorem isWhole_eq : isWhole = wholeSuch (fun _ => true) := by
  funext o; simp [isWhole, wholeSuch]

namespace AnyMemory

variable (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
  (as : List Nat) (cc : Rat) (n : Nat) (backup : Problem → Dist Nat)

/-! ### The trial as an instance of `Cog.recognizeRetrieve`

The general theorems are proved once, in CogLib, for any problems and
answers (`CogLib/Process/RecognizeRetrieve.lean`). This trial is that
composition, with problem codes from the encoding, answers in `Nat`, the
column backup, and its own route names. `relabel` translates the routes, and
`prob_trialWith` carries every probability across. -/

/-- The generic routes, in this model's names. -/
def relabel : Cog.Route × Nat → Route × Nat
  | (.whole, a) => (.whole, a)
  | (.backup, a) => (.columns, a)

theorem prob_after (x : Problem) (r : Option Item) (e : Route × Nat → Bool) :
    prob (afterRetrieval str as cc n backup x r) e =
      prob (RR.afterRecognition str as cc n backup x r) (fun o => e (relabel o)) := by
  cases r with
  | none => simp only [afterRetrieval, RR.afterRecognition, prob_bind_pure]; rfl
  | some y =>
    simp only [afterRetrieval, RR.afterRecognition]
    rw [prob_bind_sum, prob_bind_sum]
    congr 1
    apply List.map_congr_left
    intro rp _
    obtain ⟨k, p⟩ := rp
    cases k <;> simp only [prob_pure, prob_bind_pure, relabel]

/-- **Every probability of this trial is a probability of the generic
composition**, with the routes relabelled. -/
theorem prob_trialWith (x : Problem) (e : Route × Nat → Bool) :
    prob (trialWith retrieve E str as cc n backup x) e =
      prob (recognizeRetrieve E.code retrieve str as cc n backup x) (fun o => e (relabel o)) := by
  unfold trialWith recognizeRetrieve
  rw [prob_bind_sum, prob_bind_sum]
  congr 1
  apply List.map_congr_left
  intro rp _
  rw [prob_after]

theorem isColumns_relabel : (fun o => isColumns (relabel o)) = RR.isBackup (A := Nat) := by
  funext o; obtain ⟨r, a⟩ := o; cases r <;> rfl

theorem isWhole_relabel : (fun o => isWhole (relabel o)) = RR.isWhole (A := Nat) := by
  funext o; obtain ⟨r, a⟩ := o; cases r <;> rfl

theorem wholeSuch_relabel (P : Nat → Bool) :
    (fun o => wholeSuch P (relabel o)) = RR.wholeSuch P := by
  funext o; obtain ⟨r, a⟩ := o; cases r <;> rfl

theorem wholeWrong_relabel (x : Problem) :
    (fun o => wholeWrong x (relabel o)) = RR.wholeWrong Problem.sum x := by
  funext o; obtain ⟨r, a⟩ := o; cases r <;> simp [wholeWrong, RR.wholeWrong, wholeSuch, RR.wholeSuch, relabel]

/-- The chance of the columns once `r` is called up. -/
abbrev columnsAfter : Option Item → Rat := RR.backupAfter str as cc n

/-- The chance of a whole-problem answer with property `P` once `r` is called
up. -/
abbrev wholeAfter (P : Nat → Bool) : Option Item → Rat := RR.wholeAfter str as cc n P

theorem prob_columns_after (x : Problem) (hb : mass (backup x) = 1)
    (hT : ∀ y, total as (str y) ≠ 0) (r : Option Item) :
    prob (afterRetrieval str as cc n backup x r) isColumns = columnsAfter str as cc n r := by
  rw [prob_after, isColumns_relabel]
  exact RR.prob_backup_after str as cc n backup x hb hT r

theorem prob_whole_after (x : Problem) (P : Nat → Bool) (r : Option Item) :
    prob (afterRetrieval str as cc n backup x r) (wholeSuch P) = wholeAfter str as cc n P r := by
  rw [prob_after, wholeSuch_relabel]
  exact RR.prob_whole_after str as cc n backup x P r

/-- **Strategy nesting, with any memory.** With a proper backup, the column
route is taken with the average chance, over what the code calls up, of `1`
when nothing is called up and `(1 - R_y)^n` when a stored `y` is. -/
theorem columns_prob (x : Problem) (hb : mass (backup x) = 1)
    (hT : ∀ y, total as (str y) ≠ 0) :
    prob (trialWith retrieve E str as cc n backup x) isColumns =
      ((retrieve (E.code x)).map fun rp => rp.2 * columnsAfter str as cc n rp.1).sum := by
  rw [prob_trialWith, isColumns_relabel]
  exact RR.backup_prob E.code retrieve str as cc n backup x hb hT

/-- **Whole-problem answers, with any memory**: the average, over the stored
codes called up, of retrieval's chance of stating such an answer. -/
theorem whole_prob (x : Problem) (P : Nat → Bool) :
    prob (trialWith retrieve E str as cc n backup x) (wholeSuch P) =
      ((retrieve (E.code x)).map fun rp => rp.2 * wholeAfter str as cc n P rp.1).sum := by
  rw [prob_trialWith, wholeSuch_relabel]
  exact RR.whole_prob E.code retrieve str as cc n backup x P

/-- A trial on a code that calls up `r` for certain. -/
theorem trialWith_certain (x : Problem) (r : Option Item) (h : retrieve (E.code x) = pure r) :
    trialWith retrieve E str as cc n backup x = afterRetrieval str as cc n backup x r := by
  unfold trialWith
  rw [h, bind_pure_left]

/-- **Strategy nesting, for a code that calls up `r` for certain.** -/
theorem columns_prob_certain (x : Problem) (r : Option Item) (h : retrieve (E.code x) = pure r)
    (hb : mass (backup x) = 1) (hT : ∀ y, total as (str y) ≠ 0) :
    prob (trialWith retrieve E str as cc n backup x) isColumns = columnsAfter str as cc n r := by
  rw [prob_trialWith, isColumns_relabel]
  exact RR.backup_prob_certain E.code retrieve str as cc n backup x r h hb hT

/-- **Whole-problem retrieval depends only on the route.** If `x` calls up
`y` for certain, whole-problem retrieval on `x` states an answer with
property `P` exactly as often as retrieval on `y`'s associations does. -/
theorem whole_depends_only_on_route (x : Problem) (y : Item) (P : Nat → Bool)
    (h : retrieve (E.code x) = pure (some y)) :
    prob (trialWith retrieve E str as cc n backup x) (wholeSuch P) =
      prob (search as (str y) cc 0 n) (Retrieval.statedSuch P) := by
  rw [prob_trialWith, wholeSuch_relabel]
  exact RR.whole_depends_only_on_route E.code retrieve str as cc n backup x y P h

/-- Two problems that call up the same stored problem for certain are
answered alike by whole-problem retrieval. -/
theorem same_route_same_retrieval (x x' : Problem) (y : Item) (P : Nat → Bool)
    (h : retrieve (E.code x) = pure (some y)) (h' : retrieve (E.code x') = pure (some y)) :
    prob (trialWith retrieve E str as cc n backup x) (wholeSuch P) =
      prob (trialWith retrieve E str as cc n backup x') (wholeSuch P) := by
  rw [prob_trialWith, prob_trialWith, wholeSuch_relabel]
  exact RR.same_route_same_retrieval E.code retrieve str as cc n backup x x' y P h h'

/-- **A confused problem gets its neighbour's answer.** If `x` calls up the
stored `code q` for certain, and `q`'s associations are sharp, then every
answer whole-problem retrieval gives to `x` is `q`'s sum. -/
theorem confusion_gives_neighbours_answer (x q : Problem) (hT : total as (str (E.code q)) ≠ 0)
    (h : retrieve (E.code x) = pure (some (E.code q))) (hs : Sharp str cc (E.code q) q) :
    prob (trialWith retrieve E str as cc n backup x) (wholeSuch fun a => a != q.sum) = 0 := by
  rw [prob_trialWith, wholeSuch_relabel]
  exact RR.confusion_gives_neighbours_answer E.code retrieve str as cc n backup Problem.sum x q hT h hs

/-- Retrieval on a sharp stored problem states a wrong answer for `x` exactly
as often as it states any answer, when `x`'s sum is not `q`'s. -/
theorem wrong_eq_whole_of_sharp (x q : Problem) (y : Item) (hT : total as (str y) ≠ 0)
    (h : retrieve (E.code x) = pure (some y)) (hs : Sharp str cc y q) (hne : x.sum ≠ q.sum) :
    prob (trialWith retrieve E str as cc n backup x) (wholeWrong x) =
      prob (trialWith retrieve E str as cc n backup x) isWhole := by
  rw [prob_trialWith, prob_trialWith, wholeWrong_relabel, isWhole_relabel]
  exact RR.wrong_eq_whole_of_sharp E.code retrieve str as cc n backup Problem.sum x y q.sum hT h hs hne

/-- **Confident errors, with any memory.** Let the stored `q` call up itself
for certain, with sharp associations, and let `x` (with a different sum)
call up `q` for certain. Then retrieval never errs on `q`, always errs on
`x`, and `x` falls back on the columns exactly as rarely as `q` does. The
general theorem is `Cog.RR.confident_errors`. -/
theorem confident_errors (x q : Problem) (hT : ∀ y, total as (str y) ≠ 0)
    (hbx : mass (backup x) = 1) (hbq : mass (backup q) = 1)
    (hq : retrieve (E.code q) = pure (some (E.code q)))
    (hx : retrieve (E.code x) = pure (some (E.code q)))
    (hs : Sharp str cc (E.code q) q) (hne : x.sum ≠ q.sum) :
    prob (trialWith retrieve E str as cc n backup q) (wholeWrong q) = 0 ∧
      prob (trialWith retrieve E str as cc n backup x) (wholeWrong x) =
        prob (trialWith retrieve E str as cc n backup x) isWhole ∧
      prob (trialWith retrieve E str as cc n backup x) isColumns =
        prob (trialWith retrieve E str as cc n backup q) isColumns := by
  simp only [prob_trialWith, wholeWrong_relabel, isWhole_relabel, isColumns_relabel]
  exact RR.confident_errors E.code retrieve str as cc n backup Problem.sum x q hT hbx hbq hq hx hs hne

/-- **Confusion with a problem of the same sum is harmless.** -/
theorem same_sum_confusion_harmless (x q : Problem)
    (hq : retrieve (E.code q) = pure (some (E.code q)))
    (hx : retrieve (E.code x) = pure (some (E.code q))) (hsum : x.sum = q.sum) :
    prob (trialWith retrieve E str as cc n backup x) (wholeWrong x) =
      prob (trialWith retrieve E str as cc n backup q) (wholeWrong q) := by
  rw [prob_trialWith, prob_trialWith, wholeWrong_relabel, wholeWrong_relabel]
  exact RR.same_correct_confusion_harmless E.code retrieve str as cc n backup Problem.sum x q hq hx hsum

/-- **Commuted confusions are harmless**: confusing `a + b` with `b + a`. -/
theorem commuted_confusion_harmless (x : Problem)
    (hq : retrieve (E.code x.swap) = pure (some (E.code x.swap)))
    (hx : retrieve (E.code x) = pure (some (E.code x.swap))) :
    prob (trialWith retrieve E str as cc n backup x) (wholeWrong x) =
      prob (trialWith retrieve E str as cc n backup x.swap) (wholeWrong x.swap) :=
  same_sum_confusion_harmless retrieve E str as cc n backup x x.swap hq hx
    (by simp [Problem.sum, Problem.swap, Nat.add_comm])

/-- A problem that can call up `q` has `q`'s digit wherever retrieval agrees
on all of that digit's features (`AgreesOn`). -/
theorem confused_digit (x q : Problem) (i : Addend) (j : Place)
    (hagree : Phenomena.AgreesOn retrieve (E.code x) (E.features i j))
    (hx : (retrieve (E.code x)).Possible (some (E.code q))) :
    x.digit i j = q.digit i j :=
  Phenomena.confusion_preserves_of retrieve E.code _ (fun p => p.digit i j)
    (fun p q => E.determines p q i j) x q hagree hx

/-- **Near misses: within 200, with any memory that agrees on the hundreds
digits.** -/
theorem near_miss_200 (x q : Problem)
    (hagree : ∀ i, Phenomena.AgreesOn retrieve (E.code x) (E.features i .hundreds))
    (hx : (retrieve (E.code x)).Possible (some (E.code q)))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    q.sum < x.sum + 200 ∧ x.sum < q.sum + 200 := by
  have h1 := confused_digit retrieve E x q .first .hundreds (hagree .first) hx
  have h2 := confused_digit retrieve E x q .second .hundreds (hagree .second) hx
  simp only [Problem.digit, Problem.addend, digitOf] at h1 h2
  simp only [Problem.sum]
  omega

/-- **Near misses: within 20**, when retrieval also agrees on the tens
digits. -/
theorem near_miss_20 (x q : Problem)
    (hagree : ∀ i, ∀ j, j ≠ Place.units → Phenomena.AgreesOn retrieve (E.code x) (E.features i j))
    (hx : (retrieve (E.code x)).Possible (some (E.code q)))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    q.sum < x.sum + 20 ∧ x.sum < q.sum + 20 := by
  have h1 := confused_digit retrieve E x q .first .hundreds (hagree .first _ (by decide)) hx
  have h2 := confused_digit retrieve E x q .second .hundreds (hagree .second _ (by decide)) hx
  have h3 := confused_digit retrieve E x q .first .tens (hagree .first _ (by decide)) hx
  have h4 := confused_digit retrieve E x q .second .tens (hagree .second _ (by decide)) hx
  simp only [Problem.digit, Problem.addend, digitOf] at h1 h2 h3 h4
  simp only [Problem.sum]
  omega

/-- **Practiced problems stay practiced, with any memory that has stable
retrieval.** Studying a code other than `q`'s never changes how `q`, which
calls up itself for certain, is answered. -/
theorem learning_preserves_trial {S : Type} (R : Retriever S Item)
    (hst : Phenomena.StableRetrieval R) (s : S) (q : Problem) (z : Item)
    (hq : R.retrieve s (E.code q) = pure (some (E.code q))) (hz : E.code q ≠ z) :
    trialWith (R.retrieve (R.study s z)) E str as cc n backup q =
      trialWith (R.retrieve s) E str as cc n backup q := by
  unfold trialWith
  rw [hst s z _ hq hz]

end AnyMemory
end MD
