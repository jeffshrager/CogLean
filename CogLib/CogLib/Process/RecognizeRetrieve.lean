/-
Processes: recognize, then retrieve, else back up.

A composition of two mechanisms, over any problem type `P` and answer type
`A`:
1. **Recognition**, by any memory: a problem's code calls up a stored code,
   or nothing, with probabilities (`retrieve`).
2. **Associative retrieval** on the recognized code's associations: sample
   answers in proportion to strength, state one that clears the criterion,
   and give up after `n` searches (`search`, after the
   distributions-of-associations model).
3. **A backup**, when nothing is recognized or retrieval is exhausted.

The theorems hold for every memory, encoding, strengths, criterion, search
length and backup. Multi-digit addition is one instance
(`MultiDigit/AnyMemory.lean`); any task with problems, a familiar set and a
backup is another.

With no law of memory:
* `backup_prob`, `whole_prob`: backup use, and whole-problem answers with a
  property, are averages over what the code calls up.
* For a code that calls up a stored `y` for certain:
  - `backup_prob_certain`: backup is used with probability `(1 - R_y)^n`;
  - `whole_depends_only_on_route`, `same_route_same_retrieval`;
  - `confusion_gives_neighbours_answer`, `wrong_eq_whole_of_sharp`;
  - `confident_errors`: a problem confused with a familiar one, whose
    associations are sharp, errs on every whole-problem answer, with no more
    backup use than the familiar problem;
  - `same_correct_confusion_harmless`.

From laws of memory (`Phenomena/RetrievalLaws`):
* `confident_errors_of_laws`: any memory with determinate retrieval,
  certainty and stability produces confident errors whenever a stranger can
  be taken for a studied item with sharp associations.
-/

import CogLib.Process.SampledRetrieval
import CogLib.Phenomena.RetrievalLaws

namespace Cog

open Dist

/-- The route by which an answer was reached. -/
inductive Route where
  | whole
  | backup
  deriving Repr, DecidableEq

@[simp] theorem Route.whole_beq_whole : (Route.whole == Route.whole) = true := rfl
@[simp] theorem Route.backup_beq_backup : (Route.backup == Route.backup) = true := rfl
@[simp] theorem Route.whole_beq_backup : (Route.whole == Route.backup) = false := rfl
@[simp] theorem Route.backup_beq_whole : (Route.backup == Route.whole) = false := rfl

namespace RR

variable {P A : Type}

/-- The backup was used. -/
def isBackup (o : Route × A) : Bool := o.1 == .backup

/-- A whole-problem answer was stated. -/
def isWhole (o : Route × A) : Bool := o.1 == .whole

/-- A whole-problem answer with property `Q` was stated. -/
def wholeSuch (Q : A → Bool) (o : Route × A) : Bool := o.1 == .whole && Q o.2

/-- A wrong whole-problem answer to `x`. -/
def wholeWrong [DecidableEq A] (correct : P → A) (x : P) : Route × A → Bool :=
  wholeSuch fun a => a != correct x

/-- The associations of `y` are *sharp* at criterion `cc`: no answer but `c`
clears it. -/
def Sharp (str : Item → A → Rat) (cc : Rat) (y : Item) (c : A) : Prop :=
  ∀ a, above (str y) cc a = true → a = c

theorem isWhole_eq : (isWhole : Route × A → Bool) = wholeSuch (fun _ => true) := by
  funext o; simp [isWhole, wholeSuch]

/-- What follows recognition: retrieval on the stored code called up, with the
backup when it is exhausted, or when nothing is called up. -/
def afterRecognition (str : Item → A → Rat) (as : List A) (cc : Rat) (n : Nat)
    (backup : P → Dist A) (x : P) : Option Item → Dist (Route × A)
  | none => Dist.bind (backup x) fun r => Dist.pure (.backup, r)
  | some y => Dist.bind (search as (str y) cc 0 n) fun
      | .stated a _ => Dist.pure (.whole, a)
      | .exhausted => Dist.bind (backup x) fun r => Dist.pure (.backup, r)

end RR

/-- **Recognize, then retrieve, else back up.** -/
def recognizeRetrieve {P A : Type} (code : P → Item) (retrieve : Item → Dist (Option Item))
    (str : Item → A → Rat) (as : List A) (cc : Rat) (n : Nat) (backup : P → Dist A) (x : P) :
    Dist (Route × A) :=
  Dist.bind (retrieve (code x)) (RR.afterRecognition str as cc n backup x)

namespace RR

variable {P A : Type} [DecidableEq A] (code : P → Item) (retrieve : Item → Dist (Option Item))
  (str : Item → A → Rat) (as : List A) (cc : Rat) (n : Nat) (backup : P → Dist A)

/-- The backup, as part of a trial, makes every outcome a backup outcome. -/
theorem prob_backup_part (x : P) (e : Route × A → Bool) :
    prob (Dist.bind (backup x) fun r => Dist.pure (Route.backup, r)) e =
      prob (backup x) (fun r => e (.backup, r)) :=
  prob_bind_pure _ _ _

/-- The chance of the backup once `r` is called up. -/
def backupAfter : Option Item → Rat
  | none => 1
  | some y => (1 - reach as (str y) cc) ^ n

/-- The chance of a whole-problem answer with property `Q` once `r` is called
up. -/
def wholeAfter (Q : A → Bool) : Option Item → Rat
  | none => 0
  | some y => prob (search as (str y) cc 0 n) (Retrieval.statedSuch Q)

theorem prob_backup_after (x : P) (hb : mass (backup x) = 1)
    (hT : ∀ y, total as (str y) ≠ 0) (r : Option Item) :
    prob (afterRecognition str as cc n backup x r) isBackup = backupAfter str as cc n r := by
  cases r with
  | none =>
    simp only [afterRecognition, backupAfter]
    rw [prob_backup_part]
    simpa [isBackup, mass] using hb
  | some y =>
    simp only [afterRecognition, backupAfter]
    rw [prob_bind_split _ _ _ (fun _ => false) Retrieval.isExhausted 1]
    · rw [prob_false, prob_exhausted as (str y) cc (hT y)]; grind
    · intro r
      cases r with
      | stated a k => simp [prob_pure, isBackup, Retrieval.isExhausted]; grind
      | exhausted =>
        simp only [Retrieval.isExhausted]
        rw [prob_backup_part]
        simp only [isBackup, Route.backup_beq_backup, mass] at hb ⊢
        rw [hb]; grind

theorem prob_whole_after (x : P) (Q : A → Bool) (r : Option Item) :
    prob (afterRecognition str as cc n backup x r) (wholeSuch Q) = wholeAfter str as cc n Q r := by
  cases r with
  | none =>
    simp only [afterRecognition, wholeAfter]
    rw [prob_backup_part]
    simp only [wholeSuch, Route.backup_beq_whole, Bool.false_and]
    exact prob_false _
  | some y =>
    simp only [afterRecognition, wholeAfter]
    rw [prob_bind_split _ _ _ (Retrieval.statedSuch Q) (fun _ => false) 0]
    · rw [prob_false]; grind
    · intro r
      cases r with
      | stated a k =>
        by_cases hp : Q a <;> simp [prob_pure, wholeSuch, Retrieval.statedSuch, hp] <;> grind
      | exhausted =>
        simp only [Retrieval.statedSuch]
        rw [prob_backup_part]
        simp only [wholeSuch, Route.backup_beq_whole, Bool.false_and]
        rw [prob_false]; grind

/-- **Backup use, with any memory**: the average, over what the code calls up,
of `1` (nothing) and `(1 - R_y)^n` (a stored `y`). -/
theorem backup_prob (x : P) (hb : mass (backup x) = 1) (hT : ∀ y, total as (str y) ≠ 0) :
    prob (recognizeRetrieve code retrieve str as cc n backup x) isBackup =
      ((retrieve (code x)).map fun rp => rp.2 * backupAfter str as cc n rp.1).sum := by
  unfold recognizeRetrieve
  rw [prob_bind_sum]
  simp only [prob_backup_after str as cc n backup x hb hT]

/-- **Whole-problem answers, with any memory**: the average, over the stored
codes called up, of retrieval's chance of stating such an answer. -/
theorem whole_prob (x : P) (Q : A → Bool) :
    prob (recognizeRetrieve code retrieve str as cc n backup x) (wholeSuch Q) =
      ((retrieve (code x)).map fun rp => rp.2 * wholeAfter str as cc n Q rp.1).sum := by
  unfold recognizeRetrieve
  rw [prob_bind_sum]
  simp only [prob_whole_after str as cc n backup x Q]

/-- A trial on a code that calls up `r` for certain. -/
theorem recognizeRetrieve_certain (x : P) (r : Option Item) (h : retrieve (code x) = pure r) :
    recognizeRetrieve code retrieve str as cc n backup x = afterRecognition str as cc n backup x r := by
  unfold recognizeRetrieve
  rw [h, bind_pure_left]

/-- **Strategy nesting, for a code that calls up `r` for certain.** -/
theorem backup_prob_certain (x : P) (r : Option Item) (h : retrieve (code x) = pure r)
    (hb : mass (backup x) = 1) (hT : ∀ y, total as (str y) ≠ 0) :
    prob (recognizeRetrieve code retrieve str as cc n backup x) isBackup =
      backupAfter str as cc n r := by
  rw [recognizeRetrieve_certain code retrieve str as cc n backup x r h]
  exact prob_backup_after str as cc n backup x hb hT r

/-- **Whole-problem retrieval depends only on the route.** -/
theorem whole_depends_only_on_route (x : P) (y : Item) (Q : A → Bool)
    (h : retrieve (code x) = pure (some y)) :
    prob (recognizeRetrieve code retrieve str as cc n backup x) (wholeSuch Q) =
      prob (search as (str y) cc 0 n) (Retrieval.statedSuch Q) := by
  rw [recognizeRetrieve_certain code retrieve str as cc n backup x _ h]
  exact prob_whole_after str as cc n backup x Q (some y)

/-- Two problems that call up the same stored code for certain are answered
alike by whole-problem retrieval. -/
theorem same_route_same_retrieval (x x' : P) (y : Item) (Q : A → Bool)
    (h : retrieve (code x) = pure (some y)) (h' : retrieve (code x') = pure (some y)) :
    prob (recognizeRetrieve code retrieve str as cc n backup x) (wholeSuch Q) =
      prob (recognizeRetrieve code retrieve str as cc n backup x') (wholeSuch Q) := by
  rw [whole_depends_only_on_route code retrieve str as cc n backup x y Q h,
    whole_depends_only_on_route code retrieve str as cc n backup x' y Q h']

/-- **A confused problem gets its neighbour's answer.** -/
theorem confusion_gives_neighbours_answer (correct : P → A) (x q : P)
    (hT : total as (str (code q)) ≠ 0) (h : retrieve (code x) = pure (some (code q)))
    (hs : Sharp str cc (code q) (correct q)) :
    prob (recognizeRetrieve code retrieve str as cc n backup x)
      (wholeSuch fun a => a != correct q) = 0 := by
  rw [whole_depends_only_on_route code retrieve str as cc n backup x _ _ h,
    prob_stated _ _ _ _ hT]
  have : reachSuch as (str (code q)) cc (fun a => a != correct q) = 0 := by
    simp only [reachSuch]
    rw [prob_congr _ _ (fun _ => false), prob_false]
    intro a
    by_cases ha : above (str (code q)) cc a
    · simp [hs a ha]
    · simp [ha]
  rw [this]; grind

/-- Retrieval on sharp associations states a wrong answer for `x` exactly as
often as it states any answer, when `x`'s correct answer is not `c`. -/
theorem wrong_eq_whole_of_sharp (correct : P → A) (x : P) (y : Item) (c : A)
    (hT : total as (str y) ≠ 0) (h : retrieve (code x) = pure (some y)) (hs : Sharp str cc y c)
    (hne : correct x ≠ c) :
    prob (recognizeRetrieve code retrieve str as cc n backup x) (wholeWrong correct x) =
      prob (recognizeRetrieve code retrieve str as cc n backup x) isWhole := by
  rw [wholeWrong, isWhole_eq, whole_depends_only_on_route code retrieve str as cc n backup x y _ h,
    whole_depends_only_on_route code retrieve str as cc n backup x y _ h,
    prob_stated _ _ _ _ hT, prob_stated _ _ _ _ hT]
  congr 1
  simp only [reachSuch]
  apply prob_congr
  intro a
  by_cases ha : above (str y) cc a
  · have := hs a ha
    simp [this, Ne.symm hne]
  · simp [ha]

/-- **Confident errors, with any memory.** Let the familiar `q` call up itself
for certain, with sharp associations, and let `x`, whose correct answer
differs, call up `q` for certain. Then retrieval never errs on `q`, always
errs on `x`, and `x` falls back on the backup exactly as rarely as `q` does. -/
theorem confident_errors (correct : P → A) (x q : P) (hT : ∀ y, total as (str y) ≠ 0)
    (hbx : mass (backup x) = 1) (hbq : mass (backup q) = 1)
    (hq : retrieve (code q) = pure (some (code q)))
    (hx : retrieve (code x) = pure (some (code q)))
    (hs : Sharp str cc (code q) (correct q)) (hne : correct x ≠ correct q) :
    prob (recognizeRetrieve code retrieve str as cc n backup q) (wholeWrong correct q) = 0 ∧
      prob (recognizeRetrieve code retrieve str as cc n backup x) (wholeWrong correct x) =
        prob (recognizeRetrieve code retrieve str as cc n backup x) isWhole ∧
      prob (recognizeRetrieve code retrieve str as cc n backup x) isBackup =
        prob (recognizeRetrieve code retrieve str as cc n backup q) isBackup := by
  refine ⟨confusion_gives_neighbours_answer code retrieve str as cc n backup correct q q (hT _) hq hs,
    wrong_eq_whole_of_sharp code retrieve str as cc n backup correct x _ _ (hT _) hx hs hne, ?_⟩
  rw [backup_prob_certain code retrieve str as cc n backup x _ hx hbx hT,
    backup_prob_certain code retrieve str as cc n backup q _ hq hbq hT]

/-- **Confusion with a problem of the same correct answer is harmless.** -/
theorem same_correct_confusion_harmless (correct : P → A) (x q : P)
    (hq : retrieve (code q) = pure (some (code q)))
    (hx : retrieve (code x) = pure (some (code q))) (hsum : correct x = correct q) :
    prob (recognizeRetrieve code retrieve str as cc n backup x) (wholeWrong correct x) =
      prob (recognizeRetrieve code retrieve str as cc n backup q) (wholeWrong correct q) := by
  rw [wholeWrong, wholeWrong, hsum]
  exact same_route_same_retrieval code retrieve str as cc n backup x q _ _ hx hq

/-- **Confident errors, from laws of memory.** For any memory with
determinate retrieval, certainty and stability: after a study list without
repeats, if a stranger `x` can be taken for a studied `q` (with positive
probability), and `q`'s associations are sharp, then `confident_errors`
holds. The matrix (`CogMatrix/`) says which memory families have the three
laws. -/
theorem confident_errors_of_laws {S : Type} (R : Retriever S Item) (s0 : S) (U : List Item)
    (hdet : Laws.Determinate R s0 U) (hcert : Laws.Certainty R s0 U)
    (hstab : Laws.Stability R s0 U) (xs : List Item) (hxs : ∀ y ∈ xs, y ∈ U) (hnd : xs.Nodup)
    (correct : P → A) (x q : P) (hq : code q ∈ xs)
    (hconf : 0 < Laws.pRet R (R.studyAll s0 xs) (code x) (code q))
    (hT : ∀ y, total as (str y) ≠ 0) (hbx : mass (backup x) = 1) (hbq : mass (backup q) = 1)
    (hs : Sharp str cc (code q) (correct q)) (hne : correct x ≠ correct q) :
    prob (recognizeRetrieve code (R.retrieve (R.studyAll s0 xs)) str as cc n backup q)
        (wholeWrong correct q) = 0 ∧
      prob (recognizeRetrieve code (R.retrieve (R.studyAll s0 xs)) str as cc n backup x)
          (wholeWrong correct x) =
        prob (recognizeRetrieve code (R.retrieve (R.studyAll s0 xs)) str as cc n backup x)
          isWhole ∧
      prob (recognizeRetrieve code (R.retrieve (R.studyAll s0 xs)) str as cc n backup x)
          isBackup =
        prob (recognizeRetrieve code (R.retrieve (R.studyAll s0 xs)) str as cc n backup q)
          isBackup := by
  have hr : Laws.Reachable R s0 U (R.studyAll s0 xs) := ⟨xs, hxs, rfl⟩
  have hq' := Laws.retrieve_of_pRet_one R s0 U hdet _ hr (code q) (code q)
    (Laws.studied_selfRetrieval R s0 U hcert hstab xs hxs hnd (code q) hq)
  have hx' := Laws.retrieve_of_pRet_pos R s0 U hdet _ hr (code x) (code q) hconf
  exact confident_errors code _ str as cc n backup correct x q hT hbx hbq hq' hx' hs hne

end RR
end Cog
