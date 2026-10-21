/-
The phenomena the distributions-of-associations model explains, as
consequences of its postulates.

The chapter's central claim is that errors, solution times and overt
strategy use "are all functions of a single variable: the distribution of
associations between problems and potential answers" (p. 238). The theorems
below make that precise for one trial, with a given confidence criterion and
search length, and find its limits.

* `retrieval_prob`: retrieval is used with probability `1 - (1 - R)^n`,
  the chapter's `(1 - R)^N` for overt strategy use (p. 250).
* `retrieval_error_share`: among retrieval trials, the share of errors is
  the wrong answers' share of the strength above the criterion, for every
  search length (p. 250's equation has no `N` in it).
* `retrieval_independent_of_backup`: neither depends on the backup
  strategies.
* `counting_error_share`: among counting trials, the share of errors is the
  counting process's error rate on the sum, whatever the associations: the
  chapter's "nonintuitive prediction" (p. 245).
* `peaking_lowers_retrieval_errors`: moving strength to the correct answer
  never raises the error share among retrieval trials, at any criterion.
* `correct_strengthening_lowers_errors`: learning from a correct answer
  (A6), however it was reached, never raises the error share on retrieval
  trials.
* `peaking_can_raise_overt_use`: but making a distribution more peaked can
  *raise* overt strategy use, even averaged over the chapter's twelve
  confidence criteria. "A peaked distribution results in less frequent use
  of overt strategies" (p. 245) needs a condition the chapter doesn't state.
-/

import StrategyChoice.Postulates

namespace SC

open Cog Dist

/-- The backup strategies never count as retrieval, nor state a retrieval
error. -/
theorem prob_backup_zero (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat)
    (p : Problem) (e : Strategy × Answer → Bool)
    (hf : ∀ a, e (.fingers, a) = false) (hc : ∀ a, e (.countingFingers, a) = false) :
    prob (backup as s bk cc p) e = 0 := by
  unfold backup
  rw [prob_bind_split _ _ _ (fun _ => false) (fun _ => false) 0]
  · rw [prob_false]; grind
  · intro a
    split
    · simp [prob_pure, hf] <;> grind
    · rw [prob_bind_split _ _ _ (fun _ => false) (fun _ => false) 0]
      · rw [prob_false]; simp <;> grind
      · intro r; simp [prob_pure, hc] <;> grind

/-- Retrieval-trial events: the probability of an event that holds only on
retrieval trials with answers in `P` is that of retrieval stating an answer
in `P`. -/
theorem prob_trial_retrieval (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat)
    (n : Nat) (p : Problem) (e : Strategy × Answer → Bool) (P : Answer → Bool)
    (hr : ∀ a, e (.retrieval, a) = P a)
    (hf : ∀ a, e (.fingers, a) = false) (hc : ∀ a, e (.countingFingers, a) = false) :
    prob (trial as s bk cc n p) e = prob (search as s cc 0 n) (Retrieval.statedSuch P) := by
  unfold trial
  rw [prob_bind_split _ _ _ (Retrieval.statedSuch P) (fun _ => false) 0]
  · rw [prob_false]; grind
  · intro r
    cases r with
    | stated a k => by_cases h : P a <;> simp [prob_pure, hr, h, Retrieval.statedSuch] <;> grind
    | exhausted => simp [prob_backup_zero as s bk cc p e hf hc, Retrieval.statedSuch] <;> grind

/-- **Retrieval is used with probability `1 - (1 - R)^n`** (p. 250: overt
strategies with probability `(1 - R)^N`). -/
theorem retrieval_prob (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat) (n : Nat)
    (p : Problem) (hT : total as s ≠ 0) :
    prob (trial as s bk cc n p) isRetrieval = 1 - (1 - reach as s cc) ^ n := by
  rw [prob_trial_retrieval as s bk cc n p isRetrieval (fun _ => true)
    (by intro a; rfl) (by intro a; rfl) (by intro a; rfl)]
  rw [prob_stated as s cc _ hT]
  have : reachSuch as s cc (fun _ => true) = reach as s cc := by
    simp only [reachSuch, reach, Bool.and_true]
  rw [this, reach_mul_geom]

/-- Retrieval errors: the probability of stating a wrong answer by
retrieval. -/
theorem retrievalWrong_prob (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat)
    (n : Nat) (p : Problem) (hT : total as s ≠ 0) :
    prob (trial as s bk cc n p) (retrievalWrong p) =
      reachSuch as s cc (fun a => a != p.sum) * geom (1 - reach as s cc) n := by
  rw [prob_trial_retrieval as s bk cc n p (retrievalWrong p) (fun a => a != p.sum)
    (by intro a; simp [retrievalWrong]) (by intro a; simp [retrievalWrong])
    (by intro a; simp [retrievalWrong])]
  exact prob_stated as s cc _ hT n 0

/-- **The error share on retrieval trials** is the wrong answers' share of
the strength above the criterion, whatever the search length. -/
theorem retrieval_error_share (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat)
    (n : Nat) (p : Problem) (hT : total as s ≠ 0) (hA : strengthIn as s (above s cc) ≠ 0) :
    prob (trial as s bk cc n p) (retrievalWrong p) =
      prob (trial as s bk cc n p) isRetrieval * aboveShare as s cc (fun a => a != p.sum) := by
  rw [retrievalWrong_prob as s bk cc n p hT, retrieval_prob as s bk cc n p hT,
    ← reach_mul_geom, ← reachSuch_div_reach as s cc _ hT hA]
  have hR : reach as s cc ≠ 0 := by
    simp only [reach, prob_sample]
    intro h
    have := (by grind : ∀ x T : Rat, T ≠ 0 → x / T = 0 → x = 0) _ _ hT h
    exact hA this
  generalize reach as s cc = R at *
  grind

/-- **Retrieval does not depend on the backup strategies**: how often it is
used, and how often it errs, are the same whatever the elaboration and
counting. -/
theorem retrieval_independent_of_backup (as : List Answer) (s : Answer → Rat) (bk bk' : Backup)
    (cc : Rat) (n : Nat) (p : Problem) (hT : total as s ≠ 0) :
    prob (trial as s bk cc n p) isRetrieval = prob (trial as s bk' cc n p) isRetrieval ∧
      prob (trial as s bk cc n p) (retrievalWrong p) =
        prob (trial as s bk' cc n p) (retrievalWrong p) := by
  rw [retrieval_prob as s bk cc n p hT, retrieval_prob as s bk' cc n p hT,
    retrievalWrong_prob as s bk cc n p hT, retrievalWrong_prob as s bk' cc n p hT]
  exact ⟨rfl, rfl⟩

/-- Counting is a proper distribution. -/
theorem mass_count (qs qd : Rat) : ∀ k, mass (count qs qd k) = 1 := by
  intro k
  induction k with
  | zero => simp [mass, count, prob_pure] <;> grind
  | succ k ih =>
    simp only [mass, count]
    rw [prob_bind_split _ _ _ (fun _ => true) (fun _ => false) 0]
    · simp only [mass] at ih; rw [ih, prob_false]; grind
    · intro r; simp [prob] <;> grind

/-- Events on counting trials, by the answer counted. -/
theorem prob_trial_counting (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat)
    (n : Nat) (p : Problem) (e : Strategy × Answer → Bool) (P : Answer → Bool)
    (hr : ∀ a, e (.retrieval, a) = false) (hf : ∀ a, e (.fingers, a) = false)
    (hc : ∀ a, e (.countingFingers, a) = P a) (hT : total as s ≠ 0) :
    prob (trial as s bk cc n p) e =
      (1 - reach as s cc) ^ n *
        (prob (sample as (elaborate s p.sum bk.e)) (fun a => !above (elaborate s p.sum bk.e) cc a) *
          prob (count bk.qs bk.qd p.sum) P) := by
  have hcount : prob (Dist.bind (count bk.qs bk.qd p.sum)
      fun r => Dist.pure (Strategy.countingFingers, r)) e = prob (count bk.qs bk.qd p.sum) P := by
    rw [prob_bind_split _ _ _ P (fun _ => false) 0]
    · rw [prob_false]; grind
    · intro r; by_cases h : P r <;> simp [prob_pure, hc, h] <;> grind
  have hback : prob (backup as s bk cc p) e =
      prob (sample as (elaborate s p.sum bk.e)) (fun a => !above (elaborate s p.sum bk.e) cc a) *
        prob (count bk.qs bk.qd p.sum) P := by
    unfold backup
    rw [prob_bind_split _ _ _ (fun _ => false) (fun a => !above (elaborate s p.sum bk.e) cc a)
      (prob (count bk.qs bk.qd p.sum) P)]
    · rw [prob_false]; grind
    · intro a
      split
      · rename_i h; simp [prob_pure, hf, h] <;> grind
      · rename_i h; simp [h, hcount] <;> grind
  unfold trial
  rw [prob_bind_split _ _ _ (fun _ => false) Retrieval.isExhausted (prob (backup as s bk cc p) e)]
  · rw [prob_false, prob_exhausted as s cc hT, hback]; grind
  · intro r
    cases r with
    | stated a k => simp [prob_pure, hr, Retrieval.isExhausted] <;> grind
    | exhausted => simp [Retrieval.isExhausted] <;> grind

/-- **The error share on counting trials** is the counting process's error
rate on the sum: it involves neither the associations, nor the criterion, nor
the search length (p. 245). -/
theorem counting_error_share (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat)
    (n : Nat) (p : Problem) (hT : total as s ≠ 0) :
    prob (trial as s bk cc n p) (countingWrong p) =
      prob (trial as s bk cc n p) isCounting * prob (count bk.qs bk.qd p.sum) (fun a => a != p.sum) := by
  rw [prob_trial_counting as s bk cc n p (countingWrong p) (fun a => a != p.sum)
      (by intro a; simp [countingWrong]) (by intro a; simp [countingWrong])
      (by intro a; simp [countingWrong]) hT,
    prob_trial_counting as s bk cc n p isCounting (fun _ => true)
      (by intro a; rfl) (by intro a; rfl) (by intro a; rfl) hT]
  have := mass_count bk.qs bk.qd p.sum
  simp only [mass] at this
  rw [this]; grind

/-- **Moving strength to the correct answer never raises the error share on
retrieval trials**, at any confidence criterion and search length. Strengths
`s'` give the correct answer at least what `s` gives it, and every wrong
answer at most. -/
theorem peaking_lowers_retrieval_errors (as : List Answer) (s s' : Answer → Rat) (cc : Rat)
    (p : Problem) (hs : ∀ a, 0 ≤ s a) (hs' : ∀ a, 0 ≤ s' a)
    (hc : s p.sum ≤ s' p.sum) (hother : ∀ a, a ≠ p.sum → s' a ≤ s a)
    (hA : 0 < strengthIn as s (above s cc)) (hA' : 0 < strengthIn as s' (above s' cc)) :
    aboveShare as s' cc (fun a => a != p.sum) ≤ aboveShare as s cc (fun a => a != p.sum) :=
  aboveShare_shift as s s' cc p.sum hs hs' hc hother hA hA'

/-- **Learning from a correct answer never raises retrieval errors** (A6).
After the correct answer is stated, by any strategy (retrieval, fingers or
counting), and strengthened, the error share on retrieval trials is no larger
at any criterion. This is how backup strategies improve later retrieval. -/
theorem correct_strengthening_lowers_errors (as : List Answer) (s : Answer → Rat) (inc cc : Rat)
    (p : Problem) (hs : ∀ a, 0 ≤ s a) (hinc : 0 ≤ inc) (hA : 0 < strengthIn as s (above s cc)) :
    aboveShare as (strengthen s inc p.sum p.sum) cc (fun a => a != p.sum) ≤
      aboveShare as s cc (fun a => a != p.sum) := by
  have hge : ∀ a, s a ≤ strengthen s inc p.sum p.sum a := by
    intro a; simp only [strengthen]; split <;> grind
  have hs' : ∀ a, 0 ≤ strengthen s inc p.sum p.sum a := fun a => Rat.le_trans (hs a) (hge a)
  have hA' : 0 < strengthIn as (strengthen s inc p.sum p.sum) (above (strengthen s inc p.sum p.sum) cc) := by
    have hmono : strengthIn as s (above s cc) ≤
        strengthIn as (strengthen s inc p.sum p.sum) (above (strengthen s inc p.sum p.sum) cc) := by
      apply strengthIn_mono as _ s _ _ hs'
      intro a ha
      simp only [above, decide_eq_true_eq] at ha ⊢
      have := hge a
      exact ⟨by grind, this⟩
    grind
  apply peaking_lowers_retrieval_errors as s _ cc p hs hs' (hge p.sum) _ hA hA'
  intro a ha; simp [strengthen, ha]

/-! ### Peakedness and overt strategy use -/

/-- The twelve confidence criteria of the mathematical model (p. 250). -/
def criteria : List Rat :=
  [5/100, 10/100, 15/100, 20/100, 30/100, 40/100, 50/100, 60/100, 70/100, 80/100, 90/100, 1]

/-- Overt strategy use with search length `n`, averaged over the twelve
criteria. -/
def meanOvert (as : List Answer) (s : Answer → Rat) (n : Nat) : Rat :=
  (criteria.map fun cc => (1 - reach as s cc) ^ n).foldl (· + ·) 0 / 12

/-- A problem, `1 + 1`, with answers 2 (correct), 3 and 1. -/
def peakProblem : Problem := ⟨1, 1⟩
def peakAnswers : List Answer := [2, 3, 1]

/-- Strengths .38, .31, .31 ... -/
def flatter : Answer → Rat := fun a => if a = 2 then 38/100 else if a = 3 then 31/100 else 31/100
/-- ... and .39, .30, .31: one hundredth moved from a wrong answer to the
correct one, which was already the strongest. -/
def peaked : Answer → Rat := fun a => if a = 2 then 39/100 else if a = 3 then 30/100 else 31/100

/-- **Peaking can raise overt strategy use.** Moving strength to the correct
answer, already the peak, raises the overt strategy use predicted with search
length 1, averaged over the chapter's twelve criteria, from 7/12 to 73/120.
(The wrong answer drops to the criterion .30 and so below it.) -/
theorem peaking_can_raise_overt_use :
    peaked peakProblem.sum ≥ flatter peakProblem.sum ∧
      (∀ a, a ≠ peakProblem.sum → peaked a ≤ flatter a) ∧
      meanOvert peakAnswers flatter 1 = 7 / 12 ∧
      meanOvert peakAnswers peaked 1 = 73 / 120 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  intro a ha
  have h2 : a ≠ 2 := ha
  simp only [peaked, flatter, h2, ite_false]
  split <;> decide +kernel

end SC
