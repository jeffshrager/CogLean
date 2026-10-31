/-
Exact evaluation of a trial.

A trial's distribution, written out, repeats outcomes: counting `k` objects
lists `3^k` of them. For exact computation (`decide +kernel`) `trialMerged`
merges equal outcomes after each stage. It is not a further model: it is the
same distribution as `trial` (`same_trialMerged`), so every probability
computed from it is a probability of `trial`.
-/

import StrategyChoice.Phenomena

namespace SC

open Cog Dist

/-- Counting, with equal outcomes merged after each object. -/
def countMerged (qs qd : Rat) : Nat → Dist Nat
  | 0 => Dist.pure 0
  | k + 1 => merge (Dist.bind (countMerged qs qd k) fun r => [(r, qs), (r + 1, 1 - qs - qd), (r + 2, qd)])

theorem same_countMerged (qs qd : Rat) : ∀ k, Same (countMerged qs qd k) (count qs qd k) := by
  intro k
  induction k with
  | zero => exact Same.refl _
  | succ k ih =>
    intro h
    simp only [countMerged, count]
    rw [same_merge]
    exact same_bind ih (fun _ => Same.refl _) h

/-- The backup strategies, with counting merged. -/
def backupMerged (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat) (p : Problem) :
    Dist (Strategy × Answer) :=
  merge <| Dist.bind (sample as (elaborate s p.sum bk.e)) fun a =>
    if above (elaborate s p.sum bk.e) cc a then Dist.pure (.fingers, a)
    else Dist.bind (countMerged bk.qs bk.qd p.sum) fun r => Dist.pure (.countingFingers, r)

/-- A trial, with equal outcomes merged. -/
def trialMerged (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat) (n : Nat)
    (p : Problem) : Dist (Strategy × Answer) :=
  merge <| Dist.bind (search as s cc 0 n) fun
    | .stated a _ => Dist.pure (.retrieval, a)
    | .exhausted => backupMerged as s bk cc p

theorem same_backupMerged (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat)
    (p : Problem) : Same (backupMerged as s bk cc p) (backup as s bk cc p) := by
  intro h
  simp only [backupMerged, backup]
  rw [same_merge]
  refine same_bind (Same.refl _) (fun a => ?_) h
  split
  · exact Same.refl _
  · exact same_bind (same_countMerged _ _ _) fun _ => Same.refl _

/-- **The merged trial is the trial**, as a distribution. -/
theorem same_trialMerged (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat) (n : Nat)
    (p : Problem) : Same (trialMerged as s bk cc n p) (trial as s bk cc n p) := by
  intro h
  simp only [trialMerged, trial]
  rw [same_merge]
  refine same_bind (Same.refl _) (fun o => ?_) h
  cases o with
  | stated a k => exact Same.refl _
  | exhausted => exact same_backupMerged as s bk cc p

end SC
