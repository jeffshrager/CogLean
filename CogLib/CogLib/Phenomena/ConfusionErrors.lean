/-
Phenomena of confusion between problems, stated theory-neutrally.

A task gives, for each problem, a distribution over observable outcomes
(`trial`). Three events on outcomes are named by the task, not here: an
answer stated by whole-problem retrieval (`isWhole`), such an answer that is
wrong for a given problem (`wholeWrong`), and use of a backup procedure
(`isBackup`). Nothing here says how the outcomes are produced, or why.

* `ConfusionErrorPattern`: a familiar problem `q` is never answered wrongly by
  retrieval; every retrieval answer to `x` is wrong; and `x` uses the backup
  exactly as often as `q`. Equal backup use is not low backup use.
* `ConfidentErrors r`: the pattern, with backup use on `x` at most `r`. The
  bound is an argument, not a fixed threshold.
* `GradedConfusionPattern ε`, `GradedConfidentErrors ε r`: the same, each
  equality holding to within `ε`. A memory whose retrieval is never certain
  can approach the pattern without reaching it. At `ε = 0` the pattern gives
  the graded one (`ConfusionErrorPattern.graded`).

Mechanisms exhibit these by theorem (`Process/RecognizeRetrieve`,
`RR.confident_errors` and `RR.confident_errors_of_laws`); the assumptions
that produce them (confusion, sharp associations, proper distributions) are
the theorems' hypotheses, not part of the definitions.
-/
import CogLib.Rep.Distribution

namespace Cog.Phenomena

open Dist

variable {P O : Type}

/-- **The confusion-error pattern.** Of two problems `x` and `q`: `q` is
never answered wrongly by retrieval; every retrieval answer to `x` is wrong;
and backup use on `x` equals that on `q`. -/
def ConfusionErrorPattern (trial : P → Dist O) (wholeWrong : P → O → Bool)
    (isWhole isBackup : O → Bool) (x q : P) : Prop :=
  prob (trial q) (wholeWrong q) = 0 ∧
    prob (trial x) (wholeWrong x) = prob (trial x) isWhole ∧
    prob (trial x) isBackup = prob (trial q) isBackup

/-- **Confident errors, with backup use at most `r`.** The confusion-error
pattern, and `x` uses the backup with probability at most `r`. -/
def ConfidentErrors (trial : P → Dist O) (wholeWrong : P → O → Bool)
    (isWhole isBackup : O → Bool) (x q : P) (r : Rat) : Prop :=
  ConfusionErrorPattern trial wholeWrong isWhole isBackup x q ∧ prob (trial x) isBackup ≤ r

/-- **The confusion-error pattern, to within `ε`.** `q` is answered wrongly
by retrieval with probability at most `ε`; `x` is answered rightly by
retrieval with probability at most `ε`; and backup use on the two differs by
at most `ε`. -/
def GradedConfusionPattern (trial : P → Dist O) (wholeWrong : P → O → Bool)
    (isWhole isBackup : O → Bool) (x q : P) (ε : Rat) : Prop :=
  prob (trial q) (wholeWrong q) ≤ ε ∧
    prob (trial x) isWhole - prob (trial x) (wholeWrong x) ≤ ε ∧
    prob (trial x) isBackup - prob (trial q) isBackup ≤ ε ∧
    prob (trial q) isBackup - prob (trial x) isBackup ≤ ε

/-- **Confident errors, to within `ε`, with backup use at most `r`.** -/
def GradedConfidentErrors (trial : P → Dist O) (wholeWrong : P → O → Bool)
    (isWhole isBackup : O → Bool) (x q : P) (ε r : Rat) : Prop :=
  GradedConfusionPattern trial wholeWrong isWhole isBackup x q ε ∧ prob (trial x) isBackup ≤ r

/-- The pattern is the conjunction of its three probability statements. -/
theorem confusionErrorPattern_iff (trial : P → Dist O) (wholeWrong : P → O → Bool)
    (isWhole isBackup : O → Bool) (x q : P) :
    ConfusionErrorPattern trial wholeWrong isWhole isBackup x q ↔
      (prob (trial q) (wholeWrong q) = 0 ∧
        prob (trial x) (wholeWrong x) = prob (trial x) isWhole ∧
        prob (trial x) isBackup = prob (trial q) isBackup) :=
  Iff.rfl

namespace ConfusionErrorPattern

variable {trial : P → Dist O} {wholeWrong : P → O → Bool} {isWhole isBackup : O → Bool} {x q : P}

theorem familiar_never_wrong (h : ConfusionErrorPattern trial wholeWrong isWhole isBackup x q) :
    prob (trial q) (wholeWrong q) = 0 := h.1

theorem confused_always_wrong (h : ConfusionErrorPattern trial wholeWrong isWhole isBackup x q) :
    prob (trial x) (wholeWrong x) = prob (trial x) isWhole := h.2.1

theorem same_backup (h : ConfusionErrorPattern trial wholeWrong isWhole isBackup x q) :
    prob (trial x) isBackup = prob (trial q) isBackup := h.2.2

/-- The pattern with a bound on backup use gives confident errors. -/
theorem confident {r : Rat} (h : ConfusionErrorPattern trial wholeWrong isWhole isBackup x q)
    (hr : prob (trial x) isBackup ≤ r) : ConfidentErrors trial wholeWrong isWhole isBackup x q r :=
  ⟨h, hr⟩

/-- The exact pattern is the graded pattern within 0. -/
theorem graded (h : ConfusionErrorPattern trial wholeWrong isWhole isBackup x q) :
    GradedConfusionPattern trial wholeWrong isWhole isBackup x q 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

end ConfusionErrorPattern

/-- The pattern fails if backup use on the two problems differs. -/
theorem not_confusionErrorPattern_of_backup_ne {trial : P → Dist O} {wholeWrong : P → O → Bool}
    {isWhole isBackup : O → Bool} {x q : P}
    (h : prob (trial x) isBackup ≠ prob (trial q) isBackup) :
    ¬ ConfusionErrorPattern trial wholeWrong isWhole isBackup x q :=
  fun hp => h hp.2.2

end Cog.Phenomena
