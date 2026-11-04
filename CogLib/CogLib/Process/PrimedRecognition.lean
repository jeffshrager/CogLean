/-
Processes: recognition by ACT-R's declarative memory, with priming, then
retrieval, else back up.

EPAM's net calls up one stored code for certain, and so produces the exact
confusion-error pattern (`RR.confident_errors`). ACT-R's memory never
retrieves for certain (`Act.retrieve_not_certain`), so the exact pattern is
out of its reach in general. But spreading activation from a context that
primes a familiar `q` multiplies `q`'s weight. A stranger `x` that partially
matches `q` then calls up `q`, and `q` calls up itself, with probability as
close to 1 as the priming makes it, and the trial approaches the pattern:

* `act_primed_confident_errors`: with explicit bounds on the priming;
* `act_priming_confident_errors`: for every `δ > 0`, priming beyond some
  factor gives the pattern within `2δ`.

This is a second explanation of confident errors, from other mechanisms:
partial matching and priming, not discrimination. The two differ in what
they predict about the errors: EPAM's follow the features a stranger shares
with a stored problem; primed ACT-R's follow the context, such as what was
seen just before.
-/

import CogLib.Process.RecognizeRetrieve
import CogLib.Memory.Activation

namespace Cog
namespace RR

open Dist

/-- `a / (a + b)` is at least `1 - δ` when `b` is at most `δ a`. -/
theorem share_ge (a b δ : Rat) (ha : 0 < a) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (h : b ≤ δ * a) :
    1 - δ ≤ a / (a + b) := by
  have hab : 0 < a + b := by grind
  have e : 1 - δ = (1 - δ) / 1 := by grind
  rw [e]
  apply div_le_div_cross (by decide +kernel) hab
  have := Rat.mul_nonneg hδ hb
  grind

variable {P A : Type} [DecidableEq A] (code : P → Item)
  (str : Item → A → Rat) (as : List A) (cc : Rat) (n : Nat) (backup : P → Dist A)

/-- Unprimed weight on `y`, and on everything else, for the probe `x`. -/
abbrev wOn (Pa : ActParams) (s : ActState) (x y : Item) : Rat :=
  strengthIn (Act.outcomes s) (Act.weight Pa s x) (· == some y)
/-- The unprimed weight off `y`, failure included. -/
abbrev wOff (Pa : ActParams) (s : ActState) (x y : Item) : Rat :=
  strengthIn (Act.outcomes s) (Act.weight Pa s x) (fun o => !(o == some y))

/-- Retrieval in a context that primes a code with positive weight is a
proper distribution. -/
theorem primed_proper (Pa : ActParams) (s : ActState) (hμ : 0 ≤ Pa.mu) (hθ : 0 ≤ Pa.theta)
    (x y : Item) (ρ : Rat) (hρ : 0 < ρ) (hx : 0 < wOn Pa s x y) :
    Nonneg (Act.retrieveIn Pa (Act.primeOnly y ρ) s x) ∧ mass (Act.retrieveIn Pa (Act.primeOnly y ρ) s x) = 1 := by
  have hw := Act.weight_nonneg Pa hμ hθ s x
  have hwi : ∀ o, 0 ≤ Act.weightIn Pa (Act.primeOnly y ρ) s x o := by
    intro o; cases o with
    | none => exact hθ
    | some z =>
      simp only [Act.weightIn, Act.primeOnly]
      split
      · exact Rat.mul_nonneg (Rat.le_of_lt hρ) (hw _)
      · have := hw (some z); grind
  refine ⟨nonneg_sample _ _ hwi, mass_sample _ _ ?_⟩
  obtain ⟨h1, h2⟩ := Act.strengthIn_weightIn Pa s x y ρ
  rw [total, strengthIn_split _ _ (fun _ => true) (· == some y)]
  simp only [Bool.true_and]
  rw [h1, h2]
  have := strengthIn_nonneg (Act.outcomes s) (Act.weight Pa s x) (fun o => !(o == some y)) hw
  have := Rat.mul_pos hρ hx
  grind

/-- **Primed ACT-R memory makes graded confident errors.** In a context that
primes the familiar `q` by `ρ`, let the rest of the weight, for the probes
`x` and `q`, be at most `δ` times `q`'s primed weight. Then the trial makes
`Phenomena.GradedConfidentErrors` within `2δ`, with backup use on `x` at most
`q`'s exhaustion rate plus `δ`. Postulates: ACT-R's activation retrieval with
priming, sharp-criterion retrieval, the backup. Conditions: `x` partially
matches `q` (`hx`), `q` is stored (`hq`), the priming bounds, sharpness, and
well-formedness. -/
theorem act_primed_confident_errors (Pa : ActParams) (s : ActState) (correct : P → A) (x q : P)
    (ρ δ : Rat) (hμ : 0 ≤ Pa.mu) (hθ : 0 ≤ Pa.theta) (hρ : 0 < ρ) (hδ : 0 ≤ δ)
    (hx : 0 < wOn Pa s (code x) (code q)) (hq : 0 < wOn Pa s (code q) (code q))
    (hρx : wOff Pa s (code x) (code q) ≤ δ * (ρ * wOn Pa s (code x) (code q)))
    (hρq : wOff Pa s (code q) (code q) ≤ δ * (ρ * wOn Pa s (code q) (code q)))
    (hs0 : ∀ y a, 0 ≤ str y a) (hT : ∀ y, total as (str y) ≠ 0)
    (hbx : mass (backup x) = 1) (hbq : mass (backup q) = 1)
    (hs : Sharp str cc (code q) (correct q)) (hne : correct x ≠ correct q) :
    Phenomena.GradedConfidentErrors
      (recognizeRetrieve code (Act.retrieveIn Pa (Act.primeOnly (code q) ρ) s) str as cc n backup)
      (wholeWrong correct) isWhole isBackup x q (2 * δ) (backupAfter str as cc n (some (code q)) + δ) := by
  obtain ⟨nx, mx⟩ := primed_proper Pa s hμ hθ (code x) (code q) ρ hρ hx
  obtain ⟨nq, mq⟩ := primed_proper Pa s hμ hθ (code q) (code q) ρ hρ hq
  have hw := Act.weight_nonneg Pa hμ hθ s
  apply confident_errors_graded code _ str as cc n backup correct x q δ hs0 hT hbx hbq nx mx nq mq _ _ hs hne
  · rw [Act.prob_primed]
    exact share_ge _ _ _ (Rat.mul_pos hρ hq) (strengthIn_nonneg _ _ _ (hw _)) hδ hρq
  · rw [Act.prob_primed]
    exact share_ge _ _ _ (Rat.mul_pos hρ hx) (strengthIn_nonneg _ _ _ (hw _)) hδ hρx

/-- **Priming brings ACT-R's memory as close to the confusion-error pattern
as one likes.** For every `δ > 0` there is a priming factor beyond which the
trial makes graded confident errors within `2δ`. Without priming, the exact
pattern can fail (`MD.setting_actr_not_pattern`), and ACT-R's retrieval is
never certain (`Act.retrieve_not_certain`); the exact pattern is the limit,
not a value reached. Conditions as in `act_primed_confident_errors`, with no
bound on `ρ`. -/
theorem act_priming_confident_errors (Pa : ActParams) (s : ActState) (correct : P → A) (x q : P)
    (δ : Rat) (hμ : 0 ≤ Pa.mu) (hθ : 0 ≤ Pa.theta) (hδ : 0 < δ)
    (hx : 0 < wOn Pa s (code x) (code q)) (hq : 0 < wOn Pa s (code q) (code q))
    (hs0 : ∀ y a, 0 ≤ str y a) (hT : ∀ y, total as (str y) ≠ 0)
    (hbx : mass (backup x) = 1) (hbq : mass (backup q) = 1)
    (hs : Sharp str cc (code q) (correct q)) (hne : correct x ≠ correct q) :
    ∃ ρ₀, ∀ ρ, ρ₀ ≤ ρ → Phenomena.GradedConfidentErrors
      (recognizeRetrieve code (Act.retrieveIn Pa (Act.primeOnly (code q) ρ) s) str as cc n backup)
      (wholeWrong correct) isWhole isBackup x q (2 * δ) (backupAfter str as cc n (some (code q)) + δ) := by
  have hw := Act.weight_nonneg Pa hμ hθ s
  let ox := wOff Pa s (code x) (code q)
  let oq := wOff Pa s (code q) (code q)
  have hox : 0 ≤ ox := strengthIn_nonneg _ _ _ (hw _)
  have hoq : 0 ≤ oq := strengthIn_nonneg _ _ _ (hw _)
  refine ⟨ox / (δ * wOn Pa s (code x) (code q)) + oq / (δ * wOn Pa s (code q) (code q)) + 1, ?_⟩
  intro ρ hρ
  have dx : 0 < δ * wOn Pa s (code x) (code q) := Rat.mul_pos hδ hx
  have dq : 0 < δ * wOn Pa s (code q) (code q) := Rat.mul_pos hδ hq
  have ax := div_nonneg' hox (Rat.le_of_lt dx)
  have aq := div_nonneg' hoq (Rat.le_of_lt dq)
  have key : ∀ (o d : Rat), 0 < d → o / d ≤ ρ → o ≤ ρ * d := by
    intro o d hd h
    have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hd)
    have e : o / d * d = o := by have : d ≠ 0 := by grind
                                 grind
    grind
  have kx := key ox _ dx (by grind)
  have kq := key oq _ dq (by grind)
  apply act_primed_confident_errors code str as cc n backup Pa s correct x q ρ δ hμ hθ (by grind)
    (Rat.le_of_lt hδ) hx hq _ _ hs0 hT hbx hbq hs hne
  · have : ρ * (δ * wOn Pa s (code x) (code q)) = δ * (ρ * wOn Pa s (code x) (code q)) := by grind
    grind
  · have : ρ * (δ * wOn Pa s (code q) (code q)) = δ * (ρ * wOn Pa s (code q) (code q)) := by grind
    grind
end RR
end Cog
