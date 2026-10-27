/-
A study-test experiment, run with four memories.

Study the three 3-bit codes 110, 101 and 011, once each, in that order.
Then test:
* each studied item, probed with itself, giving accuracy by serial position;
* the lure 111, never studied, the prototype of the three (each differs from
  it in one feature);
* the lure 000, never studied and unlike all three.

The experiment is written once (`E`); only the memory changes. The parameters
are those of the matrix's counterexamples (`CogMatrix/Matrix/*.lean`).

| Memory | Serial-position curve | 111 called old | 111 retrieves itself | 000 called old |
|---|---|---|---|---|
| Discrimination (EPAM) | 1, 1, 1 | 1 | 0 | 1 |
| Activation (ACT-R) | 40/97, 15/28, 120/157 | 55/61 | 0 | 55/67 |
| Strength (DOA) | 8/17, 8/17, 8/17 | 1 | 0 | 1 |
| Global matching (MINERVA 2) | 1, 1, 1 | 0 | 1 | 0 |

"Called old" means the probe retrieved some studied item. Each row follows
the family's laws:
* EPAM's flat curve follows from certainty and stability alone
  (`epam_curve_flat`, by `curve_flat`). EPAM has no recency, and confuses every
  lure with a studied item.
* ACT-R's curve rises with serial position: recency. No item is retrieved for
  certain, because ACT-R lacks certainty.
* Strength memory's curve is flat but low. It is order-free, so position
  can't matter, and similar items compete.
* MINERVA returns the prototype itself, never studied: it lacks stored-only
  retrieval. It rejects the dissimilar lure, whose echo has no positive
  intensity.
-/

import Experiments.StudyTest

namespace Cog.Exp.PrototypeDemo

open Laws Matrix

/-- The experiment. -/
def E : StudyTest := ⟨[bits 3, bits 5, bits 6], [bits 7, bits 0]⟩

/-! ### EPAM -/

def epam := netRetriever F3
def epam0 : Net := .leaf none

/-- Any two different 3-bit codes differ on a feature EPAM notices. -/
theorem noticeable_U3 : PairwiseNoticeable F3 U3 := by
  have h : ∀ x ∈ U3, ∀ z ∈ U3, z ≠ x → (firstDiff F3 x z).isSome = true := by decide
  intro x hx z hz hzx
  exact Option.isSome_iff_exists.mp (h x hx z hz hzx)

/-- **EPAM's flat curve, from laws alone.** -/
theorem epam_curve_flat : ∀ r ∈ E.curve epam epam0, r = 1 :=
  curve_flat epam epam0 U3 (Discrimination.certainty F3 U3 noticeable_U3)
    (Discrimination.stability F3 U3) E (by decide) (by decide)

theorem epam_lures :
    E.claimsOld epam epam0 (bits 7) = 1 ∧ E.retrievesItself epam epam0 (bits 7) = 0 ∧
      E.claimsOld epam epam0 (bits 0) = 1 := by
  decide +kernel

/-! ### ACT-R -/

def act := actRetriever Activation.P

/-- **ACT-R's curve rises with serial position.** -/
theorem act_curve : E.curve act Activation.empty = [40 / 97, 15 / 28, 120 / 157] := by
  decide +kernel

theorem act_curve_rises : (40 / 97 : Rat) < 15 / 28 ∧ (15 / 28 : Rat) < 120 / 157 := by
  decide +kernel

theorem act_lures :
    E.claimsOld act Activation.empty (bits 7) = 55 / 61 ∧
      E.retrievesItself act Activation.empty (bits 7) = 0 ∧
      E.claimsOld act Activation.empty (bits 0) = 55 / 67 := by
  decide +kernel

/-! ### Strength -/

def str := strRetriever Strength.P

theorem str_curve : E.curve str Strength.s0 = [8 / 17, 8 / 17, 8 / 17] := by
  decide +kernel

theorem str_lures :
    E.claimsOld str Strength.s0 (bits 7) = 1 ∧ E.retrievesItself str Strength.s0 (bits 7) = 0 ∧
      E.claimsOld str Strength.s0 (bits 0) = 1 := by
  decide +kernel

/-! ### MINERVA 2 -/

def minerva := minRetriever Minerva.P

theorem minerva_curve : E.curve minerva [] = [1, 1, 1] := by
  decide +kernel

/-- **MINERVA returns the prototype**, never studied, and rejects the
dissimilar lure. -/
theorem minerva_lures :
    E.claimsOld minerva [] (bits 7) = 0 ∧ E.retrievesItself minerva [] (bits 7) = 1 ∧
      E.claimsOld minerva [] (bits 0) = 0 := by
  decide +kernel

end Cog.Exp.PrototypeDemo
