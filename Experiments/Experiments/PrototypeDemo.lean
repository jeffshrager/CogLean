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

"Called old" means the probe retrieved some studied item. The numbers are of
two kinds:
* Derived from laws: EPAM's flat curve follows from certainty and stability
  alone (`epam_curve_flat`, by `curve_flat`), for any memory with them.
* Computed from a mechanism, with these parameters: everything else. The
  laws do not predict these. ACT-R's rising curve is not implied by the
  recency law, which concerns a probe equally similar to two items. Strength
  memory's flat curve comes from the symmetry of the three items, not from
  order-freedom. MINERVA's returning the prototype witnesses that it lacks
  stored-only retrieval.

"Called old" is a report, and stored-only retrieval is about what memory
returns. EPAM and strength memory call the prototype old by returning a
studied item.
-/

import Experiments.StudyTest

namespace Cog.Exp.PrototypeDemo

open Laws Matrix

/-- The experiment. -/
def E : StudyTest := ⟨[bits 3, bits 5, bits 6], [bits 7, bits 0]⟩

/-! ### EPAM -/

def epam := netRetriever F3
def epam0 : Net := .leaf none

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
