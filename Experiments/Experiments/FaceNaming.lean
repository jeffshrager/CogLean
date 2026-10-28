/-
A second task through the same composition: naming familiar people.

Nothing here is arithmetic. A face is a code. Memory recognizes it as a
familiar face, or as nothing (any `Retriever`). The recognized person's name
associations are then searched, with a criterion and a search length. When
nothing is recognized or no name clears the criterion, the backup is
"don't know". That is CogLib's `recognizeRetrieve`, the composition first
extracted from multi-digit addition, with people for problems and names for
answers.

Familiar: Ann (face 000) and Bob (face 110). Each face's own name has
strength .90, and other names .01; criterion .50. The stranger Carl (face
100) differs from each familiar face in one feature.

* **Confident misnaming, inherited** (`epam_confident_misnaming`). EPAM's
  net learns Ann and Bob, tests only the first feature, and recognizes Carl
  as Bob. By `Cog.RR.confident_errors`, for every search length:
  - Bob is never misnamed;
  - every name Carl is given is wrong;
  - Carl says "don't know" exactly as rarely as Bob does.

  This is the multi-digit confident error, with no arithmetic: a retrieved,
  wrong name with no extra "don't know", which comes from recognizing the
  wrong person, not from uncertain memory.
* **The same, from laws** (`epam_confident_misnaming_of_laws`), by
  `Cog.RR.confident_errors_of_laws`, from EPAM's matrix cells (determinate,
  certain, stable) and one computed fact: Carl can be taken for Bob.
* **Graded misnaming with ACT-R's memory** (`act_values`), same task, same
  associations, search length 1:

| | EPAM | ACT-R |
|---|---|---|
| Carl named Bob | 45/46 | 225/391 |
| Carl named Ann | 0 | 225/782 |
| Carl: "don't know" | 1/46 | 107/782 |
| Bob: "don't know" | 1/46 | 229/2254 |
| Bob named Ann | 0 | 225/2254 |

  Under ACT-R, Carl can be taken for either familiar person. He says "don't
  know" more often than Bob does, and even Bob is sometimes misnamed. The
  general theorem's hypothesis (Carl's face calls up Bob's for certain) does
  not hold for ACT-R, and its conclusion fails (`act_more_dont_know`).
-/

import CogMatrix

namespace Cog.Exp.FaceNaming

open Dist Matrix

/-- Names, and the backup answer. -/
inductive Name where
  | ann
  | bob
  | carl
  | dunno
  deriving Repr, DecidableEq

/-- A person: a face, and the person's name. -/
structure Person where
  face : Item
  name : Name

def ann : Person := ⟨bits 0, .ann⟩
def bob : Person := ⟨bits 3, .bob⟩
def carl : Person := ⟨bits 1, .carl⟩

/-- The names searched. -/
def names : List Name := [.ann, .bob, .carl]

/-- Name associations of the familiar faces: .90 to the face's own name, .01
to the others. -/
def str (y : Item) (a : Name) : Rat :=
  if y = ann.face then (if a = .ann then 9 / 10 else 1 / 100)
  else if y = bob.face then (if a = .bob then 9 / 10 else 1 / 100)
  else 1 / 100

/-- The backup: "don't know". -/
def backup (_ : Person) : Dist Name := Dist.pure .dunno

theorem total_ne (y : Item) : total names (str y) ≠ 0 := by
  unfold str
  by_cases h1 : y = ann.face <;> by_cases h2 : y = bob.face <;>
    simp only [h1, h2, ite_true, ite_false] <;> decide +kernel

theorem mass_backup (p : Person) : mass (backup p) = 1 := by
  simp [mass, backup, prob_pure]

/-- Bob's face's associations are sharp: only "Bob" clears the criterion. -/
theorem sharp_bob : RR.Sharp str (1 / 2) bob.face Name.bob := by
  intro a ha
  revert ha
  cases a <;> decide +kernel

/-! ### EPAM -/

/-- The net after learning Ann and Bob. -/
def net : Net := (netRetriever F3).studyAll (Net.leaf none) [ann.face, bob.face]

theorem net_bob : net.retrieve bob.face = pure (some bob.face) :=
  Net.retrieve_of_select _ _ _ (by decide +kernel)

theorem net_carl : net.retrieve carl.face = pure (some bob.face) :=
  Net.retrieve_of_select _ _ _ (by decide +kernel)

/-- **Confident misnaming**, inherited from `Cog.RR.confident_errors`, for
every search length. -/
theorem epam_confident_misnaming (n : Nat) :
    prob (recognizeRetrieve Person.face net.retrieve str names (1 / 2) n backup bob)
        (RR.wholeWrong Person.name bob) = 0 ∧
      prob (recognizeRetrieve Person.face net.retrieve str names (1 / 2) n backup carl)
          (RR.wholeWrong Person.name carl) =
        prob (recognizeRetrieve Person.face net.retrieve str names (1 / 2) n backup carl)
          RR.isWhole ∧
      prob (recognizeRetrieve Person.face net.retrieve str names (1 / 2) n backup carl)
          RR.isBackup =
        prob (recognizeRetrieve Person.face net.retrieve str names (1 / 2) n backup bob)
          RR.isBackup :=
  RR.confident_errors Person.face net.retrieve str names (1 / 2) n backup Person.name carl bob
    total_ne (mass_backup carl) (mass_backup bob) net_bob net_carl sharp_bob (by decide)

/-- **Confident misnaming, from EPAM's laws.** The same conclusion, derived
from matrix cells: discrimination is determinate, certain (on the 3-bit
codes, which it can tell apart) and stable. The only computed fact is that
Carl can be taken for Bob. -/
theorem epam_confident_misnaming_of_laws (n : Nat) :
    prob (recognizeRetrieve Person.face ((netRetriever F3).retrieve net) str names (1 / 2) n backup
        bob) (RR.wholeWrong Person.name bob) = 0 ∧
      prob (recognizeRetrieve Person.face ((netRetriever F3).retrieve net) str names (1 / 2) n backup
          carl) (RR.wholeWrong Person.name carl) =
        prob (recognizeRetrieve Person.face ((netRetriever F3).retrieve net) str names (1 / 2) n
          backup carl) RR.isWhole ∧
      prob (recognizeRetrieve Person.face ((netRetriever F3).retrieve net) str names (1 / 2) n backup
          carl) RR.isBackup =
        prob (recognizeRetrieve Person.face ((netRetriever F3).retrieve net) str names (1 / 2) n
          backup bob) RR.isBackup :=
  RR.confident_errors_of_laws Person.face str names (1 / 2) n backup (netRetriever F3) (Net.leaf none)
    U3 (Discrimination.determinate F3 U3) (Discrimination.certainty F3 U3 noticeable_U3)
    (Discrimination.stability F3 U3) [ann.face, bob.face] (by decide) (by decide) Person.name carl bob
    (by decide) (by decide +kernel) total_ne (mass_backup carl) (mass_backup bob) sharp_bob
    (by decide)

/-! ### Both memories, search length 1 -/

def epamTrial (p : Person) : Dist (Route × Name) :=
  recognizeRetrieve Person.face net.retrieve str names (1 / 2) 1 backup p

/-- Memory after studying Ann's face, then Bob's. -/
def mem : ActState := (actRetriever Activation.P).studyAll Activation.empty [ann.face, bob.face]

def actTrial (p : Person) : Dist (Route × Name) :=
  recognizeRetrieve Person.face ((actRetriever Activation.P).retrieve mem) str names (1 / 2) 1
    backup p

theorem epam_values :
    prob (epamTrial carl) (RR.wholeSuch (· == Name.bob)) = 45 / 46 ∧
      prob (epamTrial carl) (RR.wholeSuch (· == Name.ann)) = 0 ∧
      prob (epamTrial carl) RR.isBackup = 1 / 46 ∧
      prob (epamTrial bob) RR.isBackup = 1 / 46 ∧
      prob (epamTrial bob) (RR.wholeSuch (· == Name.ann)) = 0 := by
  decide +kernel

theorem act_values :
    prob (actTrial carl) (RR.wholeSuch (· == Name.bob)) = 225 / 391 ∧
      prob (actTrial carl) (RR.wholeSuch (· == Name.ann)) = 225 / 782 ∧
      prob (actTrial carl) RR.isBackup = 107 / 782 ∧
      prob (actTrial bob) RR.isBackup = 229 / 2254 ∧
      prob (actTrial bob) (RR.wholeSuch (· == Name.ann)) = 225 / 2254 := by
  decide +kernel

/-- **Under ACT-R, the stranger says "don't know" more often than the familiar
person**, so the third part of confident errors fails. -/
theorem act_more_dont_know : prob (actTrial bob) RR.isBackup < prob (actTrial carl) RR.isBackup := by
  decide +kernel

end Cog.Exp.FaceNaming
