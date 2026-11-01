/-
Phenomena of theory change, stated theory-neutrally.

Each is a property of the sequence of interpretations a learner brings in
at successive failed predictions (in `Process/TheoryRevision`, what each
revision brought in). Neither names a mechanism. They are events, so their
probabilities can be computed for any learner.

* `gardenPath`: the first knowledge brought in is not the last: an early
  interpretation was later replaced.
* `perseverates`: the same knowledge is brought in at two successive
  failures: a failed interpretation was tried again.
* `oscillates`: an interpretation is replaced and later brought back: the
  learner alternates between interpretations.
-/

namespace Cog.Phenomena

variable {V : Type} [DecidableEq V]

/-- **A garden path**: the first interpretation adopted is later replaced. -/
def gardenPath (vs : List V) : Bool :=
  match vs.head?, vs.getLast? with
  | some v, some w => v != w
  | _, _ => false

/-- **Perseveration**: the same interpretation is adopted at two successive
failures. -/
def perseverates : List V → Bool
  | v :: w :: rest => v == w || perseverates (w :: rest)
  | _ => false

/-- **Oscillation**: an interpretation is adopted, a different one later, and
the first again after that. -/
def oscillates : List V → Bool
  | [] => false
  | v :: rest => (match rest.dropWhile (· == v) with
      | w :: rest' => rest'.contains v
      | [] => false) || oscillates rest

/-- One adoption is neither a garden path nor perseveration. -/
theorem single_neither (v : V) : gardenPath [v] = false ∧ perseverates [v] = false := by
  simp [gardenPath, perseverates]

end Cog.Phenomena
