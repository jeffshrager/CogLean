/-
Multi-digit addition: EPAM recognition combined with distributions-of-
associations retrieval, as choices from CogLib.

A child adding two 3-digit numbers may simply *know* the answer to a
familiar problem (100 + 100), or may work it out column by column. The model
nests the distributions-of-associations architecture one level up:

* **Whole-problem retrieval.** An EPAM discrimination net recognizes the
  problem as one of the familiar problems it stores (EPAM D2). Retrieval
  then runs on that problem's distribution of associations (DOA A3).
* **Column backup.** If the problem is not recognized, or retrieval is
  exhausted, the answer is computed some other way, column by column.

| Postulate | CogLib |
|---|---|
| M1 Problem code: features for each digit of each addend | `Encoding`: `code`, `features`, `determines` |
| M2 Recognition: a discrimination net of familiar problems (EPAM D2) | `Cog.Net`, `Net.select` |
| M3 Whole-problem retrieval: the recognized problem's associations, a confidence criterion and a search length (DOA A1-A3) | `Cog.search` |
| M4 Column backup, when M2 or M3 fails | `backup`, a distribution of answers per problem |
| M1a-M1c Further features: zeros, magnitude, column facts | `Features.lean`: `Zeros`, `Magnitude`, `ColumnFacts` |

Nothing here is a table of numbers. The encoding, the net, the strengths,
the criterion, the search length and the backup are all parameters, and the
theorems in `Phenomena.lean` hold for every choice of them.

Simplifications:
* The backup is left abstract: any distribution of answers. Building it from
  single-digit DOA trials chained by carries is the next stage.
* Strengths are attached to stored codes. A code stores the problem it
  encodes (`select` returns `code q`), so a stored image's "correct" answer
  is `q`'s sum.
-/

import CogLib

namespace MD

open Cog Dist

/-- An addition problem `a + b`; the theorems about digits assume 3-digit
addends (`a, b < 1000`). -/
structure Problem where
  a : Nat
  b : Nat
  deriving Repr, DecidableEq

def Problem.sum (p : Problem) : Nat := p.a + p.b

/-- The problem with its addends swapped. -/
def Problem.swap (p : Problem) : Problem := ⟨p.b, p.a⟩

inductive Addend where
  | first
  | second
  deriving Repr, DecidableEq

inductive Place where
  | hundreds
  | tens
  | units
  deriving Repr, DecidableEq

def Problem.addend (p : Problem) : Addend → Nat
  | .first => p.a
  | .second => p.b

/-- A digit of a number. -/
def digitOf (n : Nat) : Place → Nat
  | .hundreds => n / 100 % 10
  | .tens => n / 10 % 10
  | .units => n % 10

def Problem.digit (p : Problem) (i : Addend) (j : Place) : Nat := digitOf (p.addend i) j

/-- A digit is less than 10. -/
theorem digit_lt (p : Problem) (i : Addend) (j : Place) : p.digit i j < 10 := by
  cases j <;> simp only [Problem.digit, digitOf] <;> exact Nat.mod_lt _ (by decide)

/-- **M1 Problem code.** Each digit of each addend has its own features, and
agreeing on a digit's features means having the same digit. -/
structure Encoding where
  code : Problem → Item
  features : Addend → Place → List Feature
  determines : ∀ p q i j, (∀ f ∈ features i j, (code p).feat f = (code q).feat f) →
    p.digit i j = q.digit i j

/-- The route by which an answer was reached. -/
inductive Route where
  | whole
  | columns
  deriving Repr, DecidableEq

/-- **A trial** (M2-M4). Recognize the problem's code in the net `N`. If it
is recognized as a stored code `y`, retrieve with `y`'s strengths `str y`,
criterion `cc` and search length `n`; if retrieval is exhausted, or nothing
is recognized, use the column backup. -/
def trial (E : Encoding) (N : Net) (str : Item → Nat → Rat) (as : List Nat) (cc : Rat) (n : Nat)
    (backup : Problem → Dist Nat) (x : Problem) : Dist (Route × Nat) :=
  match N.select (E.code x) with
  | none => Dist.bind (backup x) fun r => Dist.pure (.columns, r)
  | some y => Dist.bind (search as (str y) cc 0 n) fun
      | .stated a _ => Dist.pure (.whole, a)
      | .exhausted => Dist.bind (backup x) fun r => Dist.pure (.columns, r)

@[simp] theorem Route.whole_beq_whole : (Route.whole == Route.whole) = true := rfl
@[simp] theorem Route.columns_beq_columns : (Route.columns == Route.columns) = true := rfl
@[simp] theorem Route.whole_beq_columns : (Route.whole == Route.columns) = false := rfl
@[simp] theorem Route.columns_beq_whole : (Route.columns == Route.whole) = false := rfl

/-! ### Events -/

def isColumns (o : Route × Nat) : Bool := o.1 == .columns

def isWhole (o : Route × Nat) : Bool := o.1 == .whole

/-- An answer stated by whole-problem retrieval, with property `P`. -/
def wholeSuch (P : Nat → Bool) (o : Route × Nat) : Bool := o.1 == .whole && P o.2

/-- A wrong answer to `x`, stated by whole-problem retrieval. -/
def wholeWrong (x : Problem) : Route × Nat → Bool := wholeSuch fun a => a != x.sum

end MD
