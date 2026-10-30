/-
View application to concepts: an ARITHMETIC view for number concepts.

The learner's theory of number concepts, as a knowledge net (CogLib's
`Process/Categorize`):
* the type frame `category`: membership by similarity to a prototype,
  graded by Hampton's threshold (`test = simTest []`), and combination by
  selective modification (`combine = modifyComb []`, Smith et al. 1988);
* `mult3` (*multiple of 3*), whose prototype is learned from the exemplars
  3, 6, …, 30, as in `Concepts.Numbers`, and `even`, an adjective naming
  parity 0, learned from 2, 4, …, 20. Each is `named` by what it is a
  multiple of.

The ARITHMETIC view has a `category` type frame too: membership by
divisibility (`test = divisibleBy [hole k]`, with `k` read from the
concept's name through `named = multipleOf [hole k]`), and combination by
conjunction (`combine = conjComb []`).

Applying the view (CogLib's view application, unchanged): `category` is
matched to the view's `category`, the same abstract type, so the view wins
on `test` and `combine`. The concepts' own frames, prototypes included, are
not matched, so they are kept.

* Before: 14 is an *even multiple of 3* to degree .80 and a *multiple of 3*
  to degree .06 (`before`): over-extension, as in `Concepts`.
* After: membership in *even multiple of 3* is exactly divisibility by 6,
  for every number (`after_exact`), so no number is ever more a member of
  the combination than of *multiple of 3* (`after_no_overextension`).
* Typicality is unchanged, for every number (`typicality_unchanged`): 14 is
  still more typical of *even multiple of 3* than of *multiple of 3*, though
  now a member of neither (`dissociation`). Typicality is graded where
  membership is all-or-none, as Armstrong, Gleitman & Gleitman (1983) found
  for *odd number*.
-/

import CogLib.Process.Categorize

namespace ViewApplication.Numbers

open Cog

inductive A
  | category | mult3 | even | kCat
  | simTest | modifyComb | divisibleBy | conjComb | multipleOf | av | dv | k
  | parity | lastDigit | digitSum3 | size
  | num (n : Nat)
  deriving DecidableEq

inductive Lbl | isa | kind | test | combine | named | adj | vote | diag | indicates
  deriving DecidableEq

open A

abbrev a := @Term.atom A
abbrev ap := @Term.app A
abbrev h := @Term.hole A

def dsum3 (n : Nat) : Nat := (n / 100 + n / 10 % 10 + n % 10) % 3
def ndigits (n : Nat) : Nat := if n < 10 then 1 else if n < 100 then 2 else 3

/-- The value of each attribute of `n`. -/
def val (n : Nat) : A → A
  | .parity => num (n % 2)
  | .lastDigit => num (n % 10)
  | .digitSum3 => num (dsum3 n)
  | .size => num (ndigits n)
  | _ => num 0

def S : Schema A A where
  attrs := [parity, lastDigit, digitSum3, size]
  vals
    | .parity => [num 0, num 1]
    | .lastDigit => (List.range 10).map num
    | .digitSum3 => [num 0, num 1, num 2]
    | .size => [num 1, num 2, num 3]
    | _ => []

/-- A prototype learned from exemplars, as links: on each value, the number
of exemplars with it; every diagnosticity 1. -/
def protoLinks (c : A) (exs : List Nat) : List (Term A × Lbl × Term A) :=
  S.attrs.flatMap fun i =>
    (a c, .diag, ap dv [a i, a (num 1)]) ::
      (S.vals i).filterMap fun v =>
        let n := (exs.filter fun e => val e i == v).length
        if n = 0 then none else some (a c, .vote, ap av [a i, a v, a (num n)])

def numOf : A → Rat
  | num n => n
  | _ => 0

/-- Divisibility, the arithmetic the view's test refers to. -/
def rule : Term A → Nat → Bool
  | .app divisibleBy [.atom (num d)], n => n % d == 0
  | _, _ => false

def C : CatConfig A Lbl Nat where
  voteL := .vote
  diagL := .diag
  testL := .test
  combineL := .combine
  namedL := .named
  adjL := .adj
  av := av
  dv := dv
  simTest := simTest
  modifyComb := modifyComb
  num := numOf
  K := ⟨1, 1, 1⟩
  boost := 2
  SL := -50
  SH := 0
  S := S
  inst n := Inst.pure (val n) fun _ => 10
  rule := rule

/-- The learner's theory. -/
def theory : KNet A Lbl where
  isa := .isa
  links := [
    (a category, .kind, a kCat), (a category, .test, ap simTest []),
    (a category, .combine, ap modifyComb []),
    (a mult3, .isa, a category), (a mult3, .named, ap multipleOf [a (num 3)]),
    (a even, .isa, a category), (a even, .named, ap multipleOf [a (num 2)]),
    (a even, .adj, ap av [a parity, a (num 0)])] ++
    protoLinks mult3 ((List.range 10).map fun j => 3 * (j + 1)) ++
    protoLinks even ((List.range 10).map fun j => 2 * (j + 1))

/-- The ARITHMETIC view. -/
def arithmetic : KNet A Lbl where
  isa := .isa
  links := [
    (a category, .kind, a kCat), (a category, .test, ap divisibleBy [h k]),
    (a category, .combine, ap conjComb []), (a category, .named, ap multipleOf [h k])]

def K : VAConfig Lbl := ⟨.kind, .indicates⟩

/-- The theory after applying the view (the one outcome). -/
def after : KNet A Lbl :=
  match applyView K arithmetic theory with
  | [(G, _)] => G
  | _ => theory

/-- Applying the view has one outcome: `category` matches the view's
`category`, the same abstract type. -/
theorem one_outcome : (applyView K arithmetic theory).length = 1 ∧
    Dist.mass (applyView K arithmetic theory) = 1 := by
  decide +kernel

/-- **Before**: over-extension. 14 is an *even multiple of 3* to degree .80,
a *multiple of 3* to degree .06. -/
theorem before : membership2 C theory even mult3 14 = 497 / 625 ∧
    membership C theory mult3 14 = 81 / 1250 := by
  decide +kernel

theorem after_slots :
    typeSlot after mult3 .test = some (ap divisibleBy [h k]) ∧
      typeSlot after mult3 .named = some (ap multipleOf [h k]) ∧
      after.slot mult3 .named = some (ap multipleOf [a (num 3)]) ∧
      typeSlot after even .test = some (ap divisibleBy [h k]) ∧
      typeSlot after even .named = some (ap multipleOf [h k]) ∧
      after.slot even .named = some (ap multipleOf [a (num 2)]) ∧
      typeSlot after mult3 .combine = some (ap conjComb []) := by
  decide +kernel

/-- After the view, membership in *multiple of 3* is divisibility by 3. -/
theorem after_head (n : Nat) : membership C after mult3 n = if n % 3 = 0 then 1 else 0 := by
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := after_slots
  have hne : ¬ (ap divisibleBy [h k] = Term.app simTest []) := by decide
  have hf : Term.fill (((ap multipleOf [h k]).unify (ap multipleOf [a (num 3)])).getD [])
      (ap divisibleBy [h k]) = ap divisibleBy [a (num 3)] := by decide
  simp only [membership, h1, h2, h3, C, hne, ite_false, hf]
  by_cases hd : n % 3 = 0 <;> simp [rule, hd]

theorem after_adj (n : Nat) : membership C after even n = if n % 2 = 0 then 1 else 0 := by
  obtain ⟨-, -, -, h1, h2, h3, -⟩ := after_slots
  have hne : ¬ (ap divisibleBy [h k] = Term.app simTest []) := by decide
  have hf : Term.fill (((ap multipleOf [h k]).unify (ap multipleOf [a (num 2)])).getD [])
      (ap divisibleBy [h k]) = ap divisibleBy [a (num 2)] := by decide
  simp only [membership, h1, h2, h3, C, hne, ite_false, hf]
  by_cases hd : n % 2 = 0 <;> simp [rule, hd]

/-- **After: membership is exact.** An *even multiple of 3* is exactly a
multiple of 6, for every number. -/
theorem after_exact (n : Nat) : membership2 C after even mult3 n = if n % 6 = 0 then 1 else 0 := by
  obtain ⟨-, -, -, -, -, -, h7⟩ := after_slots
  unfold membership2
  rw [show C.combineL = Lbl.combine from rfl, h7, ite_eq_right (by decide), after_head, after_adj]
  have key : n % 6 = 0 ↔ n % 2 = 0 ∧ n % 3 = 0 := by omega
  by_cases h2 : n % 2 = 0 <;> by_cases h3 : n % 3 = 0 <;> simp only [h2, h3, key] <;> decide

/-- **No over-extension after the view**, at any number. -/
theorem after_no_overextension (n : Nat) :
    membership2 C after even mult3 n ≤ membership C after mult3 n := by
  rw [after_exact, after_head]
  by_cases h3 : n % 3 = 0 <;> by_cases h6 : n % 6 = 0 <;> simp [h3, h6] <;> first | decide | omega

/-- The view leaves the concepts' prototype links alone. -/
theorem prototypes_kept :
    after.targets (a mult3) .vote = theory.targets (a mult3) .vote ∧
      after.targets (a mult3) .diag = theory.targets (a mult3) .diag ∧
      after.targets (a even) .adj = theory.targets (a even) .adj := by
  decide +kernel

/-- **Typicality is unchanged by the view**, for every number. -/
theorem typicality_unchanged (n : Nat) :
    typicality C after mult3 n = typicality C theory mult3 n ∧
      typicality2 C after even mult3 n = typicality2 C theory even mult3 n := by
  obtain ⟨hv, hd, ha⟩ := prototypes_kept
  have hp : protoOfNet C after mult3 = protoOfNet C theory mult3 := by
    simp only [protoOfNet, weightOf_congr C after theory mult3 C.diagL C.dv _ hd,
      weightOf_congr C after theory mult3 C.voteL C.av _ hv]
  have hadj : adjOf after C even = adjOf theory C even := by
    unfold adjOf; rw [show C.adjL = Lbl.adj from rfl, ha]
  exact ⟨typicality_congr C after theory mult3 hv hd n, by simp only [typicality2, hadj, hp, typicality]⟩

/-- **Typicality and membership dissociate**: after the view, 14 is still
more typical of *even multiple of 3* than of *multiple of 3*, and a member
of neither. -/
theorem dissociation :
    typicality C after mult3 14 < typicality2 C after even mult3 14 ∧
      membership2 C after even mult3 14 = 0 ∧ membership C after mult3 14 = 0 := by
  refine ⟨?_, by rw [after_exact]; decide, by rw [after_head]; decide⟩
  rw [(typicality_unchanged 14).1, (typicality_unchanged 14).2]
  decide +kernel

end ViewApplication.Numbers
