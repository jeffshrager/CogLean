/-
Exact trial distributions of the Lean model, as JSON, for comparison with the
blind simulation (`sim/compare.py`). Not part of the library build:

    cd MultiDigit && lake env lean --tstack=4000000 Export.lean > sim/instances/lean_exact.json

Each instance matches a parameter file in `sim/instances/`. The column backup
is `columns` with DOA single-digit trials (`doaFact`), as in the
simulation's spec. Distributions are collapsed (equal outcomes merged) before
the columns are chained; this changes no probability, only the size of the
list.
-/

import MultiDigit

namespace MD.Export

open Cog Dist MD

/-- Merge equal outcomes. -/
def collapse {α : Type} [DecidableEq α] (d : Dist α) : Dist α :=
  d.foldl (fun acc (a, p) =>
    if acc.any (·.1 == a) then acc.map fun (b, q) => if b = a then (b, q + p) else (b, q)
    else acc ++ [(a, p)]) []

def ratStr (r : Rat) : String := s!"\"{r.num}/{r.den}\""

def probStr (p : Problem) : String := s!"{p.a}+{p.b}"

/-- Whole-problem strengths: a table per familiar problem, looked up by its
code; 0 for answers not in the table and for unknown codes. -/
def wholeStr (E : Encoding) (table : List (Problem × List (Nat × Rat))) (y : Item) (a : Nat) : Rat :=
  match table.find? (fun (q, _) => E.code q == y) with
  | some (_, t) => (t.find? (·.1 == a)).map (·.2) |>.getD 0
  | none => 0

/-- Single-digit strengths over 0..18: `correct` for d + e, `other` otherwise,
with overrides. -/
def singleStr (correct other : Rat) (overrides : List ((Nat × Nat) × List (Nat × Rat)))
    (p : SC.Problem) (a : Nat) : Rat :=
  match overrides.find? (·.1 == (p.a, p.b)) with
  | some (_, t) =>
    match t.find? (·.1 == a) with
    | some (_, s) => s
    | none => if a = p.a + p.b then correct else other
  | none => if a = p.a + p.b then correct else other

structure Instance where
  name : String
  E : Encoding
  order : NoticingOrder
  familiar : List Problem
  answers : List Nat
  whole : List (Problem × List (Nat × Rat))
  c : Rat
  n : Nat
  overrides : List ((Nat × Nat) × List (Nat × Rat))
  correct : Rat
  other : Rat
  c1 : Rat
  n1 : Nat
  bk : SC.Backup
  schedule : List Problem

def Instance.net (I : Instance) : Net :=
  Net.learnAll I.order (Net.leaf none) (I.familiar.map I.E.code)

def Instance.fact (I : Instance) (d e : Nat) : Dist Nat :=
  collapse (doaFact (List.range 19) (singleStr I.correct I.other I.overrides) I.bk I.c1 I.n1 d e)

def Instance.dist (I : Instance) (x : Problem) : Dist (Route × Nat) :=
  collapse (trial I.E I.net (wholeStr I.E I.whole) I.answers I.c I.n
    (fun p => collapse (columns I.fact p)) x)

def Instance.recognized (I : Instance) (x : Problem) : String :=
  match I.net.select (I.E.code x) with
  | some y =>
    match I.familiar.find? (fun q => I.E.code q == y) with
    | some q => s!"\"{probStr q}\""
    | none => "\"?\""
  | none => "null"

def routeStr : Route → String
  | .whole => "whole"
  | .columns => "columns"

def Instance.json (I : Instance) : String :=
  let probs := I.schedule.map fun x =>
    let outs := (I.dist x).map fun (o, p) =>
      s!"\{\"route\": \"{routeStr o.1}\", \"answer\": {o.2}, \"p\": {ratStr p}}"
    s!"\"{probStr x}\": \{\"recognized_as\": {I.recognized x}, \"outcomes\": [{", ".intercalate outs}]}"
  s!"\"{I.name}\": \{{", ".intercalate probs}}"

def bk : SC.Backup := ⟨1 / 20, 1 / 10, 1 / 10⟩

def sharp (q : Problem) (answers : List Nat) : Problem × List (Nat × Rat) :=
  (q, answers.map fun a => (a, if a = q.sum then 9 / 10 else 1 / 100))

/-- `Example.lean`'s net, with DOA columns. -/
def i1 : Instance where
  name := "i1_bcd_example"
  E := Example.bcd
  order := Example.order
  familiar := [⟨100, 100⟩, ⟨100, 200⟩]
  answers := [200, 250, 300]
  whole := [sharp ⟨100, 100⟩ [200, 250, 300], sharp ⟨100, 200⟩ [200, 250, 300]]
  c := 1 / 2
  n := 1
  overrides := [((1, 1), [(2, 3 / 10), (3, 3 / 10)])]
  correct := 3 / 5
  other := 1 / 50
  c1 := 2 / 5
  n1 := 1
  bk := bk
  schedule := [⟨150, 100⟩, ⟨100, 100⟩, ⟨100, 200⟩, ⟨120, 130⟩]

/-- `Example2.lean`'s zeros net. -/
def i2 : Instance where
  name := "i2_rich_zeros"
  E := Example2.rich
  order := Example2.richOrder
  familiar := [⟨100, 100⟩, ⟨120, 100⟩]
  answers := [200, 220, 250]
  whole := [sharp ⟨100, 100⟩ [200, 220, 250], sharp ⟨120, 100⟩ [200, 220, 250]]
  c := 1 / 2
  n := 2
  overrides := []
  correct := 3 / 5
  other := 1 / 50
  c1 := 2 / 5
  n1 := 2
  bk := bk
  schedule := [⟨150, 100⟩, ⟨100, 100⟩, ⟨120, 100⟩]

/-- `Example2.lean`'s magnitude nets, rich and BCD. -/
def i3 : Instance where
  name := "i3_rich_magnitude"
  E := Example2.rich
  order := Example2.richOrder
  familiar := [⟨700, 100⟩, ⟨800, 100⟩]
  answers := [700, 800, 900]
  whole := [(⟨700, 100⟩, [(800, 7 / 10), (900, 1 / 10), (700, 1 / 10)]),
    (⟨800, 100⟩, [(900, 7 / 10), (800, 1 / 10), (700, 1 / 10)])]
  c := 3 / 10
  n := 1
  overrides := []
  correct := 3 / 5
  other := 1 / 50
  c1 := 2 / 5
  n1 := 1
  bk := bk
  schedule := [⟨600, 100⟩]

def i4 : Instance := { i3 with name := "i4_bcd_magnitude", E := Example.bcd, order := Example.order }

#eval IO.println ("{" ++ ", ".intercalate ([i1, i2, i3, i4].map Instance.json) ++ "}")

end MD.Export
