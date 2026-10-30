/-
`lake exe sc-check [--draws=N]`

Checks the simulation's trial sampler against the model: on small cases,
the frequency of every outcome of `drawTrial` must lie within 4 standard
errors of its exact probability under `SC.trial`.
-/

import Sims.StrategyChoice

open Cog Sims Sims.SCSim SC

def toF (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

structure Case where
  name : String
  as : List Answer
  s : Answer → Rat
  bk : Backup
  cc : Rat
  n : Nat
  p : Problem

def cases : List Case := [
  ⟨"1+1, n=1, cc=.3", [1, 2, 3, 4], fun a => if a = 2 then 3 / 10 else 1 / 10, ⟨1 / 20, 1 / 10, 1 / 10⟩, 3 / 10, 1, ⟨1, 1⟩⟩,
  ⟨"1+2, n=2, cc=.2", [1, 2, 3, 4, 5], fun a => if a = 3 then 1 / 4 else if a = 4 then 1 / 5 else 1 / 20,
    ⟨1 / 20, 1 / 20, 1 / 10⟩, 1 / 5, 2, ⟨1, 2⟩⟩,
  ⟨"2+2, n=3, cc=.5", [2, 3, 4, 5], fun _ => 1 / 10, ⟨1 / 20, 1 / 5, 1 / 10⟩, 1 / 2, 3, ⟨2, 2⟩⟩]

def outcomes : List (Strategy × Answer) :=
  [Strategy.retrieval, .fingers, .countingFingers].flatMap fun st => (List.range 9).map fun a => (st, a)

def checkCase (c : Case) (draws seed : Nat) : IO Bool := do
  let exact := trial c.as c.s c.bk c.cc c.n c.p
  let mut counts : Array Nat := Array.replicate outcomes.length 0
  let mut g := mkStdGen seed
  for _ in [0:draws] do
    let (o, g') := drawTrial c.as c.s c.bk c.cc c.n c.p g
    g := g'
    match outcomes.findIdx? (· == o) with
    | some i => counts := counts.modify i (· + 1)
    | none => pure ()
  let mut ok := true
  let mut worst : Float := 0
  for i in [0:outcomes.length] do
    let o := outcomes[i]!
    let p := toF (Dist.prob exact (· == o))
    let f := counts[i]!.toFloat / draws.toFloat
    let se := Float.sqrt (p * (1 - p) / draws.toFloat)
    let z := if se == 0 then (if f == 0 then 0 else 1000) else (f - p).abs / se
    if z > worst then worst := z
    if z > 4 then ok := false
  let total := toF (Dist.mass exact)
  IO.println s!"{c.name}: exact mass {total}, worst |z| = {(worst * 100).round / 100} {if ok then "ok" else "FAIL"}"
  return ok

def main (args : List String) : IO UInt32 := do
  let draws := ((args.findSome? fun a => if a.startsWith "--draws=" then (a.drop 8).toString.toNat? else none)).getD 20000
  let mut allOk := true
  for c in cases do
    let ok ← checkCase c draws 7
    allOk := allOk && ok
  IO.println (if allOk then "all cases within 4 standard errors" else "SOME CASES FAILED")
  return (if allOk then 0 else 1)
