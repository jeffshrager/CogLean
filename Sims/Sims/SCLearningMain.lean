/-
`lake exe sc-learning [--runs=N] [--trials=N] [--inc=r] [--prime=r] [--qs=r] [--qd=r] [--c=r] [--seed=N]`
`lake exe sc-learning --sweep [--runs=N]`

Runs the learning phase of Siegler & Shrager's simulation `runs` times and
reports, for the six problems of Fig. 9.8, the mean strength at the correct
answer (the peak) and its mean share of the total, beside the chapter's
values. Rationals are given as `n/d` or decimals.
-/

import Sims.StrategyChoice

open Sims Sims.SCSim SC

def parseRat (s : String) : Option Rat :=
  match s.splitOn "/" with
  | [n, d] => do let n ← n.toNat?; let d ← d.toNat?; if d = 0 then none else some ((n : Rat) / d)
  | [x] => match x.splitOn "." with
    | [i] => i.toNat?.map (fun n => (n : Rat))
    | [i, f] => do
      let iv ← (if i = "" then some 0 else i.toNat?)
      let fv ← f.toNat?
      some ((iv : Rat) + (fv : Rat) / ((10 ^ f.length : Nat) : Rat))
    | _ => none
  | _ => none

def getArg (args : List String) (key : String) : Option String :=
  args.findSome? fun a => if a.startsWith s!"--{key}=" then some (a.drop (key.length + 3)).toString else none

def fmt (r : Float) : String :=
  let x := (r * 100).round / 100
  toString x

def toF (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

/-- The targets of Fig. 9.8 (pp. 273-275): problem, peak, share. -/
def targets : List (Problem × Float × Float) :=
  [(⟨1, 4⟩, 0.67, 0.77), (⟨2, 3⟩, 0.37, 0.46), (⟨4, 1⟩, 0.80, 0.76), (⟨3, 2⟩, 0.51, 0.69),
   (⟨3, 4⟩, 0.39, 0.50), (⟨4, 5⟩, 0.32, 0.43)]

/-- Mean peak and share over `runs` seeds, for each target problem. -/
def summarize (P : Params) (runs seed : Nat) : List (Problem × Float × Float) := Id.run do
  let mut sums : Array (Float × Float) := Array.replicate targets.length (0, 0)
  for r in [0:runs] do
    let assoc := learn P (seed + r)
    for i in [0:targets.length] do
      let (p, _, _) := targets[i]!
      let (pk, sh) := peakShare (strengths assoc p) p
      let (a, b) := sums[i]!
      sums := sums.set! i (a + toF pk, b + toF sh)
  return (List.range targets.length).map fun i =>
    let (p, _, _) := targets[i]!
    let (a, b) := sums[i]!
    (p, a / runs.toFloat, b / runs.toFloat)

/-- Mean absolute difference from the chapter's peaks and shares. -/
def distance (res : List (Problem × Float × Float)) : Float :=
  let ds := (res.zip targets).map fun ((_, pk, sh), (_, tp, ts)) => (pk - tp).abs + (sh - ts).abs
  ds.foldl (· + ·) 0 / (2 * targets.length.toFloat)

def report (P : Params) (runs seed : Nat) : IO Unit := do
  let res := summarize P runs seed
  IO.println s!"inc={toF P.inc} prime={toF P.prime} qs={toF P.qs} qd={toF P.qd} c={toF P.c} trials={P.trials} runs={runs}"
  IO.println "problem  peak (chapter)  share (chapter)"
  for ((p, pk, sh), (_, tp, ts)) in res.zip targets do
    IO.println s!"{p.a}+{p.b}      {fmt pk} ({tp})       {fmt sh} ({ts})"
  IO.println s!"mean |difference| = {fmt (distance res)}"

def main (args : List String) : IO Unit := do
  let runs := ((getArg args "runs").bind String.toNat?).getD 20
  let seed := ((getArg args "seed").bind String.toNat?).getD 1
  let base : Params := {}
  let P : Params := {
    inc := ((getArg args "inc").bind parseRat).getD base.inc
    prime := ((getArg args "prime").bind parseRat).getD base.prime
    qs := ((getArg args "qs").bind parseRat).getD base.qs
    qd := ((getArg args "qd").bind parseRat).getD base.qd
    c := ((getArg args "c").bind parseRat).getD base.c
    trials := ((getArg args "trials").bind String.toNat?).getD base.trials }
  if args.contains "--sweep" then
    IO.println "inc     prime   mean |difference| from Fig. 9.8 (peaks and shares)"
    for inc in [(1 : Rat) / 400, 1 / 250, 1 / 200, 1 / 150, 1 / 100] do
      for prime in [(1 : Rat) / 100, 1 / 50, 1 / 20, 1 / 10, 1 / 5] do
        let Q := { P with inc := inc, prime := prime }
        IO.println s!"{fmt (toF inc * 1000)}e-3  {toF prime}    {fmt (distance (summarize Q runs seed))}"
  else
    report P runs seed
