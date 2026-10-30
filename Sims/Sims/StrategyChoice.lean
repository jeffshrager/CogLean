/-
Simulating the distributions-of-associations model (Siegler & Shrager 1984)
with learning, as in the chapter's simulation (pp. 272-275).

One trial is drawn stage by stage, following `SC.trial`: retrieval up to the
search length, drawing each answer from the model's own `Cog.sample` and
stating it if it is `Cog.above` the criterion; else the backup, with the
model's own `SC.elaborate`; else counting, object by object as in `SC.count`.
Learning is the model's own `SC.strengthen`. `sc-check` compares these draws
with the exact `SC.trial` on small cases.

The environment, from the chapter:
* answers 1-12, every association initially .01 (p. 272);
* the 25 problems 1-5 + 1-5, presented in proportion to the parental input
  of Table 9.5 (parents out of 30), with a constant added to each percentage
  (fn. 13); the constant is not given, and `c = 12` reproduces the stated
  5.4% for 4 + 1 and at least 2% for every problem;
* the criterion drawn from .05-.99 (here in hundredths) and the search length
  from 1-3, on each trial (p. 273, item 2);
* on an ascending or tie problem, a momentary association to the second
  addend plus one (the counting-string prime, p. 272), of size `prime`;
* elaboration adds .05 (item 4).

Not given in the chapter, and so parameters: the prime's size, the increment
`inc`, and the counting errors `qs`, `qd`.
-/

import Sims.Sampling
import StrategyChoice

namespace Sims.SCSim

open Cog SC

/-- Answers 1-12. -/
def answers : List Answer := (List.range 12).map (· + 1)

/-- Draw a retrieval search: the stated answer, or none if exhausted (`Cog.search`). -/
def drawSearch (as : List Answer) (s : Answer → Rat) (cc : Rat) : Nat → StdGen → Option Answer × StdGen
  | 0, g => (none, g)
  | n + 1, g =>
    let (a, g) := drawDist (Dist.sample as s) g
    if above s cc a then (some a, g) else drawSearch as s cc n g

/-- Draw a count of `k` objects (`SC.count`): each skipped with probability
`qs`, counted twice with probability `qd`. -/
def drawCount (qs qd : Rat) : Nat → StdGen → Nat × StdGen
  | 0, g => (0, g)
  | k + 1, g =>
    let (r, g) := drawCount qs qd k g
    let (step, g) := drawDist [((0 : Nat), qs), (1, 1 - qs - qd), (2, qd)] g
    (r + step, g)

/-- Draw a trial (`SC.trial`), at a given criterion and search length. -/
def drawTrial (as : List Answer) (s : Answer → Rat) (bk : Backup) (cc : Rat) (n : Nat) (p : Problem)
    (g : StdGen) : (Strategy × Answer) × StdGen :=
  match drawSearch as s cc n g with
  | (some a, g) => ((.retrieval, a), g)
  | (none, g) =>
    let s' := elaborate s p.sum bk.e
    let (a, g) := drawDist (Dist.sample as s') g
    if above s' cc a then ((.fingers, a), g)
    else
      let (r, g) := drawCount bk.qs bk.qd p.sum g
      ((.countingFingers, r), g)

/-- Table 9.5: parents (out of 30) who presented `a + b`. -/
def parents (a b : Nat) : Nat :=
  match a, b with
  | 1, 1 => 15 | 1, 2 => 6 | 1, 3 => 1 | 1, 4 => 1 | 1, 5 => 0
  | 2, 1 => 14 | 2, 2 => 12 | 2, 3 => 1 | 2, 4 => 0 | 2, 5 => 0
  | 3, 1 => 14 | 3, 2 => 3 | 3, 3 => 0 | 3, 4 => 0 | 3, 5 => 0
  | 4, 1 => 9 | 4, 2 => 5 | 4, 3 => 0 | 4, 4 => 1 | 4, 5 => 1
  | 5, 1 => 4 | 5, 2 => 0 | 5, 3 => 1 | 5, 4 => 0 | 5, 5 => 3
  | _, _ => 0

def problems : List Problem :=
  (List.range 5).flatMap fun i => (List.range 5).map fun j => ⟨i + 1, j + 1⟩

/-- The presentation distribution: each problem's percentage of parental
input, plus the constant `c`. -/
def presentation (c : Rat) : Dist Problem :=
  let tot : Rat := ((problems.map fun p => parents p.a p.b).foldl (· + ·) 0 : Nat)
  problems.map fun p => (p, 100 * (parents p.a p.b : Rat) / tot + c)

structure Params where
  inc : Rat := 1 / 200
  prime : Rat := 1 / 20
  qs : Rat := 1 / 20
  qd : Rat := 1 / 20
  c : Rat := 12
  trials : Nat := 2000

/-- Associations: one table per problem, over answers 0-12. -/
abbrev Assoc := Array (Array Rat)

def idx (p : Problem) : Nat := (p.a - 1) * 5 + (p.b - 1)

def initAssoc : Assoc :=
  Array.replicate 25 ((List.range 13).toArray.map fun a => if 1 ≤ a then (1 : Rat) / 100 else 0)

/-- A problem's strengths, as a function (A1). -/
def strengths (assoc : Assoc) (p : Problem) : Answer → Rat := fun a => (assoc.getD (idx p) #[]).getD a 0

/-- The counting-string prime, added for the trial only. -/
def primed (P : Params) (s : Answer → Rat) (p : Problem) : Answer → Rat :=
  if p.a ≤ p.b then fun x => s x + (if x = p.b + 1 then P.prime else 0) else s

instance : Inhabited Problem := ⟨⟨1, 1⟩⟩

instance : Inhabited Strategy := ⟨.retrieval⟩

/-- One learning trial: present a problem, draw a criterion and search
length, draw the trial, strengthen the answer stated (`SC.strengthen`). -/
def learnTrial (P : Params) (assoc : Assoc) (g : StdGen) : Assoc × StdGen :=
  let (p, g) := drawDist (presentation P.c) g
  let (k, g) := drawNat 5 99 g
  let cc : Rat := (k : Rat) / 100
  let (n, g) := drawNat 1 3 g
  let s := strengths assoc p
  let ((_, a), g) := drawTrial answers (primed P s p) ⟨1 / 20, P.qs, P.qd⟩ cc n p g
  let s' := strengthen s P.inc p.sum a
  (assoc.set! (idx p) ((List.range 13).toArray.map s'), g)

/-- A learning phase of `P.trials` trials from the initial associations. -/
def learn (P : Params) (seed : Nat) : Assoc := Id.run do
  let mut assoc := initAssoc
  let mut g := mkStdGen seed
  for _ in [0:P.trials] do
    let (a', g') := learnTrial P assoc g
    assoc := a'
    g := g'
  return assoc

/-- The strength at the correct answer, and its share of the total over 1-12. -/
def peakShare (s : Answer → Rat) (p : Problem) : Rat × Rat :=
  let total := (answers.map s).foldl (· + ·) 0
  (s p.sum, s p.sum / total)

end Sims.SCSim
