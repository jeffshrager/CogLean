/-
The paper's worked example (Smith et al. 1988, Figs. 1–4), reproduced
exactly: the apple prototype, a red apple `I1`, a brown apple `I2`, and a
red but bumpy apple `I3`, with `a = b = c = 1` and a boost of 2.

The paper rounds: 21, −54, 2.5, 66, −114. The exact values are 85/4,
−215/4, 5/2, 265/4, −455/4. Our copy of the figures is partly illegible;
the sums in the text fix the totals (color 30, shape 20, texture 30), and for
these instances any split of the non-modal votes gives the same similarities.
-/

import Concepts.Phenomena

namespace Concepts.Apple

open Cog

inductive Attr | color | shape | texture
  deriving DecidableEq

inductive Val | red | green | brown | round | square | cyl | smooth | rough | bumpy
  deriving DecidableEq

def S : Schema Attr Val where
  attrs := [.color, .shape, .texture]
  vals
    | .color => [.red, .green, .brown]
    | .shape => [.round, .square, .cyl]
    | .texture => [.smooth, .rough, .bumpy]

def apple : Proto Attr Val where
  diag
    | .color => 1
    | .shape => 1 / 2
    | .texture => 1 / 4
  votes
    | .color, .red => 25
    | .color, .green => 5
    | .shape, .round => 15
    | .shape, .square => 5
    | .texture, .smooth => 25
    | .texture, .rough => 5
    | _, _ => 0

/-- As many votes per attribute as the prototype has there. -/
def n : Attr → Rat
  | .color => 30
  | .shape => 20
  | .texture => 30

def inst (c s t : Val) : Inst Attr Val :=
  Inst.pure (fun | .color => c | .shape => s | .texture => t) n

def I1 := inst .red .round .smooth
def I2 := inst .brown .round .smooth
def I3 := inst .red .round .bumpy

def Q : Params := ⟨⟨1, 1, 1⟩, 2, 0, 1⟩

def redApple := combine Q S .color .red apple
def brownApple := combine Q S .color .brown apple

/-- Fig. 1: typicality in *apple*. -/
theorem fig1 : typicality Q S apple I1 = 85 / 4 ∧ typicality Q S apple I2 = -215 / 4 ∧
    typicality Q S apple I3 = 5 / 2 := by
  decide +kernel

/-- Figs. 3–4: typicality in *red apple* and *brown apple*. -/
theorem fig3_fig4 : typicality Q S redApple I1 = 265 / 4 ∧ typicality Q S redApple I2 = -455 / 4 ∧
    typicality Q S brownApple I2 = 265 / 4 ∧ typicality Q S brownApple I1 = -455 / 4 := by
  decide +kernel

/-- The conjunction effect is larger for the incompatible conjunction
(p. 495): 120 against 45. -/
theorem incompatible_larger :
    typicality Q S brownApple I2 - typicality Q S apple I2 = 120 ∧
      typicality Q S redApple I1 - typicality Q S apple I1 = 45 := by
  decide +kernel

end Concepts.Apple
