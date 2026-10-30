/-
Selective modification (Smith, Osherson, Rips & Keane 1988), with graded
membership by the threshold model (Hampton 2007).

* SO1 (pp. 488–489): a concept is a prototype: attributes, values of each,
  the salience of each value ("votes"), the diagnosticity of each
  attribute (`Proto`, `Schema`).
* SO2 (p. 489): an instance is represented like a prototype, without
  diagnosticity; in the paper's examples all its votes on an attribute are
  on one value, as many as the prototype has on that attribute
  (`Inst.pure`).
* SO3 (pp. 489–491, Eqs. 1–2): typicality is similarity by Tversky's
  contrast rule, attribute by attribute, each vote one feature, each
  count multiplied by the prototype's diagnosticity (`sim`).
* SO4 (pp. 492–493): an adjective naming one value of one attribute
  selects that attribute of the noun, shifts all its votes to the value,
  and boosts its diagnosticity, by 2 in the paper (`modify`).
* H1 (Hampton 2007, pp. 360, 365, Eqs. 6, 8): membership is a
  nondecreasing function of the same similarity, 0 below a bound, 1 above
  another, graded between (`thresholdM`). Not part of SO; it is what makes
  membership, and so over-extension, a prediction.

The free parameters are the contrast weights `a`, `b`, `c`, the boost, the
bounds of H1, and, for each concept, its prototype.
-/

import CogLib.Process.Combination
import CogLib.Phenomena.Combination

namespace Concepts

open Cog

/-- The parameters of the model. -/
structure Params where
  K : Contrast
  boost : Rat
  SL : Rat
  SH : Rat

variable {A V : Type} [DecidableEq A] [DecidableEq V]

/-- SO4: the combination of an adjective (value `v0` of attribute `i0`) with a noun. -/
def combine (Q : Params) (S : Schema A V) (i0 : A) (v0 : V) (noun : Proto A V) : Proto A V :=
  modify S Q.boost i0 v0 noun

/-- SO3: typicality. -/
def typicality (Q : Params) (S : Schema A V) (P : Proto A V) (I : Inst A V) : Rat := sim Q.K S P I

/-- H1: graded membership. -/
def membership (Q : Params) (S : Schema A V) (P : Proto A V) (I : Inst A V) : Rat :=
  thresholdM Q.SL Q.SH (sim Q.K S P I)

end Concepts
