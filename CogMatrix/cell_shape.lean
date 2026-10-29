/-
Used by `gen_matrix.py`; not part of the library. `cellShape` reads a matrix
cell's statement: whether it is a law or the negation of one, which law,
which family, and whether the family's parameters are bound by the theorem
(a claim for every setting) or fixed (a claim for one setting).
-/

import Lean
import CogMatrix

open Lean Meta

def cellShape (n : Name) : MetaM String := do
  let some ci := (← getEnv).find? n | return s!"{n}|missing"
  forallTelescope ci.type fun _ body => do
    let (neg, p) := if body.isAppOfArity ``Not 1 then (true, body.appArg!) else (false, body)
    let law := p.getAppFn.constName?.getD .anonymous
    let mut ret : Option Expr := none
    for a in p.getAppArgs do
      if (← inferType a).getAppFn.isConstOf ``Cog.Retriever then ret := some a
    match ret with
    | none => return s!"{n}|{neg}|{law}|none|false"
    | some r => return s!"{n}|{neg}|{law}|{r.getAppFn.constName?.getD .anonymous}|{r.hasFVar}"
