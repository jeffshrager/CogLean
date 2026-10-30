/-
View selection by spreading activation, composed with view application.

Shrager (1987, §3.4.1) left view selection without a principled account:
views were suggested by key labels, by the device's behavior, or by the
current theory. Here selection is spreading activation (Collins & Loftus
1975, `Process/SpreadingActivation`) over one knowledge net that holds the
learner's theory and the views' associations: activation starts at the cue
(a key's label) and at the concepts the current theory uses, spreads along
`suggests` links, and a view is chosen in proportion to its activation. The
chosen view is then applied (`Process/ViewApplication`). The composition is
a mixture: the chance of a resulting theory is, summed over views, the
chance that view is chosen times the chance its application gives that
theory, the same shape as recognition followed by retrieval in MultiDigit.

A hypothetical device with a key labelled "+". "+" suggests a CALCULATING
view ("+" adds to the display), strength 1/2, and a PROGRAMMING view ("+"
appends a step), strength 1/4. *Memory* suggests PROGRAMMING, strength 1/2.

* `naive`: a learner whose theory has no memory reads "+" as adding with
  probability 2/3, as appending a step with probability 1/3.
* `primed`: a learner whose theory already has a memory (as after
  CODE.AND.STARTUP) reads it as appending a step with probability 3/5.

So the same cue brings in different knowledge, depending on what the
learner already knows. All strengths are illustrative.
-/

import CogLib.Process.SpreadingActivation

namespace ViewApplication.Selection

open Cog

inductive A
  | keyOp | plusKey | plus | plusAct | doSomething | doA | kOpType | arg
  | calcOp | addToDisplay | stepOp | appendStep
  | memCell | memoryObj | calculating | programming
  deriving DecidableEq

inductive Lbl | isa | kind | method | function | suggests | indicates
  deriving DecidableEq

open A

abbrev a := @Term.atom A
abbrev ap := @Term.app A
abbrev h := @Term.hole A

/-- What the learner knows about the "+" key: an operation that does something. -/
def naiveTheory : KNet A Lbl where
  isa := .isa
  links := [
    (a keyOp, .kind, a kOpType), (a keyOp, .function, ap doSomething [h arg]),
    (a plusKey, .isa, a keyOp), (a plusKey, .method, ap doA [a plus]),
    (a plusKey, .function, ap doSomething [a plusAct])]

/-- The same, with a memory in the theory. -/
def memoryTheory : KNet A Lbl :=
  { naiveTheory with links := naiveTheory.links ++ [(a memCell, .isa, a memoryObj)] }

/-- The two views. -/
def view : A → KNet A Lbl
  | calculating => ⟨[(a calcOp, .kind, a kOpType), (a calcOp, .function, ap addToDisplay [h arg])], .isa⟩
  | _ => ⟨[(a stepOp, .kind, a kOpType), (a stepOp, .function, ap appendStep [h arg])], .isa⟩

/-- Associations: what suggests which view. -/
def associations : List (Term A × Lbl × Term A) := [
  (a plus, .suggests, a calculating), (a plus, .suggests, a programming),
  (a memoryObj, .suggests, a programming)]

def strength : Term A × Lbl × Term A → Rat
  | (.atom plus, .suggests, .atom calculating) => 1 / 2
  | (.atom plus, .suggests, .atom programming) => 1 / 4
  | (.atom memoryObj, .suggests, .atom programming) => 1 / 2
  | _ => 0

def P : SAParams A Lbl := ⟨strength, 1⟩

/-- Sources: the cue, and the concepts the theory uses (its frames' types). -/
def sources (cue : A) (T : KNet A Lbl) : Sources A :=
  (a cue, 1) :: (T.links.filterMap fun e => if e.2.1 == T.isa then some (e.2.2, 1) else none)

/-- The net activation spreads over: the theory with the associations. -/
def net (T : KNet A Lbl) : KNet A Lbl := { T with links := T.links ++ associations }

/-- **Select a view by spreading activation, then apply it.** -/
def interpret (cue : A) (T : KNet A Lbl) : Dist (KNet A Lbl) :=
  Dist.bind (choose (net T) P (sources cue T) [calculating, programming]) fun v =>
    applyView ⟨.kind, .indicates⟩ (view v) T

/-- The "+" key read as adding, or as appending a step. -/
def reads (f : A) (G : KNet A Lbl) : Bool := G.slot plusKey .function == some (ap f [a plusAct])

/-- **Naive**: "+" adds with probability 2/3, appends a step with 1/3. -/
theorem naive : Dist.prob (interpret plus naiveTheory) (reads addToDisplay) = 2 / 3 ∧
    Dist.prob (interpret plus naiveTheory) (reads appendStep) = 1 / 3 := by
  decide +kernel

/-- **Primed by a memory**: "+" appends a step with probability 3/5. -/
theorem primed : Dist.prob (interpret plus memoryTheory) (reads appendStep) = 3 / 5 ∧
    Dist.prob (interpret plus memoryTheory) (reads addToDisplay) = 2 / 5 := by
  decide +kernel

end ViewApplication.Selection
