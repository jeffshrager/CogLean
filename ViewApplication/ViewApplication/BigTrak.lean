/-
The paper's worked example (Shrager 1987, §3.5), as data for CogLib's
view application: applying the view CODE.AND.STARTUP (Table 2) to an
initial theory of the BigTrak (Table 1) gives the theory of Table 4.

Paraphrased slot values are terms: "Do each user-action in some
code-sequence" is the pattern `doEachIn [hole codeSeq]`, and Forward-9's
"Do each user-action in Sequence-1" is `doEachIn [seq1]`; "Do a
Real-World-Action" is `doAct [hole rwa]`; "Set the program-plan to a
Real-World-Action" is `setPlan [hole rwa]`. The GO-keypress's "press a
button whose label indicates CODE.AND.STARTUP" is `press [hole casLabel]`,
and the device description (the input to IE, §3.1) records that GO's label
indicates CODE.AND.STARTUP.

Nothing here is specific to view application: all five steps are CogLib's.
The theory's Action-operation can be matched to either of the view's
operation types, at random (p. 261). With probability 1/2 it is matched to
Memory-operation, and the result is Table 4 (`table4_reproduced`). Instance
names are the theory's (the paper renames Forward-9 New-Forward-Operation).
-/

import CogLib.Process.ViewApplication

namespace ViewApplication.BigTrak

open Cog

inductive A
  | script1 | actionOp | forward9 | codeSeq | seq1
  | memOp | immOp | startupOp | keyPress | goKeypress | programPlan | actionPlan
  | kScript | kOpType | kObjType
  | doEachIn | doAct | setPlan | doA | doEachActIn | listOf | press | steps
  | moveFwd9 | rwa | userAction | casLabel
  | clr | fwd | nine | go
  deriving DecidableEq

inductive Lbl | isa | kind | method | function | struct | indicates
  deriving DecidableEq

open A Term

abbrev a := @Term.atom A
abbrev ap := @Term.app A
abbrev h := @Term.hole A

/-- Table 1: an initial theory of BigTrak, with the device's key labels. -/
def table1 : KNet A Lbl where
  isa := .isa
  links := [
    (a script1, .kind, a kScript), (a script1, .method, ap steps [a actionOp]),
    (a actionOp, .kind, a kOpType), (a actionOp, .method, ap doEachIn [h codeSeq]),
    (a actionOp, .function, ap doAct [h rwa]),
    (a forward9, .isa, a actionOp), (a forward9, .method, ap doEachIn [a seq1]),
    (a forward9, .function, ap doAct [a moveFwd9]),
    (a codeSeq, .kind, a kObjType), (a codeSeq, .struct, ap listOf [a userAction]),
    (a seq1, .isa, a codeSeq), (a seq1, .struct, ap press [a clr, a fwd, a nine, a go]),
    (a go, .indicates, a casLabel)]

/-- Table 2: the CODE.AND.STARTUP view. -/
def table2 : KNet A Lbl where
  isa := .isa
  links := [
    (a memOp, .kind, a kOpType), (a memOp, .method, ap doEachIn [h codeSeq]),
    (a memOp, .function, ap setPlan [h rwa]),
    (a immOp, .kind, a kOpType), (a immOp, .method, ap doA [a keyPress]),
    (a startupOp, .isa, a immOp), (a startupOp, .method, ap doA [a goKeypress]),
    (a startupOp, .function, ap doEachActIn [a programPlan]),
    (a codeSeq, .kind, a kObjType), (a codeSeq, .struct, ap listOf [a keyPress]),
    (a keyPress, .kind, a kObjType),
    (a goKeypress, .isa, a keyPress), (a goKeypress, .struct, ap press [h casLabel]),
    (a programPlan, .isa, a actionPlan), (a programPlan, .struct, ap listOf [a rwa])]

def K : VAConfig Lbl := ⟨.kind, .indicates⟩

/-- Table 4: the theory after applying CODE.AND.STARTUP. -/
def table4 : List (Term A × Lbl × Term A) := [
  (a script1, .kind, a kScript), (a script1, .method, ap steps [a memOp, a immOp]),
  (a memOp, .kind, a kOpType), (a memOp, .method, ap doEachIn [h codeSeq]),
  (a memOp, .function, ap setPlan [h rwa]),
  (a forward9, .isa, a memOp), (a forward9, .method, ap doEachIn [a seq1]),
  (a forward9, .function, ap setPlan [a moveFwd9]),
  (a immOp, .kind, a kOpType), (a immOp, .method, ap doA [a keyPress]),
  (a startupOp, .isa, a immOp), (a startupOp, .method, ap doA [a goKeypress]),
  (a startupOp, .function, ap doEachActIn [a programPlan]),
  (a codeSeq, .kind, a kObjType), (a codeSeq, .struct, ap listOf [a keyPress]),
  (a seq1, .isa, a codeSeq), (a seq1, .struct, ap press [a clr, a fwd, a nine]),
  (a keyPress, .kind, a kObjType),
  (a goKeypress, .isa, a keyPress), (a goKeypress, .struct, ap press [a go]),
  (a programPlan, .isa, a actionPlan), (a programPlan, .struct, ap listOf [a rwa]),
  (a go, .indicates, a casLabel)]

/-- The same links, in any order. -/
def sameLinks (G : KNet A Lbl) (ls : List (Term A × Lbl × Term A)) : Bool :=
  G.links.all (· ∈ ls) && ls.all (· ∈ G.links)

/-- **Table 4, reproduced**: applying CODE.AND.STARTUP to Table 1 gives Table 4
with probability 1/2 (when Action-operation is matched to Memory-operation). -/
theorem table4_reproduced : Dist.prob (applyView K table2 table1) (sameLinks · table4) = 1 / 2 := by
  decide +kernel

/-- Two outcomes, equally likely. -/
theorem two_outcomes : (applyView K table2 table1).length = 2 ∧
    Dist.mass (applyView K table2 table1) = 1 := by
  decide +kernel

end ViewApplication.BigTrak
