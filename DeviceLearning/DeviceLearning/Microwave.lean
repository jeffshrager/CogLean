/-
A microwave oven, a learner's initial theory of it, and two views.

All of this is task data, an illustrative design; the processes are
CogLib's (`Process/TheoryExecution`, `Process/ViewApplication`).

**The device.** Keys: TIME COOK, CLOCK, the digits 9 and 0, START. After
TIME COOK, the digits are a cooking time, read as minutes and seconds with
seconds allowed past 59: 9 0 START cooks for 90 seconds. After CLOCK, the
digits are a time of day, hours and minutes: 9 0 is not a valid time.

**The learner's theory** (Shrager 1987's representation): the digit keys
and START are understood (operation types of kind `kKnown`); TIME COOK and
CLOCK are instances of an operation type whose function is unknown
(`doSomething`), of kind `kSetting`.

**Views**, each one operation type of kind `kSetting`:
* SET-A-TIME: such a key sets a time of day (`setTime`);
* DURATION: such a key sets a duration (`setDuration`).
Applying a view matches the theory's unknown operation type to the view's
(the only one of that kind), so both keys are re-interpreted.

**Predictions** read each pressed key's function and apply its
denotation (`den`): `setTime` and `setDuration` set how digits will be
read, `appendDigit` adds a digit, `beginCook` reports the outcome.
`doSomething` has no denotation, so the initial theory predicts nothing.
-/

import CogLib.Process.TheoryExecution
import CogLib.Process.TypeSplit

namespace DeviceLearning

open Cog

inductive A
  | tcKey | clkKey | d9 | d0 | startKey
  | modeOp | digitOp | startOp | setOp | durOp
  | kSetting | kKnown
  | doSomething | setTime | setDuration | appendDigit | beginCook
  | tcAct | clkAct | nine | zero | goAct | arg
  | enterNumber | timeOfDay | durationM | modeOpB
  deriving DecidableEq, Repr

inductive Lbl | isa | kind | function | indicates | meaning
  deriving DecidableEq, Repr

open A

abbrev a := @Term.atom A
abbrev ap := @Term.app A
abbrev h := @Term.hole A

/-- What a sequence of key presses leads to. -/
inductive Obs
  | nothing
  | invalid
  | clockSet (hhmm : Nat)
  | cooks (secs : Nat)
  deriving DecidableEq, Repr

/-- How the digits are being read. -/
inductive Mode | idle | clock | duration
  deriving DecidableEq, Repr

/-- The device state as the learner tracks it: the reading of the digits,
the digits entered, the outcome. -/
abbrev St := Mode × List Nat × Obs

def s0 : St := (.idle, [], .nothing)

/-- The number the digits spell. -/
def number (ds : List Nat) : Nat := ds.foldl (fun n d => 10 * n + d) 0

/-- What START does, given how the digits are read. -/
def outcome : Mode → List Nat → Obs
  | .idle, _ => .nothing
  | .clock, ds => if number ds % 100 < 60 then .clockSet (number ds) else .invalid
  | .duration, ds => .cooks (number ds / 100 * 60 + number ds % 100)

/-- Denotations of the function terms. -/
def den : Term A → St → Option St
  | .app setTime _, (_, _, o) => some (.clock, [], o)
  | .app setDuration _, (_, _, o) => some (.duration, [], o)
  | .app appendDigit [.atom nine], (m, ds, o) => some (m, ds ++ [9], o)
  | .app appendDigit [.atom zero], (m, ds, o) => some (m, ds ++ [0], o)
  | .app beginCook _, (m, ds, _) => some (m, ds, outcome m ds)
  | _, _ => none

/-- The device itself: TIME COOK reads a duration, CLOCK a time of day. -/
def device (keys : List A) : Obs :=
  (keys.foldl (fun (s : St) k => match k, s with
    | tcKey, (_, _, o) => (.duration, [], o)
    | clkKey, (_, _, o) => (.clock, [], o)
    | d9, (m, ds, o) => (m, ds ++ [9], o)
    | d0, (m, ds, o) => (m, ds ++ [0], o)
    | startKey, (m, ds, _) => (m, ds, outcome m ds)
    | _, s => s) s0).2.2

/-- The learner's initial theory. -/
def theory0 : KNet A Lbl where
  isa := .isa
  links := [
    (a modeOp, .kind, a kSetting), (a modeOp, .function, ap doSomething [h arg]),
    (a tcKey, .isa, a modeOp), (a tcKey, .function, ap doSomething [a tcAct]),
    (a clkKey, .isa, a modeOp), (a clkKey, .function, ap doSomething [a clkAct]),
    (a digitOp, .kind, a kKnown), (a digitOp, .function, ap appendDigit [h arg]),
    (a d9, .isa, a digitOp), (a d9, .function, ap appendDigit [a nine]),
    (a d0, .isa, a digitOp), (a d0, .function, ap appendDigit [a zero]),
    (a startOp, .kind, a kKnown), (a startOp, .function, ap beginCook [h arg]),
    (a startKey, .isa, a startOp), (a startKey, .function, ap beginCook [a goAct])]

/-- The SET-A-TIME view. -/
def setView : KNet A Lbl :=
  ⟨[(a setOp, .kind, a kSetting), (a setOp, .function, ap setTime [h arg])], .isa⟩

/-- The DURATION view. -/
def durView : KNet A Lbl :=
  ⟨[(a durOp, .kind, a kSetting), (a durOp, .function, ap setDuration [h arg])], .isa⟩

def K : VAConfig Lbl := ⟨.kind, .indicates⟩

/-- What a theory predicts for a key sequence. -/
def predicts (T : KNet A Lbl) (keys : List A) : Option Obs :=
  (predict Lbl.function den T keys s0).map (·.2.2)

/-- Cooking for 90 seconds, and setting the clock to 90. -/
def cook90 : List A := [tcKey, d9, d0, startKey]
def clock90 : List A := [clkKey, d9, d0, startKey]

/-! ### Decomposed views

SET-A-TIME and DURATION, broken into parts: SET-A-NUMBER says the key
enters a number; NUMBER-IS-A-TIME and NUMBER-IS-A-DURATION say what the
number means, as a `meaning` slot of the key's type. Each view mentions one
slot of the type `modeOp`, so view application matches it by identity and
keeps the slots it does not mention (`merge_keeps_unmentioned`): applied in
turn, they build an interpretation up. -/

/-- SET-A-NUMBER. -/
def numberView : KNet A Lbl :=
  ⟨[(a modeOp, .kind, a kSetting), (a modeOp, .function, ap enterNumber [h arg])], .isa⟩

/-- NUMBER-IS-A-TIME. -/
def timeMView : KNet A Lbl := ⟨[(a modeOp, .kind, a kSetting), (a modeOp, .meaning, a timeOfDay)], .isa⟩

/-- NUMBER-IS-A-DURATION. -/
def durMView : KNet A Lbl := ⟨[(a modeOp, .kind, a kSetting), (a modeOp, .meaning, a durationM)], .isa⟩

/-- Denotations reading the key's type: entering a number sets how the
digits are read from what the type says a number means; with no meaning,
nothing is predicted. -/
def den2 (slots : Lbl → Option (Term A)) : Term A → St → Option St
  | .app A.enterNumber _, (_, _, o) => match slots .meaning with
    | some (.atom A.timeOfDay) => some (.clock, [], o)
    | some (.atom A.durationM) => some (.duration, [], o)
    | _ => none
  | f, s => den f s

/-- The theory-aware denotation: `den2` on the slots of the acting key's type. -/
def denT (T : KNet A Lbl) (k : A) (f : Term A) (s : St) : Option St :=
  den2 (fun l => (T.parent k).bind fun p => T.slot p l) f s

theorem denT_parentReader : ParentReader denT := ⟨den2, fun _ _ _ _ => rfl⟩

/-- What a theory predicts, reading types. -/
def predicts2 (T : KNet A Lbl) (keys : List A) : Option Obs :=
  (predictT Lbl.function denT T keys s0).map (·.2.2)

/-- **Without a split, never both.** If TIME COOK and CLOCK have the same type
and both enter a number, the theory predicts 9 0 START alike after either,
so it cannot predict both cooking for 90 seconds and an invalid time. This
holds for every theory of that form (`same_parent_same_reading`,
`predictT_head_congr`). -/
theorem never_both_shared (T : KNet A Lbl) (h : T.parent tcKey = T.parent clkKey) (x y : Term A)
    (hx : T.slot tcKey .function = some (ap enterNumber [x]))
    (hy : T.slot clkKey .function = some (ap enterNumber [y])) :
    ¬ (predicts2 T cook90 = some (device cook90) ∧ predicts2 T clock90 = some (device clock90)) := by
  have hden : ∀ s, denT T tcKey (ap enterNumber [x]) s = denT T clkKey (ap enterNumber [y]) s := by
    intro s
    rw [same_parent_same_reading denT denT_parentReader T tcKey clkKey h]
    obtain ⟨m, ds, o⟩ := s
    rfl
  have heq : predicts2 T cook90 = predicts2 T clock90 := by
    unfold predicts2 cook90 clock90
    rw [predictT_head_congr _ _ T tcKey clkKey _ _ _ _ hx hy (hden _)]
  intro ⟨h1, h2⟩
  rw [heq, h2] at h1
  exact absurd h1 (by decide)

end DeviceLearning
