/-
Learning the microwave with decomposed views and type splitting
(differentiation). EPAM's net only: the results here concern representation,
and hold for any memory (`Process/TypeSplit`, `Process/ViewComposition`).

**Views in parts** (`Microwave.lean`): SET-A-NUMBER, NUMBER-IS-A-TIME and
NUMBER-IS-A-DURATION, each one slot of the keys' type. Interpreting a key
takes two of them.

**Cues.** The key's label, the display, and the digit keys. Six features:
a time word, a cooking word, a clock word, a counting-down display, a
colon, digits. Prior knowledge (illustrative): a VCR's SET TIME (stored with
NUMBER-IS-A-TIME), a kitchen timer (NUMBER-IS-A-DURATION), a calculator
keypad (SET-A-NUMBER). EPAM's net learns the three, noticing digits first,
then the countdown, the colon, and the words.

**Episodes**: TIME COOK 9 0 START (cooks 90 seconds), then CLOCK 9 0 START
(invalid), then TIME COOK 9 0 START again.

**Learners** (`viewSplitReviser`): a retrieved view is aimed at the failing
key's type; a split is offered when revising that type would break an
episode already explained. One learner may split; the other may not.
-/

import DeviceLearning.Microwave
import CogLib.Process.ViewRevision
import CogLib.Process.DiscriminationLearning
import CogLib.Phenomena.TheoryChange

namespace DeviceLearning.Diff

open Cog A

inductive Cue
  | label (k : A)
  | display
  | digits
  deriving DecidableEq, Repr

/-- Features: time word, cooking word, clock word, countdown, colon, digits. -/
def code : Cue → Item
  | .label tcKey => [true, true, false, false, false, false]
  | .label clkKey => [true, false, true, false, false, false]
  | .display => [false, false, false, true, true, false]
  | .digits => [false, false, false, false, false, true]
  | .label _ => [false, false, false, false, false, false]

def setTimeItem : Item := [true, false, true, false, true, false]
def timerItem : Item := [true, false, false, true, true, false]
def keypadItem : Item := [false, false, false, false, false, true]

/-- The view stored with each, and its frame. -/
def viewOf (y : Item) : Option (KNet A Lbl × A) :=
  if y = setTimeItem then some (timeMView, modeOp)
  else if y = timerItem then some (durMView, modeOp)
  else if y = keypadItem then some (numberView, modeOp)
  else none

def order : NoticingOrder := [5, 3, 4, 0, 1, 2]

def net : Net :=
  (((Net.leaf none).learn order setTimeItem).learn order timerItem).learn order keypadItem

/-- The key whose type a failed episode revises: its first key. -/
def target (e : Episode A Obs) : Option A := e.1.head?

/-- Cues an episode offers: the digits, the key's label, and the display if
something is cooking. -/
def vcues (e : Episode A Obs) : List Cue :=
  [.digits] ++ (e.1.head?.map Cue.label).toList ++
    (match e.2 with | .cooks _ => [.display] | _ => [])

/-- The learner; `split` says whether it may split types. -/
abbrev learner (split : Bool) :=
  viewSplitReviser K code (fun (N : Net) => N.retrieve) viewOf predicts2 target vcues
    (fun _ _ => modeOpB) split true

abbrev LS := LState (KNet A Lbl) Net A Obs (SCue Cue A) (Option (Item × A))

def eps : List (Episode A Obs) :=
  [(cook90, device cook90), (clock90, device clock90), (cook90, device cook90)]

def start : LS := ⟨theory0, net, eps, [], [], []⟩

/-- The final theory predicts both episodes. -/
def both (s : LS) : Bool :=
  predicts2 s.theory cook90 == some (device cook90) && predicts2 s.theory clock90 == some (device clock90)

/-- The meanings brought in for type `p`, in order (what a number means;
SET-A-NUMBER is left out). -/
def meaningsOn (p : A) (s : LS) : List Item :=
  s.adopted.filterMap fun b => b.bind fun (y, q) => if q == p && y != keypadItem then some y else none

/-- Whether the session split a type. -/
def didSplit (s : LS) : Bool := s.theory.parent clkKey != s.theory.parent tcKey

/-! ### Composing views -/

/-- What a theory predicts for cooking 90 seconds. -/
def cookPred (d : Dist (KNet A Lbl)) : List (Option Obs) := d.map fun T => predicts2 T.1 cook90

/-- Apply two views in turn. -/
def twice (V W : KNet A Lbl) : Dist (KNet A Lbl) := Dist.bind (applyView K V theory0) (applyView K W)

/-- **One view is not enough.** No single part, applied to the initial theory,
predicts what TIME COOK 9 0 START does: SET-A-NUMBER leaves the number's
meaning open, and a meaning alone leaves the key's function unknown. -/
theorem one_view_not_enough :
    cookPred (applyView K numberView theory0) = [none] ∧
      cookPred (applyView K timeMView theory0) = [none] ∧
      cookPred (applyView K durMView theory0) = [none] := by
  decide +kernel

/-- **Two views compose, in either order.** SET-A-NUMBER with
NUMBER-IS-A-DURATION predicts cooking for 90 seconds, whichever is applied
first; with NUMBER-IS-A-TIME, an invalid time, whichever first. (Instances
of the commutation law that `Process/ViewComposition` leaves open in
general.) -/
theorem two_views_compose :
    cookPred (twice numberView durMView) = [some (.cooks 90)] ∧
      cookPred (twice durMView numberView) = [some (.cooks 90)] ∧
      cookPred (twice numberView timeMView) = [some .invalid] ∧
      cookPred (twice timeMView numberView) = [some .invalid] := by
  decide +kernel

/-- **A revision keeps the right part.** Replacing NUMBER-IS-A-TIME by
NUMBER-IS-A-DURATION keeps SET-A-NUMBER: the key still enters a number, and
now predicts cooking (`merge_keeps_unmentioned`). -/
theorem revision_keeps_number :
    (Dist.bind (twice numberView timeMView) (applyView K durMView)).all
      (fun T => T.1.slot tcKey .function == some (ap enterNumber [a tcAct]) &&
        predicts2 T.1 cook90 == some (.cooks 90)) := by
  decide +kernel

/-! ### Sessions -/

/-- EPAM's net: both labels call up the VCR's SET TIME, the display the
kitchen timer, the digits the keypad. -/
theorem net_facts :
    net.select (code (.label tcKey)) = some setTimeItem ∧
      net.select (code (.label clkKey)) = some setTimeItem ∧
      net.select (code .display) = some timerItem ∧ net.select (code .digits) = some keypadItem := by
  decide +kernel

/-- **Without splitting: never both, and oscillation.** A learner that may not
split never ends knowing both keys (as `never_both_shared` requires). Of
the 5/6 that finish, every one oscillated between meanings on the shared
type: the clock's meaning displaced cooking's, and cooking's came back. -/
theorem no_split_session :
    Dist.prob ((learner false).session 12 start) both = 0 ∧
      Dist.prob ((learner false).session 12 start) (fun s => s.todo.isEmpty) = 5 / 6 ∧
      Dist.prob ((learner false).session 12 start)
        (fun s => Phenomena.oscillates (meaningsOn modeOp s)) = 5 / 6 := by
  decide +kernel

/-- **With conflict-driven splitting: both, without oscillation.** Every
learner that finishes (5/6) has split the shared type and knows both keys;
none oscillates. The other 1/6 brought in a wrong meaning last on the first
episode and ran out of cues. -/
theorem split_session :
    Dist.prob ((learner true).session 12 start) both = 5 / 6 ∧
      Dist.prob ((learner true).session 12 start) (fun s => s.todo.isEmpty) = 5 / 6 ∧
      Dist.prob ((learner true).session 12 start) (fun s => s.todo.isEmpty && !both s) = 0 ∧
      Dist.prob ((learner true).session 12 start) didSplit = 5 / 6 ∧
      Dist.prob ((learner true).session 12 start)
        (fun s => Phenomena.oscillates (meaningsOn modeOp s) ||
          Phenomena.oscillates (meaningsOn modeOpB s)) = 0 := by
  decide +kernel

end DeviceLearning.Diff
