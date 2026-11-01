/-
Learning the microwave: cues, two memories, and sessions.

**Cues and their codes.** A cue is a key's label or the display. Five
features: a time word, a cooking word, a clock word, a counting-down
display, a colon. TIME COOK has a time word and a cooking word; CLOCK a
time word and a clock word; the cooking display "1:30", counting down, has
the last two.

**What the learner already knows** (illustrative): a VCR's SET TIME key
(time word, clock word, a colon on its display), stored with the
SET-A-TIME view; and a kitchen timer (time word, counting down, a colon),
stored with the DURATION view.

**Memories.** EPAM's net learns the two, noticing the countdown first, then
the colon, then the words; it tests only the countdown. ACT-R's memory
studies the same two (mismatch penalty 1/2 over all five features, failure
weight 1/10).

**Learners** (`Process/TheoryRevision`, with the view-application reviser
of `Process/ViewRevision`): the episode is TIME COOK 9 0
START, which cooks for 90 seconds; the initial theory predicts nothing, so
the learner is at an impasse at once. A *two-cue* learner consults the
key's label and the display, each once per failure, in random order. A
*label-only* learner consults only the key's label, as often as it fails.
-/

import DeviceLearning.Microwave
import CogLib.Process.ViewRevision
import CogLib.Memory.Activation
import CogLib.Process.DiscriminationLearning
import CogLib.Phenomena.TheoryChange

namespace DeviceLearning

open Cog A

inductive Cue
  | label (k : A)
  | display
  deriving DecidableEq, Repr

/-- Features: time word, cooking word, clock word, countdown, colon. -/
def code : Cue → Item
  | .label tcKey => [true, true, false, false, false]
  | .label clkKey => [true, false, true, false, false]
  | .display => [false, false, false, true, true]
  | .label _ => [false, false, false, false, false]

/-- A VCR's SET TIME key, and a kitchen timer. -/
def setTimeItem : Item := [true, false, true, false, true]
def timerItem : Item := [true, false, false, true, true]

/-- The view stored with each. -/
def viewOf (y : Item) : Option (KNet A Lbl) :=
  if y = setTimeItem then some setView else if y = timerItem then some durView else none

/-- Countdown first, then the colon, then the words. -/
def order : NoticingOrder := [3, 4, 0, 1, 2]

/-- EPAM's net, after learning the two. -/
def net : Net := ((Net.leaf none).learn order setTimeItem).learn order timerItem

/-- ACT-R's parameters, and its memory after studying the two. -/
def P : ActParams := ⟨[0, 1, 2, 3, 4], 1 / 2, 1 / 10⟩
def mem : ActState := Act.study (Act.study ⟨0, []⟩ setTimeItem) timerItem

/-- The episode: TIME COOK 9 0 START, observed. -/
def ep : Episode A Obs := (cook90, device cook90)

/-- A learner with memory `retrieve`: the view-application reviser, with
predictions read off the theory (`predicts`, `Process/TheoryExecution`). -/
def learner {M : Type} (retrieve : M → Item → Dist (Option Item)) (cues : Episode A Obs → List Cue)
    (once : Bool) : Reviser (KNet A Lbl) M A Obs Cue (Option Item) :=
  viewReviser K code retrieve viewOf predicts cues once

/-- A learner's state. -/
abbrev LS (M : Type) := LState (KNet A Lbl) M A Obs Cue (Option Item)

/-- Consult the key's label and the display. -/
def twoCues (e : Episode A Obs) : List Cue := (e.1.head?.map Cue.label).toList ++ [.display]

/-- Consult only the key's label. -/
def labelOnly (e : Episode A Obs) : List Cue := (e.1.head?.map Cue.label).toList

/-- The learners. -/
abbrev epam2 := learner (fun (N : Net) => N.retrieve) twoCues true
abbrev act2 := learner (Act.retrieve P) twoCues true
abbrev epam1 := learner (fun (N : Net) => N.retrieve) labelOnly false
abbrev act1 := learner (Act.retrieve P) labelOnly false

/-- The start of a session. -/
def start {M : Type} (m : M) : LS M := ⟨theory0, m, [ep], [], []⟩

/-- The session's final theory predicts the episode. -/
def solved {M : Type} (s : LS M) : Bool := predicts s.theory cook90 == some (.cooks 90)

/-- The interpretations a session brought in, in order (retrievals that
called up nothing are not interpretations). -/
def views {M : Type} (s : LS M) : List Item := s.adopted.filterMap id

/-! ### Setting facts -/

/-- **EPAM's net confuses TIME COOK with a VCR's SET TIME.** It tests only the
countdown, so both key labels call up SET TIME, and the cooking display
calls up the kitchen timer. -/
theorem net_facts :
    net.select (code (.label tcKey)) = some setTimeItem ∧
      net.select (code (.label clkKey)) = some setTimeItem ∧
      net.select (code .display) = some timerItem := by
  decide +kernel

/-- **ACT-R's retrieval is graded.** TIME COOK calls up SET TIME with
probability 5/23 and the kitchen timer with 10/23 (equally similar, the
timer more recent), and nothing with 8/23. -/
theorem act_graded :
    Dist.prob (Act.retrieve P mem (code (.label tcKey))) (· == some setTimeItem) = 5 / 23 ∧
      Dist.prob (Act.retrieve P mem (code (.label tcKey))) (· == some timerItem) = 10 / 23 ∧
      Dist.prob (Act.retrieve P mem (code (.label tcKey))) (· == none) = 8 / 23 := by
  decide +kernel

/-- The view each interpretation gives: SET-A-TIME predicts that 90 is an
invalid time for either key; DURATION predicts cooking for 90 seconds for
either. The initial theory predicts nothing. -/
theorem view_predictions :
    predicts theory0 cook90 = none ∧
      (applyView K setView theory0).all (fun T => predicts T.1 cook90 == some .invalid) ∧
      (applyView K durView theory0).all (fun T => predicts T.1 cook90 == some (.cooks 90)) ∧
      device cook90 = .cooks 90 ∧ device clock90 = .invalid := by
  decide +kernel

/-! ### The confusion-error pattern, outside arithmetic -/

/-- The keys a cue's episode presses. -/
def keysOf : Cue → List A
  | .label clkKey => clock90
  | _ => cook90

/-- **Confident misinterpretation.** With EPAM's net, the TIME COOK label is
taken for SET TIME, as is the CLOCK label. Reading each label's episode off
the revised theory: CLOCK's is always predicted correctly, TIME COOK's
always wrongly, and neither leads to exploration. This is
`Phenomena.ConfusionErrorPattern`, the pattern stated for multi-digit
addition, here for a different mechanism (`view_confusion_pattern`). -/
theorem epam_confusion_pattern :
    Phenomena.ConfusionErrorPattern
      (vtrial K code net.retrieve viewOf theory0 (fun c T => predicts T (keysOf c))
        (fun _ => Dist.pure none))
      (RR.wholeWrong fun c => some (device (keysOf c))) RR.isWhole RR.isBackup
      (Cue.label tcKey) (Cue.label clkKey) :=
  view_confusion_pattern K code net.retrieve viewOf theory0 _ _ _ _ _ setTimeItem setView
    (by decide +kernel) (by decide +kernel) (by simp [viewOf]) (by decide +kernel)
    (by decide +kernel)

/-! ### Sessions -/

/-- **Perseveration follows from determinacy.** EPAM's net has the law of
determinacy (it retrieves deterministically), so, by
`revise_same_of_determinate`, every revision by the TIME COOK label adopts
one and the same retrieval, from any theory and at every attempt. -/
theorem epam_revisions_same :
    ∃ r : Option Item, ∀ s : LS Net, s.mem = net →
      ∀ x ∈ epam1.space.apply (.revise (.label tcKey)) s, x.1.adopted = s.adopted ++ [r] :=
  revise_same_of_determinate K (netRetriever order) (Net.leaf none) [setTimeItem, timerItem]
    (Laws.determinate_of_deterministic _ _ _ (netRetriever_deterministic order)) code viewOf predicts
    labelOnly false net ⟨[setTimeItem, timerItem], by simp, rfl⟩ (.label tcKey)

/-- **EPAM, two cues: a garden path half the time, always solved.** If the
learner consults the label first (probability 1/2), it adopts SET-A-TIME,
fails again, consults the display, and adopts DURATION: a garden path.
Otherwise the display brings in DURATION at once. -/
theorem epam_two_cues :
    Dist.prob (epam2.session 4 (start net)) (fun s => Phenomena.gardenPath (views s)) = 1 / 2 ∧
      Dist.prob (epam2.session 4 (start net)) solved = 1 ∧
      Dist.prob (epam2.session 4 (start net)) (fun s => Phenomena.perseverates (views s)) = 0 := by
  decide +kernel

/-- **ACT-R, two cues**: a garden path with probability 125/1219 (about .10),
solved with 1050/1219 (about .86), and perseveration with 25/1219 (the
display, too, can call up SET TIME). -/
theorem act_two_cues :
    Dist.prob (act2.session 4 (start mem)) (fun s => Phenomena.gardenPath (views s)) = 125 / 1219 ∧
      Dist.prob (act2.session 4 (start mem)) solved = 1050 / 1219 ∧
      Dist.prob (act2.session 4 (start mem)) (fun s => Phenomena.perseverates (views s)) =
        25 / 1219 := by
  decide +kernel

/-- **EPAM, label only: certain perseveration, never solved.** The label
calls up SET TIME at every failure (`epam_revisions_same`). -/
theorem epam_label_only :
    Dist.prob (epam1.session 4 (start net)) (fun s => Phenomena.perseverates (views s)) = 1 ∧
      Dist.prob (epam1.session 4 (start net)) solved = 0 := by
  decide +kernel

/-- **ACT-R, label only: graded retrieval escapes.** Solved within four cycles
with probability 251280/279841 (about .90); perseveration about .10. -/
theorem act_label_only :
    Dist.prob (act1.session 4 (start mem)) solved = 251280 / 279841 ∧
      Dist.prob (act1.session 4 (start mem)) (fun s => Phenomena.perseverates (views s)) =
        27225 / 279841 := by
  decide +kernel

/-- **A correct theory is kept.** After DURATION, the theory predicts the
episode, so no session from it revises it (`correct_theory_stable`; shown
for EPAM's two-cue learner, and the general theorem holds for any). -/
theorem duration_kept (k : Nat) (T : KNet A Lbl) (hT : T ∈ (applyView K durView theory0).map (·.1)) :
    ∀ x ∈ epam2.session k ⟨T, net, [ep], [], []⟩, x.1.theory = T := by
  apply correct_theory_stable
  intro e he
  simp only [List.mem_singleton] at he
  subst he
  revert T
  decide +kernel

end DeviceLearning
