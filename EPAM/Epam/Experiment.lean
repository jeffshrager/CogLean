/-
EPAM, the machinery of a serial-anticipation experiment.

This puts EPAM's postulates (`Postulates.lean`) together in the form the
hand simulation of P-1817 §4.1 actually used. The pieces are CogLib's:

* **F1 with redundancy (F1a) and P2 = k.** At a point of confusion F1 notices
  up to `k` differences (§4.1.1.1.2: "the maximum number of differences
  noticed (and tests added) each time the net is grown will be taken to be
  three"). The first test separates the incumbent from the new item. The
  others are redundant tests on the new item's side, each with a null image
  on the branch the new item does not take. These are the empty terminals of
  Fig. 4.1, which give the "none" responses.
* **Associations stored with images (F2).** Each image may carry a cue code
  for its response: the response's features on its current path.
* **Responding (R) with random branching.** The cue is sorted through the
  net. Where it is silent, both branches are possible (§3.5.1.2; Fig. 4.1
  note 6, "When cue code contains insufficient information, D2 selects
  randomly"). `responses` lists every possible response, so possibilities
  can be computed and checked by `decide`.

What is EPAM-specific here is the learner's state (a net, and a cue stored
with each image) and the learning events of its F0 cycle.
-/

import Epam.Postulates

namespace Epam

open Cog

/-- The learner's state: its net, and the cue stored with each image. -/
structure Learner where
  net : Net
  assoc : List (Item × List (Feature × Bool))

/-- Learning events of an F0 cycle (§2.4): F1 on an item, or F2 on a pair
(also used for D8, which rebuilds the cue). -/
inductive Event where
  | f1 : Item → Event
  | f2 : Item → Item → Event

/-- Apply an event. -/
def Learner.apply (order : NoticingOrder) (k : Nat) (L : Learner) : Event → Learner
  | .f1 x => { L with net := L.net.learnK order k x }
  | .f2 s r =>
    let img := (L.net.select s).getD s
    { L with assoc := (img, cueFor L.net r) :: L.assoc.filter (fun p => p.1 != img) }

/-- R: every possible response to stimulus `s`. `none` means no response
(the stimulus is not recognized, has no stored cue, or its cue reaches a null
image). -/
def Learner.responses (L : Learner) (s : Item) : List (Option Item) :=
  match L.net.select s with
  | none => [none]
  | some img =>
    match L.assoc.lookup img with
    | none => [none]
    | some c => L.net.cueResults c

end Epam
