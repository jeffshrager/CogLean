/-
Processes: association by cue codes, as the net grows underneath.

A cue is sized for the net as it is when the association is formed. The net
keeps growing as other things are learned, and a cue that was sufficient can
become insufficient: retrieval then branches where the cue is silent.

Results:
* `cue_can_fail_after_growth`: a cue that selected the response can, after
  the net grows, select another image, or still the right one.
* `learning_can_capture_old_cue`: learning new material can make an old
  cue select the new material.

So in a discrimination-net memory, interference arises in retrieval (the
cues), not in storage (the net, which is monotone: `learn_preserves`).

As phenomena: a net retrieving by cue codes is a responder
(`netResponder`), and it has `Oscillation` and `RetroactiveInterference`
whenever two codes are noticeably different.
-/

import CogLib.Memory.Cue
import CogLib.Process.DiscriminationLearning
import CogLib.Phenomena.Responder

namespace Cog
namespace Net

/-- **A cue can fail after the net grows.** Suppose `y` is the only image stored (net = one
terminal), so the link to `y` needs no information at all: the empty cue
selects `y`. Now another stimulus `w`, noticeably different, is learned. The
net grows a test, and the very same cue can now select `w`, a wrong
response, or still `y`. -/
theorem cue_can_fail_after_growth (order : NoticingOrder) (y w : Item) (f : Feature)
    (hyw : y ≠ w) (hf : firstDiff order w y = some f) :
    let before := leaf (some y)
    let after := before.learn order w
    let cue := cueOf y []
    CueSelects before cue (some y) ∧
      CueSelects after cue (some w) ∧ CueSelects after cue (some y) := by
  intro before after cue
  have hnone : ∀ g, cue g = none := fun g => by simp [cue, cueOf]
  refine ⟨CueSelects.leaf _ _, ?_, ?_⟩
  all_goals
    simp only [after, before, learn, hyw, ite_false, hf]
    cases hw : w.feat f
  · exact CueSelects.guess0 (hnone f) (CueSelects.leaf _ _)
  · exact CueSelects.guess1 (hnone f) (CueSelects.leaf _ _)
  · exact CueSelects.guess1 (hnone f) (CueSelects.leaf _ _)
  · exact CueSelects.guess0 (hnone f) (CueSelects.leaf _ _)

/-- **Learning new material can capture an old cue.** A cue that selected
`y` can select a newly learned `w` instead, because learning `w` grows the
net under the old cue. -/
theorem learning_can_capture_old_cue (order : NoticingOrder) (y w : Item) (f : Feature)
    (hyw : y ≠ w) (hf : firstDiff order w y = some f) :
    ∃ N c, CueSelects N c (some y) ∧ CueSelects (N.learn order w) c (some w) := by
  obtain ⟨h1, h2, _⟩ := cue_can_fail_after_growth order y w f hyw hf
  exact ⟨_, _, h1, h2⟩

end Net

/-! ### As phenomena -/

/-- A discrimination net retrieving by cue codes, as a responder. -/
def netResponder : Responder Net Cue Item := ⟨Net.CueSelects⟩

/-- **Cue retrieval in a growing net oscillates.** -/
theorem netResponder_oscillation (order : NoticingOrder) (y w : Item) (f : Feature)
    (hyw : y ≠ w) (hf : firstDiff order w y = some f) :
    Phenomena.Oscillation netResponder (fun N x => N.learn order x) := by
  obtain ⟨h1, h2, h3⟩ := Net.cue_can_fail_after_growth order y w f hyw hf
  exact ⟨_, _, y, w, some w, h1, by simp [Ne.symm hyw], h2, h3⟩

/-- **Cue retrieval in a growing net shows retroactive interference.** -/
theorem netResponder_retroactiveInterference (order : NoticingOrder) (y w : Item) (f : Feature)
    (hyw : y ≠ w) (hf : firstDiff order w y = some f) :
    Phenomena.RetroactiveInterference netResponder (fun N x => N.learn order x) id := by
  obtain ⟨N, c, h1, h2⟩ := Net.learning_can_capture_old_cue order y w f hyw hf
  exact ⟨N, c, y, w, hyw, h1, h2⟩

end Cog
