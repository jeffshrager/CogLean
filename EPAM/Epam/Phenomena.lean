/-
The phenomena EPAM explains, as consequences of its postulates.

Each theorem states a phenomenon the way P-1817 §4.1.1.3 or Feigenbaum &
Simon (1962) state it, and proves it from the CogLib constructs that EPAM's
postulates choose (`Postulates.lean`). Where CogLib has a theory-neutral
statement of the phenomenon (`Cog.Phenomena`), the theorem is about that
statement. The List A instance (`ListA.lean`) gives a concrete case of the
first.
-/

import Epam.Postulates
import Epam.ListA

namespace Epam.Phenomena

open Cog Net

/-- **Stimulus generalization** (§4.1.1.3.2). A stimulus that has not been
learned, but agrees with a learned stimulus on every feature its path
examines, is recognized as that stimulus, and so gets its response. (Fig. 4.1,
trial 4: PEM answered as ROM; see `stimulus_generalization_List_A`.) -/
theorem stimulus_generalization (order : NoticingOrder) (N : Net) (x y : Item) (hyx : y ≠ x)
    (hx : Recognizes N x) (hagree : ∀ f ∈ N.path x, x.feat f = y.feat f) :
    Cog.Phenomena.StimulusGeneralization (learner order) N x y :=
  netLearner_generalizes order N x y hyx hx hagree

/-- The List A instance of stimulus generalization, at trial 4. -/
theorem stimulus_generalization_List_A :
    Cog.Phenomena.StimulusGeneralization (learner ListA.order) ListA.netTrial4 ListA.ROM ListA.PEM :=
  stimulus_generalization _ _ _ _ (by decide) ListA.trial4_learned_recognized.2.2.2.1
    ListA.PEM_agrees_with_ROM_on_ROMs_path

/-- **Generalization is removed by discrimination learning.** Once the
generalized stimulus itself goes through F1, it is recognized as itself, and
the stimulus it was confused with is still recognized. -/
theorem generalization_removed_by_learning (order : NoticingOrder) (N : Net) (x y : Item)
    (hx : Recognizes N x) (hyx : y ≠ x)
    (hn : ∀ z ∈ N.images, z ≠ y → Noticeable order y z) :
    Recognizes (N.learn order y) y ∧ Recognizes (N.learn order y) x :=
  ⟨learn_recognizes order N y hn, learn_preserves order N y x hx (Ne.symm hyx)⟩

/-- **Intralist similarity** (§4.1.1.3.3), part 1. Any net that keeps two
stimuli apart has tested a feature on which they differ; the more similar the
items, the fewer such features exist. -/
theorem intralist_similarity_needs_differences (N : Net) (x y : Item)
    (h : N.select x ≠ N.select y) : ∃ f ∈ N.path x, x.feat f ≠ y.feat f :=
  discrimination_needs_a_difference N x y h

/-- **Intralist similarity**, part 2. Items alike in the features noticed
first take longer to tell apart. -/
theorem intralist_similarity_costs_scanning (order : NoticingOrder) (x z : Item) (k : Nat)
    (hk : k ≤ order.length) (hagree : ∀ f ∈ order.take k, x.feat f = z.feat f) :
    k ≤ scanCost order x z :=
  scanCost_ge_of_agree order x z k hk hagree

/-- **Oscillation** (§4.1.1.3.4). A response once given correctly can later
fail (and later still succeed again), because the net grew under a cue that
was only just sufficient when it was formed. -/
theorem oscillation (order : NoticingOrder) (y w : Item) (f : Feature)
    (hyw : y ≠ w) (hf : firstDiff order w y = some f) :
    let before := leaf (some y)
    let after := before.learn order w
    let cue := cueOf y []
    CueSelects before cue (some y) ∧
      CueSelects after cue (some w) ∧ CueSelects after cue (some y) :=
  cue_can_fail_after_growth order y w f hyw hf

/-- **Recovery** (D8). Rebuilding the cue from the response's current path
restores the link for good (it selects the response and nothing else). -/
theorem recovery (N : Net) (y : Item) (hy : Recognizes N y) :
    CueSelects N (cueOf y (N.path y)) (some y) ∧
      ∀ r, CueSelects N (cueOf y (N.path y)) r → r = some y :=
  restoration N y hy

/-- **Retroactive inhibition** (§4.1.2). Learning new material can undo a
correct response to old material. -/
theorem retroactive_inhibition (order : NoticingOrder) (y w : Item) (f : Feature)
    (hyw : y ≠ w) (hf : firstDiff order w y = some f) :
    ∃ N c, CueSelects N c (some y) ∧ CueSelects (N.learn order w) c (some w) :=
  learning_can_capture_old_cue order y w f hyw hf

/-- **Learning is non-interfering**: learning one item never undoes the
recognition of another. -/
theorem non_interference (order : NoticingOrder) :
    Cog.Phenomena.NonInterference (learner order) :=
  netLearner_nonInterference order

/-- **Learning to criterion, without unlearning.** From an empty memory, a
list of mutually noticeable items is completely learned with one
discrimination cycle each. -/
theorem learning_to_criterion (order : NoticingOrder) :
    Cog.Phenomena.ReachesCriterion (learner order) (leaf none) (PairwiseNoticeable order) :=
  netLearner_reachesCriterion order

/-- **Learning time grows with the amount to be learned** (M0, M1). -/
theorem total_time (learned : Nat → Nat) (n T : Nat)
    (hunit : ∀ t, learned t ≤ t) (hcrit : n ≤ learned T) : n ≤ T :=
  trials_at_least_items learned n T hunit hcrit

/-- **The serial position effect** (M3; Feigenbaum & Simon 1962). Errors
increase with distance from the nearer end of the list: a bowed curve. -/
theorem serial_position_effect (n : Nat) :
    Cog.Phenomena.SerialPositionEffect n (errorsAt n) :=
  anchorAttention_serialPosition n

end Epam.Phenomena
