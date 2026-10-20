/-
Memory structures: cue codes, and retrieval from partial information.

A cue code is partial information about a stimulus: some features known,
the rest unknown. Associating a response with a stimulus means storing, with
the stimulus's image, a cue for the response: enough of the response's code
to select its image. Retrieval sorts the cue through the net. Where the cue
is silent at a test, either branch may be taken.

Results:
* `cue_from_path_selects`: a cue holding exactly the features on the
  response's path selects the response, and nothing else.
* `restoration`: rebuilding a cue from the response's current path makes it
  select the response again, and only it.
-/

import CogLib.Memory.DiscriminationNet

namespace Cog

/-- A cue code: partial information about a code. `none` = unknown. -/
abbrev Cue := Feature → Option Bool

/-- The cue for `y` that records only the features in `fs`. -/
def cueOf (y : Item) (fs : List Feature) : Cue :=
  fun f => if f ∈ fs then some (y.feat f) else none

namespace Net

/-- Selection applied to a cue code. Where the cue is silent, either branch may be
taken. -/
inductive CueSelects : Net → Cue → Option Item → Prop
  | leaf (img : Option Item) (c : Cue) : CueSelects (leaf img) c img
  | known {f : Feature} {n0 n1 : Net} {c : Cue} {r : Option Item} (b : Bool)
      (hb : c f = some b) (h : CueSelects (if b then n1 else n0) c r) :
      CueSelects (test f n0 n1) c r
  | guess0 {f : Feature} {n0 n1 : Net} {c : Cue} {r : Option Item}
      (hb : c f = none) (h : CueSelects n0 c r) : CueSelects (test f n0 n1) c r
  | guess1 {f : Feature} {n0 n1 : Net} {c : Cue} {r : Option Item}
      (hb : c f = none) (h : CueSelects n1 c r) : CueSelects (test f n0 n1) c r

/-- A cue that agrees with `y` on every feature of `y`'s path selects `y`'s
terminal, and only that one. -/
theorem cue_agreeing_on_path (N : Net) (y : Item) (c : Cue)
    (hc : ∀ f ∈ N.path y, c f = some (y.feat f)) :
    CueSelects N c (N.select y) ∧ ∀ r, CueSelects N c r → r = N.select y := by
  induction N with
  | leaf img =>
    refine ⟨CueSelects.leaf img c, ?_⟩
    intro r hr
    cases hr; rfl
  | test f n0 n1 ih0 ih1 =>
    have hf : c f = some (y.feat f) := hc f (by simp [path])
    cases hy : y.feat f with
    | true =>
      have hc1 : ∀ g ∈ n1.path y, c g = some (y.feat g) :=
        fun g hg => hc g (by simp [path, hy, hg])
      obtain ⟨hs, hu⟩ := ih1 hc1
      refine ⟨?_, ?_⟩
      · have : (test f n0 n1).select y = n1.select y := by simp [select, hy]
        rw [this]
        exact CueSelects.known true (by rw [hf, hy]) (by simpa using hs)
      · intro r hr
        have : (test f n0 n1).select y = n1.select y := by simp [select, hy]
        rw [this]
        cases hr with
        | known b hb h =>
          rw [hf, hy] at hb
          cases hb
          exact hu r (by simpa using h)
        | guess0 hb _ => rw [hf] at hb; cases hb
        | guess1 hb _ => rw [hf] at hb; cases hb
    | false =>
      have hc0 : ∀ g ∈ n0.path y, c g = some (y.feat g) :=
        fun g hg => hc g (by simp [path, hy, hg])
      obtain ⟨hs, hu⟩ := ih0 hc0
      refine ⟨?_, ?_⟩
      · have : (test f n0 n1).select y = n0.select y := by simp [select, hy]
        rw [this]
        exact CueSelects.known false (by rw [hf, hy]) (by simpa using hs)
      · intro r hr
        have : (test f n0 n1).select y = n0.select y := by simp [select, hy]
        rw [this]
        cases hr with
        | known b hb h =>
          rw [hf, hy] at hb
          cases hb
          exact hu r (by simpa using h)
        | guess0 hb _ => rw [hf] at hb; cases hb
        | guess1 hb _ => rw [hf] at hb; cases hb

/-- **A path cue is sufficient.** The cue made of exactly the features on the
response's path selects the response's image, and nothing else. -/
theorem cue_from_path_selects (N : Net) (y : Item) :
    CueSelects N (cueOf y (N.path y)) (N.select y) ∧
      ∀ r, CueSelects N (cueOf y (N.path y)) r → r = N.select y :=
  cue_agreeing_on_path N y _ (fun f hf => by simp [cueOf, hf])

/-- **Restoration.** After the net has grown, rebuilding the cue from the
response's new path re-establishes the link: the cue selects the response,
and nothing else. -/
theorem restoration (N : Net) (y : Item) (hy : Recognizes N y) :
    CueSelects N (cueOf y (N.path y)) (some y) ∧
      ∀ r, CueSelects N (cueOf y (N.path y)) r → r = some y := by
  have h := cue_from_path_selects N y
  unfold Recognizes at hy
  rw [hy] at h
  exact h

/-- Every image a cue (a list of known feature values) can reach: a
computable form of `CueSelects`. -/
def cueResults : Net → List (Feature × Bool) → List (Option Item)
  | leaf img, _ => [img]
  | test f n0 n1, c =>
    match c.lookup f with
    | some true => n1.cueResults c
    | some false => n0.cueResults c
    | none => n0.cueResults c ++ n1.cueResults c

end Net

/-- The cue for `y` in net `N`: its features on its current path. -/
def cueFor (N : Net) (y : Item) : List (Feature × Bool) :=
  (N.path y).map (fun f => (f, y.feat f))

end Cog
