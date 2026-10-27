/-
Memory structures: discrimination nets.

A discrimination net stores images (copies of codes) at its terminals.
Each testing point examines one feature and branches on it. A terminal may
also be empty: the null image. Recognition sorts a code down the net and
yields the image it reaches.

Results:
* `select_depends_only_on_noticed_features`: what a code is recognized as
  depends only on the features examined on its path. Every confusion a
  discrimination net makes comes from this.
* `discrimination_needs_a_difference`: a net that tells two codes apart has
  examined a feature on which they differ.
* `confusion_agrees_on_path`: if each image is stored once, a code
  recognized as a stored image agrees with it on every feature its path
  examines. A confusion is always a confusion with a code that looks the
  same to the net.
* `confusion_preserves`: so a confusion preserves every property that the
  features on the path determine.
-/

import CogLib.Rep.Features

namespace Cog

/-- A discrimination net. A terminal holds an image or `none`, the null
image. A testing point examines one feature and branches. -/
inductive Net where
  | leaf : Option Item → Net
  | test : Feature → Net → Net → Net
  deriving Repr

namespace Net

/-- Selection: sort a code to a terminal and return its image. -/
def select : Net → Item → Option Item
  | leaf img, _ => img
  | test f n0 n1, x => if x.feat f then n1.select x else n0.select x

/-- The features examined while sorting `x`: the path it takes. -/
def path : Net → Item → List Feature
  | leaf _, _ => []
  | test f n0 n1, x => f :: (if x.feat f then n1.path x else n0.path x)

/-- A code is *recognized* by a net when it selects its own image. -/
def Recognizes (N : Net) (x : Item) : Prop := N.select x = some x

instance (N : Net) (x : Item) : Decidable (Recognizes N x) :=
  inferInstanceAs (Decidable (N.select x = some x))

/-- The images stored in a net. -/
def images : Net → List Item
  | leaf none => []
  | leaf (some z) => [z]
  | test _ n0 n1 => n0.images ++ n1.images

/-- **Selection depends only on noticed features.** Two codes that agree
on every feature the net examines along one of them select the same image. -/
theorem select_depends_only_on_noticed_features (N : Net) (x y : Item)
    (h : ∀ f ∈ N.path x, x.feat f = y.feat f) : N.select y = N.select x := by
  induction N with
  | leaf img => rfl
  | test f n0 n1 ih0 ih1 =>
    have hf : x.feat f = y.feat f := h f (by simp [path])
    simp only [select]
    rw [← hf]
    cases hx : x.feat f with
    | true =>
      simp only [ite_true]
      exact ih1 (fun g hg => h g (by simp [path, hx, hg]))
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ih0 (fun g hg => h g (by simp [path, hx, hg]))

/-- The same fact read the other way: if a net tells two codes apart, it
must have examined, on the way down one of them, a feature on which they
differ. -/
theorem discrimination_needs_a_difference (N : Net) (x y : Item)
    (h : N.select x ≠ N.select y) : ∃ f ∈ N.path x, x.feat f ≠ y.feat f := by
  apply Classical.byContradiction
  intro hno
  apply h
  have hall : ∀ f ∈ N.path x, x.feat f = y.feat f := by
    intro f hf
    apply Classical.byContradiction
    intro hne
    exact hno ⟨f, hf, hne⟩
  exact (select_depends_only_on_noticed_features N x y hall).symm

/-- What selection returns is an image stored in the net. -/
theorem select_mem_images (N : Net) (x z : Item) (h : N.select x = some z) : z ∈ N.images := by
  induction N with
  | leaf img =>
    cases img with
    | none => simp [select] at h
    | some w => simp [select] at h; simp [images, h]
  | test f n0 n1 ih0 ih1 =>
    simp only [select] at h
    simp only [images, List.mem_append]
    split at h
    · exact Or.inr (ih1 h)
    · exact Or.inl (ih0 h)

/-- **A confusion is with a code that looks the same to the net.** If each
image is stored once, and `x` is recognized as the stored image `y` (which
the net itself recognizes), then `x` agrees with `y` on every feature
examined along `x`'s path. -/
theorem confusion_agrees_on_path (N : Net) (x y : Item) (hnd : N.images.Nodup)
    (hy : N.select y = some y) (hx : N.select x = some y) :
    ∀ f ∈ N.path x, x.feat f = y.feat f := by
  induction N with
  | leaf img => simp [path]
  | test f n0 n1 ih0 ih1 =>
    simp only [images, List.nodup_append] at hnd
    obtain ⟨hnd0, hnd1, hdisj⟩ := hnd
    simp only [select] at hx hy
    intro g hg
    simp only [path] at hg
    cases hxf : x.feat f <;> cases hyf : y.feat f <;> simp [hxf, hyf] at hx hy hg
    · -- both go to n0
      rcases hg with rfl | hg
      · rw [hxf, hyf]
      · exact ih0 hnd0 hy hx g hg
    · -- x to n0, y to n1: y stored in both
      exact absurd rfl (hdisj y (select_mem_images n0 x y hx) y (select_mem_images n1 y y hy))
    · exact absurd rfl (hdisj y (select_mem_images n0 y y hy) y (select_mem_images n1 x y hx))
    · rcases hg with rfl | hg
      · rw [hxf, hyf]
      · exact ih1 hnd1 hy hx g hg

/-- **A confusion preserves what the path determines.** If each image is
stored once, `x` is recognized as the stored code of `q`, and the features
`fs`, all examined on `x`'s path, determine a property `P`, then `x` and `q`
agree on `P`. -/
theorem confusion_preserves {α β : Type} (N : Net) (code : α → Item) (fs : List Feature)
    (P : α → β) (hD : Determines code fs P) (x q : α) (hnd : N.images.Nodup)
    (hq : N.select (code q) = some (code q)) (hx : N.select (code x) = some (code q))
    (hcover : ∀ f ∈ fs, f ∈ N.path (code x)) : P x = P q :=
  hD x q fun f hf => confusion_agrees_on_path N _ _ hnd hq hx f (hcover f hf)

end Net
end Cog
