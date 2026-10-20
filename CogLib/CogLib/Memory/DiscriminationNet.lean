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

end Net
end Cog
