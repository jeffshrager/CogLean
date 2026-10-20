/-
Control: attention to features.

A *noticing order* is the order in which a system scans features when it
looks for a difference between two codes. Which differences are found, and
how long finding them takes, depend on it: two codes that differ only on
features the order never reaches cannot be told apart at all.

Results:
* `firstDiff_differs`: a difference found by the scan is a real difference.
* `scanCost_ge_of_agree`: codes that agree on the first `k` features in the
  order cost at least `k` scanning steps to tell apart (similarity costs
  time).
-/

import CogLib.Rep.Features

namespace Cog

/-- A noticing order: the order in which features are scanned. -/
abbrev NoticingOrder := List Feature

/-- The first feature, in noticing order, on which `x` and `z` differ. -/
def firstDiff (order : NoticingOrder) (x z : Item) : Option Feature :=
  order.find? (fun f => x.feat f != z.feat f)

/-- Two codes are *noticeably different* under a noticing order when the
scan finds a difference. -/
def Noticeable (order : NoticingOrder) (x z : Item) : Prop :=
  ∃ f, firstDiff order x z = some f

theorem firstDiff_differs {order : NoticingOrder} {x z : Item} {f : Feature}
    (h : firstDiff order x z = some f) : x.feat f ≠ z.feat f := by
  have := List.find?_some h
  simpa [bne_iff_ne] using this

/-- The first `k` features, in noticing order, on which `x` and `z` differ. -/
def diffs (order : NoticingOrder) (k : Nat) (x z : Item) : List Feature :=
  (order.filter (fun f => x.feat f != z.feat f)).take k

/-- How many features are scanned, in noticing order, before a difference
between `x` and `z` is found (all of them if none is). -/
def scanCost : NoticingOrder → Item → Item → Nat
  | [], _, _ => 0
  | f :: fs, x, z => if x.feat f != z.feat f then 1 else 1 + scanCost fs x z

/-- **Similarity costs scanning.** If two codes agree on the first `k`
features of the noticing order, finding their difference costs at least `k`
steps. -/
theorem scanCost_ge_of_agree (order : NoticingOrder) (x z : Item) :
    ∀ k, k ≤ order.length → (∀ f ∈ order.take k, x.feat f = z.feat f) →
      k ≤ scanCost order x z := by
  induction order with
  | nil => intro k hk _; simp at hk; omega
  | cons f fs ih =>
    intro k hk hagree
    cases k with
    | zero => exact Nat.zero_le _
    | succ k =>
      have hf : x.feat f = z.feat f := hagree f (by simp)
      have hrest : ∀ g ∈ fs.take k, x.feat g = z.feat g :=
        fun g hg => hagree g (by simp [hg])
      have := ih k (by simp at hk; omega) hrest
      simp [scanCost, hf]
      omega

end Cog
