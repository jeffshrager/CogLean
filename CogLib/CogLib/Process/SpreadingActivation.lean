/-
Processes: spreading activation (Collins & Loftus 1975), on knowledge nets.

* SA1 (p. 411, assumption 1): when a concept is processed, activation
  spreads out along the links of the net in a decreasing gradient: each
  link passes on a fraction of what reaches it, larger for stronger links
  (`strength`). Links are followed in their stated direction; a link that
  goes both ways is two links.
* SA2 (assumption 2): the longer a concept is processed, the more
  activation it releases: a source carries an amount.
* SA4 (assumption 4): activation from different sources sums.
* Spread is bounded by a depth, standing for decay over time and
  intervening activity (assumption 3).

`activation` is the total reaching a node: over every walk from a source of
length at most the depth, the source's amount times the strengths along
the walk.

Main results: activation sums over sources (`activation_append`, SA4 as a
theorem); it is never negative, and adding a source never lowers any
node's activation (`activation_mono`): priming only helps.

Choice among candidates in proportion to activation (`choose`, as in
retrieval by strength): priming a candidate that reaches no other
candidate never lowers its chance of being chosen (`choose_primed`).
-/

import CogLib.Process.ViewApplication

namespace Cog

variable {A L : Type} [DecidableEq A]

/-- The parameters: each link's strength (the fraction it passes on), and the depth. -/
structure SAParams (A L : Type) where
  strength : Term A × L × Term A → Rat
  depth : Nat

/-- Sources of activation: nodes with amounts. -/
abbrev Sources (A : Type) := List (Term A × Rat)

/-- One step of spread: each packet moves along every link out of its node,
scaled by the link's strength. -/
def spreadStep (G : KNet A L) (P : SAParams A L) (src : Sources A) : Sources A :=
  src.flatMap fun (m, x) =>
    (G.links.filter fun e => e.1 == m).map fun e => (e.2.2, x * P.strength e)

/-- All packets within `k` steps. -/
def spreadAll (G : KNet A L) (P : SAParams A L) : Nat → Sources A → Sources A
  | 0, src => src
  | k + 1, src => src ++ spreadAll G P k (spreadStep G P src)

/-- The amount at node `n` among packets. -/
def amountAt (n : Term A) (ps : Sources A) : Rat := ((ps.filter fun p => p.1 == n).map (·.2)).sum

/-- **Activation** of node `n` from sources `src`. -/
def activation (G : KNet A L) (P : SAParams A L) (src : Sources A) (n : Term A) : Rat :=
  amountAt n (spreadAll G P P.depth src)

theorem amountAt_append (n : Term A) (ps qs : Sources A) :
    amountAt n (ps ++ qs) = amountAt n ps + amountAt n qs := by
  simp [amountAt, List.filter_append, List.map_append, List.sum_append]

theorem spreadStep_append (G : KNet A L) (P : SAParams A L) (s t : Sources A) :
    spreadStep G P (s ++ t) = spreadStep G P s ++ spreadStep G P t := by
  simp [spreadStep, List.flatMap_append]

theorem spreadAll_amount_append (G : KNet A L) (P : SAParams A L) (k : Nat) (n : Term A)
    (s t : Sources A) :
    amountAt n (spreadAll G P k (s ++ t)) =
      amountAt n (spreadAll G P k s) + amountAt n (spreadAll G P k t) := by
  induction k generalizing s t with
  | zero => exact amountAt_append n s t
  | succ k ih =>
    simp only [spreadAll, amountAt_append, spreadStep_append, ih]
    grind

/-- **Activation from several sources sums** (SA4). -/
theorem activation_append (G : KNet A L) (P : SAParams A L) (s t : Sources A) (n : Term A) :
    activation G P (s ++ t) n = activation G P s n + activation G P t n :=
  spreadAll_amount_append G P P.depth n s t

theorem amountAt_nonneg (n : Term A) (ps : Sources A) (h : ∀ p ∈ ps, 0 ≤ p.2) :
    0 ≤ amountAt n ps := by
  induction ps with
  | nil => simp [amountAt]
  | cons p ps ih =>
    have hp := h p List.mem_cons_self
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    unfold amountAt at ih' ⊢
    rw [List.filter_cons]
    split
    · rw [List.map_cons, List.sum_cons]; grind
    · exact ih'

theorem spreadAll_nonneg (G : KNet A L) (P : SAParams A L) (hs : ∀ e, 0 ≤ P.strength e)
    (k : Nat) (src : Sources A) (h : ∀ p ∈ src, 0 ≤ p.2) :
    ∀ p ∈ spreadAll G P k src, 0 ≤ p.2 := by
  induction k generalizing src with
  | zero => exact h
  | succ k ih =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h p hp
    · refine ih _ ?_ p hp
      intro q hq
      simp only [spreadStep, List.mem_flatMap, List.mem_map] at hq
      obtain ⟨⟨m, x⟩, hmx, e, _, rfl⟩ := hq
      exact Rat.mul_nonneg (h _ hmx) (hs e)

/-- **Activation is never negative**, with nonnegative strengths and sources. -/
theorem activation_nonneg (G : KNet A L) (P : SAParams A L) (hs : ∀ e, 0 ≤ P.strength e)
    (src : Sources A) (h : ∀ p ∈ src, 0 ≤ p.2) (n : Term A) : 0 ≤ activation G P src n :=
  amountAt_nonneg n _ (spreadAll_nonneg G P hs _ src h)

/-- **Priming only helps**: adding sources never lowers a node's activation. -/
theorem activation_mono (G : KNet A L) (P : SAParams A L) (hs : ∀ e, 0 ≤ P.strength e)
    (src extra : Sources A) (h : ∀ p ∈ extra, 0 ≤ p.2) (n : Term A) :
    activation G P src n ≤ activation G P (src ++ extra) n := by
  rw [activation_append]
  have := activation_nonneg G P hs extra h n
  grind

/-- Choice among candidates in proportion to their activation. -/
def choose (G : KNet A L) (P : SAParams A L) (src : Sources A) (cands : List A) : Dist A :=
  let tot := (cands.map fun c => activation G P src (.atom c)).sum
  cands.map fun c => (c, activation G P src (.atom c) / tot)

/-- **Priming a candidate raises its share**: if extra activation reaches
candidate `v` by `δ` and no other candidate at all, `v`'s share of the total
activation does not fall. -/
theorem choose_primed (a S δ : Rat) (hS : a ≤ S) (hS0 : 0 < S) (hδ : 0 ≤ δ) :
    a / S ≤ (a + δ) / (S + δ) := by
  apply Dist.div_le_div_cross hS0 (by grind)
  have : a * δ ≤ S * δ := Rat.mul_le_mul_of_nonneg_right hS hδ
  grind

end Cog
