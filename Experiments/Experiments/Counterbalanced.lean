/-
An experiment derived from laws: counterbalanced study order.

Recency and order-freedom make incompatible claims, and this experiment is
derived from that disagreement (`notes/20261027_CogLean_Direction.md`, §4.1).
Take two new items `a` and `b`, and a probe `x` equally similar to both.
Condition AB studies a prior list, then `a`, then `b`; condition BA studies
the prior list, then `b`, then `a`. Both probe with `x`. With
`D = P(retrieve b) − P(retrieve a)` in each condition, the order effect is
`Δ = D_AB − D_BA`.

From laws alone, with no mechanism:
* `orderFree_delta_zero`: order-freedom gives `Δ = 0`.
* `recency_delta_pos`: recency gives `Δ > 0`.
* `orderFree_recency_inconsistent`: so no memory has both, wherever such a
  design exists.

From what memory retrieves to what a participant says:
* `ForcedChoice`: report A if `a` is retrieved, B if `b` is, and otherwise
  guess B with probability `γ`.
* `delta_report`: the reported order effect is
  `Δ + (2γ − 1)(o_AB − o_BA)`, where `o` is the chance of retrieving neither.
  Guessing cancels only when it is unbiased or "neither" is equally likely
  in both orders.
* `forcedChoice_orderFree`: under order-freedom the reported effect is 0,
  for any `γ`.
* `forcedChoice_recency`: under recency, with unbiased guessing, it is
  positive.

That is the shape `laws + response model ⇒ observable contrast`, with the
condition the bridge needs stated in the theorem.
-/

import Experiments.StudyTest

namespace Cog.Exp

open Laws Dist

/-- A counterbalanced design: a prior list, two items, and a probe. -/
structure ABBA where
  xs : List Item
  a : Item
  b : Item
  x : Item

/-- A valid design: everything from `U`, `a` and `b` distinct and new, and the
probe equally similar to both on the features `fs`. -/
structure ABBA.Valid (E : ABBA) (fs : List Feature) (U : List Item) : Prop where
  hxs : ∀ y ∈ E.xs, y ∈ U
  ha : E.a ∈ U
  hb : E.b ∈ U
  hab : E.a ≠ E.b
  hax : E.a ∉ E.xs
  hbx : E.b ∉ E.xs
  hsim : mismatches fs E.x E.a = mismatches fs E.x E.b

variable {S : Type}

namespace ABBA

/-- Memory after condition AB. -/
def memAB (E : ABBA) (R : Retriever S Item) (s0 : S) : S := R.studyAll s0 (E.xs ++ [E.a, E.b])

/-- Memory after condition BA. -/
def memBA (E : ABBA) (R : Retriever S Item) (s0 : S) : S := R.studyAll s0 (E.xs ++ [E.b, E.a])

/-- The preference for `b` over `a` in a memory state. -/
def pref (E : ABBA) (R : Retriever S Item) (s : S) : Rat := pRet R s E.x E.b - pRet R s E.x E.a

/-- **The order effect.** -/
def delta (E : ABBA) (R : Retriever S Item) (s0 : S) : Rat :=
  E.pref R (E.memAB R s0) - E.pref R (E.memBA R s0)

theorem memAB_eq (E : ABBA) (R : Retriever S Item) (s0 : S) :
    E.memAB R s0 = R.study (R.study (R.studyAll s0 E.xs) E.a) E.b := by
  simp [memAB, Retriever.studyAll, List.foldl_append]

theorem memBA_eq (E : ABBA) (R : Retriever S Item) (s0 : S) :
    E.memBA R s0 = R.study (R.study (R.studyAll s0 E.xs) E.b) E.a := by
  simp [memBA, Retriever.studyAll, List.foldl_append]

end ABBA

/-- **Order-freedom gives no order effect.** -/
theorem orderFree_delta_zero (R : Retriever S Item) (s0 : S) (U : List Item) (fs : List Feature)
    (hof : OrderFree R s0 U) (E : ABBA) (hv : E.Valid fs U) : E.delta R s0 = 0 := by
  have h := hof (R.studyAll s0 E.xs) ⟨E.xs, hv.hxs, rfl⟩ E.a hv.ha E.b hv.hb E.x
  simp only [ABBA.delta, ABBA.pref, pRet, ABBA.memAB_eq, ABBA.memBA_eq, h]
  grind

/-- **Recency gives a positive order effect.** -/
theorem recency_delta_pos (R : Retriever S Item) (s0 : S) (U : List Item) (fs : List Feature)
    (hrec : Recency fs R s0 U) (E : ABBA) (hv : E.Valid fs U) : 0 < E.delta R s0 := by
  have h1 := hrec E.xs hv.hxs E.a hv.ha E.b hv.hb hv.hab hv.hax hv.hbx E.x hv.hsim
  have h2 := hrec E.xs hv.hxs E.b hv.hb E.a hv.ha (Ne.symm hv.hab) hv.hbx hv.hax E.x hv.hsim.symm
  simp only [ABBA.delta, ABBA.pref, ABBA.memAB, ABBA.memBA]
  grind

/-- **Recency and order-freedom are inconsistent** wherever a valid design
exists. -/
theorem orderFree_recency_inconsistent (R : Retriever S Item) (s0 : S) (U : List Item)
    (fs : List Feature) (E : ABBA) (hv : E.Valid fs U) :
    ¬ (OrderFree R s0 U ∧ Recency fs R s0 U) := by
  rintro ⟨hof, hrec⟩
  have h0 := orderFree_delta_zero R s0 U fs hof E hv
  have hp := recency_delta_pos R s0 U fs hrec E hv
  rw [h0] at hp
  exact absurd hp (by decide)

/-! ### A response model: forced choice -/

/-- **Forced choice.** Report B (`true`) if `b` is retrieved, A (`false`) if
`a` is, and otherwise guess B with probability `γ`. -/
def ABBA.report (E : ABBA) (γ : Rat) (r : Option Item) : Dist Bool :=
  if r = some E.a then Dist.pure false
  else if r = some E.b then Dist.pure true
  else [(true, γ), (false, 1 - γ)]

namespace ABBA

/-- The chance of retrieving neither `a` nor `b`. -/
def neither (E : ABBA) (R : Retriever S Item) (s : S) : Rat :=
  prob (R.retrieve s E.x) fun r => !(r == some E.a) && !(r == some E.b)

/-- The reported preference for B over A. -/
def prefRep (E : ABBA) (γ : Rat) (R : Retriever S Item) (s : S) : Rat :=
  prob (Dist.bind (R.retrieve s E.x) (E.report γ)) id -
    prob (Dist.bind (R.retrieve s E.x) (E.report γ)) (fun c => !c)

/-- **The reported order effect.** -/
def deltaRep (E : ABBA) (γ : Rat) (R : Retriever S Item) (s0 : S) : Rat :=
  E.prefRep γ R (E.memAB R s0) - E.prefRep γ R (E.memBA R s0)

end ABBA

/-- What forced choice reports: the chance of B is the chance of retrieving `b`
plus `γ` times the chance of neither, and likewise for A with `1 − γ`. -/
theorem report_probs (E : ABBA) (γ : Rat) (hab : E.a ≠ E.b) (d : Dist (Option Item)) :
    prob (Dist.bind d (E.report γ)) id =
        prob d (· == some E.b) + γ * prob d (fun r => !(r == some E.a) && !(r == some E.b)) ∧
      prob (Dist.bind d (E.report γ)) (fun c => !c) =
        prob d (· == some E.a) +
          (1 - γ) * prob d (fun r => !(r == some E.a) && !(r == some E.b)) := by
  induction d with
  | nil => simp only [Dist.bind, prob]; constructor <;> grind
  | cons rp d ih =>
    obtain ⟨r, p⟩ := rp
    rw [prob_bind_cons, prob_bind_cons, ih.1, ih.2]
    simp only [prob]
    by_cases ha : r = some E.a
    · subst ha
      have hb : (some E.a == some E.b) = false := by simpa using hab
      simp [ABBA.report, prob_pure, hb]
      constructor <;> grind
    · by_cases hb : r = some E.b
      · subst hb
        simp [ABBA.report, prob_pure, ha]
        constructor <;> grind
      · have ha' : (r == some E.a) = false := by simpa using ha
        have hb' : (r == some E.b) = false := by simpa using hb
        simp [ABBA.report, ha, hb, ha', hb', prob]
        constructor <;> grind

/-- **The reported order effect**, in terms of the retrieved one. -/
theorem delta_report (R : Retriever S Item) (s0 : S) (E : ABBA) (γ : Rat) (hab : E.a ≠ E.b) :
    E.deltaRep γ R s0 =
      E.delta R s0 + (2 * γ - 1) * (E.neither R (E.memAB R s0) - E.neither R (E.memBA R s0)) := by
  have h1 := report_probs E γ hab (R.retrieve (E.memAB R s0) E.x)
  have h2 := report_probs E γ hab (R.retrieve (E.memBA R s0) E.x)
  simp only [ABBA.deltaRep, ABBA.prefRep, ABBA.delta, ABBA.pref, ABBA.neither, pRet,
    h1.1, h1.2, h2.1, h2.2]
  grind

/-- **Under order-freedom, the reported order effect is 0**, however biased the
guessing. -/
theorem forcedChoice_orderFree (R : Retriever S Item) (s0 : S) (U : List Item) (fs : List Feature)
    (hof : OrderFree R s0 U) (E : ABBA) (hv : E.Valid fs U) (γ : Rat) : E.deltaRep γ R s0 = 0 := by
  have h := hof (R.studyAll s0 E.xs) ⟨E.xs, hv.hxs, rfl⟩ E.a hv.ha E.b hv.hb E.x
  simp only [ABBA.deltaRep, ABBA.prefRep, ABBA.memAB_eq, ABBA.memBA_eq, h]
  grind

/-- **Under recency, with unbiased guessing, the reported order effect is
positive.** -/
theorem forcedChoice_recency (R : Retriever S Item) (s0 : S) (U : List Item) (fs : List Feature)
    (hrec : Recency fs R s0 U) (E : ABBA) (hv : E.Valid fs U) :
    0 < E.deltaRep (1 / 2) R s0 := by
  rw [delta_report R s0 E _ hv.hab]
  have := recency_delta_pos R s0 U fs hrec E hv
  grind

end Cog.Exp
